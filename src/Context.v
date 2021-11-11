(*
 * We are going to use de Bruijn indices for free variables.
 *
 * `TypeContext` is a list of types, where the ith type is the type of the
 * variable with index i.
 *
 * `Valuation T` (where T is a TypeContext) is a list of values such that the
 * ith value has the ith type in T.
 *
 * These definitions are loosely inspiried by the encoding in CPDT:
 * http://adam.chlipala.net/cpdt/html/Cpdt.ProgLang.html
 *)

Inductive TypeContext : Type :=
  | TypeEmpty
  | TypeCons : Type -> TypeContext -> TypeContext
  .

Inductive Valuation : TypeContext -> Type :=
  | ValuationEmpty : Valuation TypeEmpty
  | ValuationCons : forall {T rest}, T -> Valuation rest -> Valuation (TypeCons T rest)
  .

Definition head {T rest} (v : Valuation (TypeCons T rest)) : T :=
  match v in Valuation X return (match X with TypeCons T _ => T | TypeEmpty => unit end) with
  | ValuationCons x _ => x
  | _ => tt
  end.

Definition tail {T rest} (v : Valuation (TypeCons T rest)) : Valuation rest :=
  match v in Valuation X return (match X with TypeCons _ rest => Valuation rest | TypeEmpty => unit end) with
  | ValuationCons _ x => x
  | _ => tt
  end.

Fixpoint without (env : TypeContext) (var_index : nat) : TypeContext :=
  match env with
  | TypeEmpty => TypeEmpty
  | TypeCons T rest =>
    match var_index with
    | O => rest
    | S n => TypeCons T (without rest n)
    end
  end.

Fixpoint nth (env : TypeContext) (n : nat) : Type :=
  match env with
  | TypeEmpty => unit
  | TypeCons T rest =>
    match n with
    | O => T
    | S m => nth rest m
    end
  end.

Fixpoint insert {env} (var_index : nat) (x : nth env var_index) (vals : Valuation (without env var_index)) : Valuation env :=
  match env as E return nth E var_index -> Valuation (without E var_index) -> Valuation E with
  | TypeEmpty => fun x vals => ValuationEmpty
  | TypeCons T rest =>
    match var_index as N return nth (TypeCons T rest) N -> Valuation (without (TypeCons T rest) N) -> Valuation (TypeCons T rest) with
    | O => fun x vals => ValuationCons x vals
    | S n => fun x vals =>
      (* vals : Valuation (TypeCons T (without env n)) *)
      ValuationCons (head vals) (insert n x (tail vals))
    end
  end x vals.

Fixpoint tenv_replace (env : TypeContext) (var_index : nat) (T : Type) : TypeContext :=
  match env with
  | TypeEmpty => TypeEmpty
  | TypeCons U rest =>
    match var_index with
    | O => TypeCons T rest
    | S n => TypeCons U (tenv_replace rest n T)
    end
  end.

Fixpoint venv_replace {env T} (var_index : nat) (x : T) (v : Valuation env) : Valuation (tenv_replace env var_index T) :=
  match env as E return Valuation E -> Valuation (tenv_replace E var_index T) with
  | TypeEmpty => fun _ => ValuationEmpty
  | TypeCons U rest =>
    match var_index with
    | O => fun v => ValuationCons x (tail v)
    | S n => fun v => ValuationCons (head v) (venv_replace n x (tail v))
    end
  end v.

Fixpoint venv_nth {env} (v : Valuation env) (var_index : nat) : nth env var_index :=
  match v with
  | ValuationEmpty => tt
  | ValuationCons x rest =>
    match var_index with
    | O => x
    | S n => venv_nth rest n
    end
  end.

Fixpoint tenv_len (env : TypeContext) : nat :=
  match env with
  | TypeEmpty => O
  | TypeCons _ rest => S (tenv_len rest)
  end.
