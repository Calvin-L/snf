(*
 * Conversion of PNF terms to skolem normal form (SNF).
 *)

Require Import IndefiniteDescription.

Require Import SNF.Inhabited.
Require Import SNF.Context.
Require Import SNF.PNFProp.
Require Import SNF.MiscFacts.


Inductive SNFBody : TypeContext -> Type :=
  | SNFOpaque : forall {env}, (Valuation env -> Prop) -> SNFBody env
  .

Inductive SNFForall : TypeContext -> Type :=
  | SNFForall_body : forall {env}, SNFBody env -> SNFForall env
  | SNFForall_forall : forall {env} T, SNFForall (TypeCons T env) -> SNFForall env
  .

Inductive SNFExists : TypeContext -> Type :=
  | SNFExists_body : forall {env}, SNFForall env -> SNFExists env
  | SNFExists_exists : forall {env} T, SNFExists (TypeCons T env) -> SNFExists env
  .

Definition denote_snf_body {env} (p : SNFBody env) : Valuation env -> Prop :=
  match p with
  | SNFOpaque body => body
  end.

Fixpoint denote_snf_forall {env} (p : SNFForall env) : Valuation env -> Prop :=
  match p with
  | SNFForall_body body => denote_snf_body body
  | SNFForall_forall T body => fun vals => forall x:T, denote_snf_forall body (ValuationCons x vals)
  end.

Fixpoint denote_snf_exists {env} (p : SNFExists env) : Valuation env -> Prop :=
  match p with
  | SNFExists_body body => denote_snf_forall body
  | SNFExists_exists T body => fun vals => exists x:T, denote_snf_exists body (ValuationCons x vals)
  end.

Definition universalize_body {env} (P : SNFBody env) (var_index : nat) : SNFForall (without env var_index) :=
  match P in SNFBody X return SNFForall (without X var_index) with
  | @SNFOpaque env' body =>
      SNFForall_forall (nth env' var_index) (
        SNFForall_body (
          SNFOpaque (
            fun vals : Valuation (TypeCons (nth env' var_index) (without env' var_index)) =>
              body (insert var_index (head vals) (tail vals)))))
  end.

Fixpoint universalize_forall {env} (P : SNFForall env) (var_index : nat) {struct P} : SNFForall (without env var_index) :=
  match P with
  | SNFForall_body body => universalize_body body var_index
  | SNFForall_forall T body => SNFForall_forall T (universalize_forall body (S var_index))
  end.

Definition SNFBody_xform_free {env env'} (p : SNFBody env) (f : Valuation env' -> Valuation env) : SNFBody env' :=
  match p in SNFBody E return (Valuation env' -> Valuation E) -> SNFBody env' with
  | SNFOpaque body => fun f => SNFOpaque (fun v => body (f v))
  end f.

Fixpoint SNFForall_xform_free {env env'} (p : SNFForall env) (f : Valuation env' -> Valuation env) : SNFForall env' :=
  match p in SNFForall E return (Valuation env' -> Valuation E) -> SNFForall env' with
  | SNFForall_body body => fun f => SNFForall_body (SNFBody_xform_free body f)
  | SNFForall_forall T body => fun f => SNFForall_forall T (SNFForall_xform_free body (fun v => ValuationCons (head v) (f (tail v))))
  end f.

Fixpoint functionalize_wrt (env : TypeContext) (var_index : nat) {struct var_index} : TypeContext :=
  match var_index with
  | O => env
  | S n =>
    match env with
    | TypeEmpty => TypeEmpty
    | TypeCons T rest => TypeCons (nth env (S n) -> T) (functionalize_wrt rest n)
    end
  end.

Fixpoint defunctionalize_env {env} var_index : Valuation (functionalize_wrt env var_index) -> Valuation env :=
  match var_index as N return Valuation (functionalize_wrt env N) -> Valuation env with
  | O => fun vals => vals
  | S n =>
    match env as E return Valuation (functionalize_wrt E (S n)) -> Valuation E with
    | TypeEmpty => fun vals => vals
    | TypeCons T rest =>
        fun vals : Valuation (functionalize_wrt (TypeCons T rest) (S n)) =>
        let x     := vals                           : Valuation (TypeCons (nth rest n -> T) (functionalize_wrt rest n)) in
        let tail' := defunctionalize_env n (tail x) : Valuation rest in
        (ValuationCons ((head x) (venv_nth tail' n)) tail') : Valuation (TypeCons T rest)
    end
  end.

(*
 * Consider formula P with free variable `var_index`.
 *
 * Interpret P as (forall x@var_index, P x).
 *
 * This function produces an equivalent formula in SNF by "pushing" the forall
 * under each exists quantifier in P.
 *)
Fixpoint push_forall_under_exists {env} (P : SNFExists env) (var_index : nat) {struct P} : SNFExists (without (functionalize_wrt env var_index) var_index) :=
  match P in SNFExists X return SNFExists (without (functionalize_wrt X var_index) var_index) with
  | SNFExists_body body => SNFExists_body (universalize_forall (SNFForall_xform_free body (defunctionalize_env var_index)) var_index)
  | @SNFExists_exists env U body =>
    let T := nth env var_index in
    let body' := push_forall_under_exists body (S var_index) : SNFExists (without (functionalize_wrt (TypeCons U env) (S var_index)) (S var_index)) in
    SNFExists_exists (T -> U) body'
  end.

Fixpoint snf {env} (P : PNFProp env) : SNFExists env :=
  match P with
  | PNFOpaque A => SNFExists_body (SNFForall_body (SNFOpaque A))
  | PNFExists T body => SNFExists_exists T (snf body)
  | PNFForall _ body => push_forall_under_exists (snf body) 0
  end.

Lemma SNFBody_xform_free_correct:
  forall env env' (p : SNFBody env) (f : Valuation env' -> Valuation env) vals,
    denote_snf_body (SNFBody_xform_free p f) vals <-> denote_snf_body p (f vals).
Proof.
  destruct p; easy.
Qed.

Lemma SNFForall_xform_free_correct:
  forall env env' (p : SNFForall env) (f : Valuation env' -> Valuation env) vals,
    denote_snf_forall (SNFForall_xform_free p f) vals <-> denote_snf_forall p (f vals).
Proof.
  intros.
  generalize dependent env'.
  induction p; cbn.
  - setoid_rewrite SNFBody_xform_free_correct.
    easy.
  - intros.
    apply all_iff_all.
    intros.
    apply IHp.
Qed.

Lemma universalize_forall_correct:
  forall env (P : SNFForall env) var_index vals,
    denote_snf_forall (universalize_forall P var_index) vals <->
    (forall x, denote_snf_forall P (insert var_index x vals)).
Proof.
  induction P; cbn in *; intros.
  - destruct s; cbn in *; easy.
  - specialize IHP with (var_index := S var_index).
    setoid_rewrite IHP.
    cbn in *.
    easy.
Qed.

Fixpoint lift_witness_left {env var_index} {struct env} : nth (functionalize_wrt env var_index) var_index -> nth env var_index :=
  match env as E return nth (functionalize_wrt E var_index) var_index -> nth E var_index with
  | TypeEmpty => fun _ => tt
  | TypeCons T rest =>
    match var_index as N return nth (functionalize_wrt (TypeCons T rest) N) N -> nth (TypeCons T rest) N with
    | O => fun x => x
    | S n => @lift_witness_left rest n
    end
  end.

Lemma nth_is_lifted_left:
  forall env var_index (vals : Valuation (without (functionalize_wrt env var_index) var_index)) x,
    lift_witness_left x = venv_nth (defunctionalize_env var_index (insert var_index x vals)) var_index.
Proof.
  induction env; destruct var_index; cbn in *; easy.
Qed.

Fixpoint lift_witness_right {env var_index} {struct env} : nth env var_index -> nth (functionalize_wrt env var_index) var_index :=
  match env as E return nth E var_index -> nth (functionalize_wrt E var_index) var_index with
  | TypeEmpty =>
    match var_index with
    | O => fun _ => tt
    | S _ => fun _ => tt
    end
  | TypeCons T rest =>
    match var_index as N return nth (TypeCons T rest) N -> nth (functionalize_wrt (TypeCons T rest) N) N with
    | O => fun x => x
    | S n => @lift_witness_right rest n
    end
  end.

Lemma nth_is_lifted_right:
  forall env var_index (vals : Valuation (without (functionalize_wrt env var_index) var_index)) x,
    lift_witness_right (venv_nth (defunctionalize_env var_index (insert var_index x vals)) var_index) = x.
Proof.
  induction env; destruct var_index; cbn in *; try easy; intuition.
  - destruct x; easy.
  - destruct x; easy.
Qed.

Lemma push_forall_under_exists_correct:
  forall env (P : SNFExists env) var_index (vals : Valuation (without (functionalize_wrt env var_index) var_index)),
    denote_snf_exists (push_forall_under_exists P var_index) vals <->
    (forall x, denote_snf_exists P (defunctionalize_env var_index (insert var_index x vals))).
Proof.
  induction P; cbn in *; intros.
  - rewrite universalize_forall_correct.
    setoid_rewrite SNFForall_xform_free_correct.
    easy.
  - specialize IHP with (var_index := S var_index).
    cbn in IHP.
    setoid_rewrite IHP.
    clear IHP.
    setoid_rewrite forall_exists_to_exists_forall.

    (*
     * Ah!  A problem.  We have the following two types floating around in the
     * conclusion:
     *   - nth env var_index
     *   - nth (functionalize_wrt env var_index) var_index
     *
     * As it happens, those types are equal.  However, proving a normal "="
     * relation between them isn't really useful; there are limits to rewriting
     * term types.
     *
     * To show this goal, we will have to use some helper types and lemmas
     * for converting between these types.
     *)
    {

      intuition.
      - destruct H as [f H].
        exists (fun x => f (lift_witness_left x)).
        intro x.
        specialize H with x.
        cbn in *.
        erewrite nth_is_lifted_left.
        eassumption.
      - destruct H as [f H].
        exists (fun x => f (lift_witness_right x)).
        intro x.
        specialize H with x.
        cbn in *.
        rewrite nth_is_lifted_right.
        assumption.

    }
Qed.

Lemma snf_correct:
  forall env (P : PNFProp env) v,
    denote_snf_exists (snf P) v <->
    denote_pnf P v.
Proof.
  induction P; cbn; intros.
  - easy.
  - apply ex_iff_ex; easy.
  - setoid_rewrite <- IHP.
    setoid_rewrite (push_forall_under_exists_correct _ (snf P) 0).
    easy.
Qed.
