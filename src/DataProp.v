(*
 * This module defines `DataProp`, an inductive datatype that can represent
 * first-order propositions.
 *
 * Crucially, this module also defines the tactic `lift_hyp` that converts
 * hypotheses in your goal into DataProp terms.  At that point, regular Gallina
 * functions can be used to manipulate the DataProp.
 *
 * DataProps only quantify over inhabited types, making it possible to convert
 * them to prenex normal form (PNF).
 *)

Require Import Ltac2.Ltac2.

Require Import SNF.Inhabited.
Require Import SNF.Context.
Require Import SNF.TacticUtil.


Inductive DataProp : TypeContext -> Type :=
  | Opaque  : forall {env}, (Valuation env -> Prop) -> DataProp env
  | Literal : forall {env}, bool -> DataProp env
  | And     : forall {env}, DataProp env -> DataProp env -> DataProp env
  | Or      : forall {env}, DataProp env -> DataProp env -> DataProp env
  | Implies : forall {env}, DataProp env -> DataProp env -> DataProp env
  | Not     : forall {env}, DataProp env -> DataProp env
  | Exists  : forall {env} (T : Type) `{IsInhabited T}, DataProp (TypeCons T env) -> DataProp env
  | Forall  : forall {env} (T : Type) `{IsInhabited T}, DataProp (TypeCons T env) -> DataProp env
  .

Fixpoint denote {env : TypeContext} (P : DataProp env) : Valuation env -> Prop :=
  match P with
  | Opaque A => A
  | Literal b => fun _ => if b then True else False
  | And A B => fun v => denote A v /\ denote B v
  | Or A B => fun v => denote A v \/ denote B v
  | Implies A B => fun v => denote A v -> denote B v
  | Not A => fun v => ~(denote A v)
  | Exists T body => fun v => exists (x:T), denote body (ValuationCons x v)
  | Forall T body => fun v => forall (x:T), denote body (ValuationCons x v)
  end.

#[local]
Ltac2 rec to_TypeContext (type_context : constr list) : constr :=
  match type_context with
  | [] => constr:(TypeEmpty)
  | (t :: rest) => let rest' := to_TypeContext rest in constr:(TypeCons $t $rest')
  end.

#[local]
Ltac2 rec to_Valuation (type_context : constr list) (valuation : constr) : constr list :=
  match type_context with
  | [] => []
  | (t :: rest) =>
    let rest' := to_TypeContext rest in
    app1 (constr:(@head $t $rest')) valuation :: to_Valuation rest (app1 (constr:(@tail $t $rest')) valuation)
  end.

(*
 * This ltac2 function converts a regular prop into a DataProp such that
 * (abusing syntax somewhat):
 *
 *   P <-> denote (lift P TypeEmpty) ValuationEmpty
 *
 * In fact, this tactic goes one step further: the denotation of the lifted
 * type is DEFINITIONALLY equal to P.
 *)
Ltac2 rec lift (x : constr) (type_context : constr list) : constr :=
  lazy_match! x with
  | True  => let env := to_TypeContext type_context in constr:(@Literal $env true)
  | False => let env := to_TypeContext type_context in constr:(@Literal $env false)
  | ?p /\ ?q => let p' := lift p type_context in let q' := lift q type_context in constr:(And $p' $q')
  | ?p \/ ?q => let p' := lift p type_context in let q' := lift q type_context in constr:(Or $p' $q')
  | ?p <-> ?q => let p' := lift p type_context in let q' := lift q type_context in constr:(And (Implies $p' $q') (Implies $q' $p'))
  | ?p -> ?q =>
    match! Constr.type p with
    | Prop => let p' := lift p type_context in let q' := lift q type_context in constr:(Implies $p' $q')
    | _ => let q' := lift q (p :: type_context) in constr:(Forall $p $q')
    end
  | ~ ?p => let p' := lift p type_context in constr:(Not $p')
  | ex ?p =>
    match Constr.Unsafe.kind p with
    | Constr.Unsafe.Lambda binder body =>
        let t := Constr.Binder.type binder in
        let body' := lift body (t :: type_context) in
        constr:(Exists $t $body')
    | _ => Message.print (Message.concat (Message.of_string "unable to lift exists ") (Message.of_constr x)); Control.backtrack_tactic_failure "body of `ex` is not a lambda"
    end
  | forall x : ?t, _ =>
    match Constr.Unsafe.kind x with
    | Constr.Unsafe.Prod binder body =>
        let t := Constr.Binder.type binder in
        let body' := lift body (t :: type_context) in
        constr:(Forall $t $body')
    | _ => Message.print (Message.concat (Message.of_string "unable to lift forall ") (Message.of_constr x)); Control.backtrack_tactic_failure "forall lifting failure"
    end
  | _ =>
    let type_context' := to_TypeContext type_context in
    let f := make_lambda_somewhat_safely @venv (constr:(Valuation $type_context')) (fun venv =>
      Constr.Unsafe.substnl (to_Valuation type_context venv) 0 x) in
    match Constr.Unsafe.check constr:(Opaque $f) with
    | Val term => term
    | Err exn => Message.print (Message.of_exn exn); Control.backtrack_tactic_failure "unable to lift term"
    end
  end.

(*
 * In a proof, writing
 *
 *    lift_hyp @H.
 *
 * will change H into (denote P ValuationEmpty) for some DataProp P.
 *
 * This tactic will fail if
 *  - H is not a Prop
 *  - H contains dependent products (e.g. `forall (x : T) (y : f x), ...`)
 *  - H quantifies over types that are not obviously inhabited (Inhabited.v)
 *)
Ltac2 lift_hyp (hypname : ident) : unit :=
  let x := lift (Constr.type (Control.hyp hypname)) [] in
  change (denote $x ValuationEmpty) in $hypname.

Definition as_literal {env} (P : DataProp env) : option bool :=
  match P with
  | Literal b => Some b
  | _ => None
  end.

Fixpoint simplify {env} (P : DataProp env) {struct P} : DataProp env :=
  match P in DataProp E return DataProp E with
  | Opaque _ as p => p
  | Literal _ as p => p
  | And a b =>
    let a' := simplify a in
    let b' := simplify b in
    match as_literal a', as_literal b' with
    | Some true, _ => b'
    | Some false, _ => Literal false
    | _, Some true => a'
    | _, Some false => Literal false
    | _, _ => And a' b'
    end
  | Or a b =>
    let a' := simplify a in
    let b' := simplify b in
    match as_literal a', as_literal b' with
    | Some false, _ => b'
    | Some true, _ => Literal true
    | _, Some false => a'
    | _, Some true => Literal true
    | _, _ => Or a' b'
    end
  | Implies a b =>
    let a' := simplify a in
    let b' := simplify b in
    match as_literal a', as_literal b' with
    | Some false, _ => Literal true
    | Some true, _ => b'
    | _, Some false => Not a'
    | _, Some true => Literal true
    | _, _ => Implies a' b'
    end
  | Not a =>
    let a' := simplify a in
    match as_literal a' with
    | Some true => Literal false
    | Some false => Literal true
    | None => Not a'
    end
  | Exists T body =>
    let body' := simplify body in
    match as_literal body' with
    | Some b => Literal b
    | None => Exists T body'
    end
  | Forall T body =>
    let body' := simplify body in
    match as_literal body' with
    | Some b => Literal b
    | None => Forall T body'
    end
  end.

Lemma as_literal_correct:
  forall env (P : DataProp env) res,
    as_literal P = Some res ->
    forall vals,
      if res then denote P vals else ~ denote P vals.
Proof.
  destruct P; cbn; intros; Control.enter (fun () => try (fun () => discriminate)).
  assert (b = res) by congruence.
  subst b.
  destruct res.
  - constructor.
  - exact id.
Qed.

Lemma simplify_correct:
  forall env (P : DataProp env) vals,
    denote (simplify P) vals <-> denote P vals.
Proof.
  induction P; cbn; intros;
    repeat (match! goal with
    | [ |- context [ as_literal (simplify ?p) ] ] =>
      let h := Fresh.in_goal @H in
      destruct (as_literal (simplify $p)) eqn:$h
    | [ h : as_literal _ = Some _ |- _ ] =>
      apply as_literal_correct with (vals := vals) in $h
    | [ |- context [ if ?b then _ else _ ] ] =>
      destruct $b
    end);
    try (fun () => firstorder).
  - exists X.
    apply as_literal_correct with (vals := ValuationCons X vals) in H0.
    destruct b; firstorder.
  - apply as_literal_correct with (vals := ValuationCons x vals) in H0.
    destruct b; firstorder.
  - apply as_literal_correct with (vals := ValuationCons x vals) in H0.
    destruct b; firstorder.
  - apply as_literal_correct with (vals := ValuationCons X vals) in H0.
    destruct b; firstorder.
Qed.
