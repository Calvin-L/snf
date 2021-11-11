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

Require Import Inhabited.
Require Import Context.
Require Import TacticUtil.


Inductive DataProp : TypeContext -> Type :=
  | Opaque  : forall {env}, (Valuation env -> Prop) -> DataProp env
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
  | ?p /\ ?q => let p' := lift p type_context in let q' := lift q type_context in constr:(And $p' $q')
  | ?p \/ ?q => let p' := lift p type_context in let q' := lift q type_context in constr:(Or $p' $q')
  | ?p <-> ?q => let p' := lift p type_context in let q' := lift q type_context in constr:(And (Implies $p' $q') (Implies $q' $p'))
  | ?p -> ?q =>
    match! Constr.type p with
    | Prop => let p' := lift p type_context in let q' := lift q type_context in constr:(Implies $p' $q')
    | _ => let q' := lift q type_context in constr:(Forall $p $q')
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
