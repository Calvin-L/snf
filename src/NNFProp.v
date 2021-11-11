(*
 * Conversion of DataProp terms to negation normal form (NNF).
 *)

Require Import Classical.

Require Import Inhabited.
Require Import Context.
Require Import DataProp.


Inductive NNFProp : TypeContext -> Type :=
  | NNFOpaque  : forall {env}, (Valuation env -> Prop) -> NNFProp env
  | NNFAnd     : forall {env}, NNFProp env -> NNFProp env -> NNFProp env
  | NNFOr      : forall {env}, NNFProp env -> NNFProp env -> NNFProp env
  | NNFExists  : forall {env} (T : Type) `{IsInhabited T}, NNFProp (TypeCons T env) -> NNFProp env
  | NNFForall  : forall {env} (T : Type) `{IsInhabited T}, NNFProp (TypeCons T env) -> NNFProp env
  .

Definition NNFTest : NNFProp TypeEmpty :=
  NNFForall nat (NNFOpaque (fun _ => True)).

Fixpoint denote_nnf {env : TypeContext} (P : NNFProp env) : Valuation env -> Prop :=
  match P with
  | NNFOpaque A => A
  | NNFAnd A B => fun v => denote_nnf A v /\ denote_nnf B v
  | NNFOr A B => fun v => denote_nnf A v \/ denote_nnf B v
  | NNFExists T body => fun v => exists (x:T), denote_nnf body (ValuationCons x v)
  | NNFForall T body => fun v => forall (x:T), denote_nnf body (ValuationCons x v)
  end.

(* so that our tactics can avoid expanding `negb` everywhere *)
Definition nnf_negb (b : bool) :=
  match b with
  | true => false
  | false => true
  end.

Fixpoint nnf' {env} (P : DataProp env) (negate : bool) : NNFProp env :=
  match P with
  | Opaque A => NNFOpaque (if negate then (fun v => ~(A v)) else A)
  | And A B => if negate then NNFOr (nnf' A true) (nnf' B true) else NNFAnd (nnf' A false) (nnf' B false)
  | Or A B => if negate then NNFAnd (nnf' A true) (nnf' B true) else NNFOr (nnf' A false) (nnf' B false)
  | Implies A B => if negate then NNFAnd (nnf' A false) (nnf' B true) else NNFOr (nnf' A true) (nnf' B false)
  | Not A => nnf' A (nnf_negb negate)
  | Exists T body => if negate then NNFForall T (nnf' body true) else NNFExists T (nnf' body false)
  | Forall T body => if negate then NNFExists T (nnf' body true) else NNFForall T (nnf' body false)
  end.

Lemma nnf'_correct:
  forall env (P : DataProp env) negate v,
    denote_nnf (nnf' P negate) v <->
      if negate
      then denote (Not P) v
      else denote P v.
Proof.
  induction P; destruct negate; cbn in *; intros;
    repeat setoid_rewrite IHP;
    repeat setoid_rewrite IHP1;
    repeat setoid_rewrite IHP2;
    try easy.
    - intuition; apply not_and_or; intuition.
    - split.
      + apply and_not_or.
      + apply not_or_and.
    - split.
      + intuition.
      + apply imply_to_and.
    - split.
      + intuition.
      + apply imply_to_or.
    - split.
      + intuition.
      + apply NNPP.
    - split.
      + apply all_not_not_ex.
      + apply not_ex_all_not.
    - split.
      + apply ex_not_not_all.
      + apply not_all_ex_not.
Qed.

Definition nnf {env} (P : DataProp env) : NNFProp env :=
  nnf' P false.

Lemma nnf_correct:
  forall env (P : DataProp env) v,
    denote_nnf (nnf P) v <-> denote P v.
Proof.
  intros.
  apply nnf'_correct.
Qed.

Lemma to_nnf:
  forall env (P : DataProp env) v,
    denote P v ->
    denote_nnf (nnf P) v.
Proof.
  intros.
  apply <- nnf_correct; easy.
Qed.
