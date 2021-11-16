Require Import Vector.

Require Import SNF.Inhabited.
Require Import SNF.SNF.


Lemma basic_example:
  forall T `{IsInhabited T} (R : T -> T -> Prop),
  (forall x, exists y, R x y) ->
  forall x, ~ R x x.
Proof.
  snf.

  (*
   * !!!
   *
   * Behold!  The goal is now in skolem normal form.  In particular, it
   * contains the hypothesis:
   *
   *   forall x, R x (x0 x)
   *
   * Since it has rewritten the forall/exists into exists/forall.
   *
   * This goal happens to be unprovable, so we'll just get outta here...
   *)
Abort.

Lemma types_must_be_inhabited:
  forall T (R : T -> T -> Prop),
  (forall x, exists y, R x y) ->
  forall x, ~ R x x.
Proof.
  (* NOTE: the types being quantified over must be inhabited (see IsInhabited
   * typeclass). *)
  intros.
  Fail ltac2:(snf_hyp @H).
Abort.

Lemma types_should_not_be_dependent:
  (forall n (v : Vector.t nat n), True) ->
  False.
Proof.
  (* NOTE: the types being quantified over must not be dependent on other
   * quantified types. *)
  intros.
  Fail ltac2:(snf_hyp @H).
Abort.

Lemma types_can_sometimes_be_dependent:
  (exists n, forall (v : Vector.t nat n), True) ->
  False.
Proof.
  (* NOTE: dependent types can be OK if the things they depend on are skolem
   * constants. *)
  snf.
  match goal with
  | [ _ : nat |- _ ] => idtac
  end.
Abort.
