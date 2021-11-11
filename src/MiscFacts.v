Require Import Setoid.
Require Import IndefiniteDescription.


Lemma ex_iff_ex:
  forall T (P Q : T -> Prop),
    (forall x, P x <-> Q x) ->
    ex P <-> ex Q.
Proof.
  intuition.
  - destruct H0 as [witness H0].
    exists witness.
    apply H.
    easy.
  - destruct H0 as [witness H0].
    exists witness.
    apply H.
    easy.
Qed.

Lemma all_iff_all:
  forall T (P Q : T -> Prop),
    (forall x, P x <-> Q x) ->
    all P <-> all Q.
Proof.
  unfold all.
  intros.
  setoid_rewrite H.
  reflexivity.
Qed.

Lemma forall_exists_to_exists_forall:
  forall T U (P : T -> U -> Prop),
    (forall (x:T), exists (y:U), P x y) <->
    (exists (f : T -> U), forall (x:T), P x (f x)).
Proof.
  intuition.
  - apply functional_choice.
    easy.
  - destruct H as [f H].
    exists (f x).
    easy.
Qed.
