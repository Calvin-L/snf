(*
 * Conversion of NNF terms to prenex normal form (PNF).
 *)

Require Import Classical.

Require Import Inhabited.
Require Import Context.
Require Import NNFProp.
Require Import MiscFacts.


Inductive PNFProp : TypeContext -> Type :=
  | PNFOpaque : forall {env}, (Valuation env -> Prop) -> PNFProp env
  | PNFExists : forall {env} T `{IsInhabited T}, PNFProp (TypeCons T env) -> PNFProp env
  | PNFForall : forall {env} T `{IsInhabited T}, PNFProp (TypeCons T env) -> PNFProp env
  .

Fixpoint denote_pnf {env : TypeContext} (P : PNFProp env) : Valuation env -> Prop :=
  match P with
  | PNFOpaque A => A
  | PNFExists T body => fun v => exists (x:T), denote_pnf body (ValuationCons x v)
  | PNFForall T body => fun v => forall (x:T), denote_pnf body (ValuationCons x v)
  end.

Definition wrap {T env} (x : Valuation env -> Prop) : (Valuation (TypeCons T env) -> Prop) :=
  fun v => x (tail v).

Lemma wrap_correct:
  forall T (x : T) tenv (vals : Valuation tenv) (P : Valuation tenv -> Prop),
    wrap P (ValuationCons x vals) <-> P vals.
Proof.
  unfold wrap; cbn; easy.
Qed.

Fixpoint xform_free {env env'} (p : PNFProp env) (f : Valuation env' -> Valuation env) : PNFProp env' :=
  match p in PNFProp E return (Valuation env' -> Valuation E) -> PNFProp env' with
  | PNFOpaque body => fun f => PNFOpaque (fun v => body (f v))
  | PNFExists T body => fun f => PNFExists T (xform_free body (fun v => ValuationCons (head v) (f (tail v))))
  | PNFForall T body => fun f => PNFForall T (xform_free body (fun v => ValuationCons (head v) (f (tail v))))
  end f.

Lemma xform_free_correct:
  forall env (p : PNFProp env) env' (f : Valuation env' -> Valuation env) vals,
    denote_pnf (xform_free p f) vals <-> denote_pnf p (f vals).
Proof.
  induction p; cbn; intros.
  - easy.
  - apply ex_iff_ex.
    intro x.
    specialize IHp with (f := fun vals' => ValuationCons (head vals') (f (tail vals'))) (vals := ValuationCons x vals).
    exact IHp.
  - apply all_iff_all.
    intro x.
    specialize IHp with (f := fun vals' => ValuationCons (head vals') (f (tail vals'))) (vals := ValuationCons x vals).
    exact IHp.
Qed.

Definition swizzle {T U env} (p : PNFProp (TypeCons T (TypeCons U env))) : PNFProp (TypeCons U (TypeCons T env)) :=
  xform_free p (fun v => ValuationCons (head (tail v)) (ValuationCons (head v) (tail (tail v)))).

Fixpoint wrap_pnf {T env} (p : PNFProp env) : PNFProp (TypeCons T env) :=
  match p with
  | PNFOpaque x => PNFOpaque (wrap x)
  | PNFExists T body => PNFExists T (swizzle (wrap_pnf body))
  | PNFForall T body => PNFForall T (swizzle (wrap_pnf body))
  end.

Lemma wrap_pnf_correct:
  forall T (x : T) tenv (vals : Valuation tenv) (P : PNFProp tenv),
    denote_pnf (wrap_pnf P) (ValuationCons x vals) <-> denote_pnf P vals.
Proof.
  assert (
    forall T U env (x:T) (x0:U) (vals : Valuation env),
    (ValuationCons (head (tail (ValuationCons x0 (ValuationCons x vals))))
      (ValuationCons (head (ValuationCons x0 (ValuationCons x vals)))
        (tail (tail (ValuationCons x0 (ValuationCons x vals)))))) = ValuationCons x (ValuationCons x0 vals)) as X by reflexivity.

  intros.
  generalize dependent x.
  generalize dependent T.
  generalize dependent vals.
  induction P; cbn; intros.
  - easy.
  - apply ex_iff_ex.
    setoid_rewrite xform_free_correct.
    setoid_rewrite X.
    easy.
  - setoid_rewrite xform_free_correct.
    setoid_rewrite X.
    setoid_rewrite IHP.
    easy.
Qed.

Fixpoint pnf_conjoin_right {env} (P : Valuation env -> Prop) (Q : PNFProp env) : PNFProp env :=
  match Q in PNFProp E return (Valuation E -> Prop) -> PNFProp E with
  | PNFOpaque q => fun p => PNFOpaque (fun v => p v /\ q v)
  | PNFExists T body => fun p => PNFExists T (pnf_conjoin_right (wrap p) body)
  | PNFForall T body => fun p => PNFForall T (pnf_conjoin_right (wrap p) body) (* NOTE: only if T inhabited *)
  end P.

Fixpoint pnf_conjoin {env} (P Q : PNFProp env) : PNFProp env :=
  match P in PNFProp E return (PNFProp E -> PNFProp E) with
  | PNFOpaque p => fun q => pnf_conjoin_right p q
  | PNFExists T body => fun q => PNFExists T (pnf_conjoin body (wrap_pnf q))
  | PNFForall T body => fun q => PNFForall T (pnf_conjoin body (wrap_pnf q)) (* NOTE: only if T inhabited *)
  end Q.

Fixpoint pnf_disjoin_right {env} (P : Valuation env -> Prop) (Q : PNFProp env) : PNFProp env :=
  match Q in PNFProp E return (Valuation E -> Prop) -> PNFProp E with
  | PNFOpaque q => fun p => PNFOpaque (fun v => p v \/ q v)
  | PNFExists T body => fun p => PNFExists T (pnf_disjoin_right (wrap p) body)
  | PNFForall T body => fun p => PNFForall T (pnf_disjoin_right (wrap p) body) (* NOTE: only if T inhabited *)
  end P.

Fixpoint pnf_disjoin {env} (P Q : PNFProp env) : PNFProp env :=
  match P in PNFProp E return (PNFProp E -> PNFProp E) with
  | PNFOpaque p => fun q => pnf_disjoin_right p q
  | PNFExists T body => fun q => PNFExists T (pnf_disjoin body (wrap_pnf q))
  | PNFForall T body => fun q => PNFForall T (pnf_disjoin body (wrap_pnf q)) (* NOTE: only if T inhabited *)
  end Q.

Fixpoint pnf {env} (P : NNFProp env) : PNFProp env :=
  match P with
  | NNFOpaque A => PNFOpaque A
  | NNFAnd A B => pnf_conjoin (pnf A) (pnf B)
  | NNFOr A B => pnf_disjoin (pnf A) (pnf B)
  | NNFExists T body => PNFExists T (pnf body)
  | NNFForall T body => PNFForall T (pnf body)
  end.

Inductive tenv_inhabited : TypeContext -> Prop :=
  | empty_inhabited : tenv_inhabited TypeEmpty
  | cons_inhabited : forall T env, T -> tenv_inhabited env -> tenv_inhabited (TypeCons T env)
  .

Lemma pnf_conjoin_right_correct:
  forall env (P : Valuation env -> Prop) (Q : PNFProp env) v,
    denote_pnf (pnf_conjoin_right P Q) v <-> (P v /\ denote_pnf Q v).
Proof.
  intros.
  generalize dependent P.
  generalize dependent v.
  induction Q; cbn; try setoid_rewrite IHQ; intuition.
  - destruct H0.
    easy.
  - destruct H0.
    exists x.
    easy.
  - destruct H2.
    exists x.
    easy.
  - destruct H as [inhab_pf].
    destruct inhab_pf as [witness].
    specialize H0 with witness.
    easy.
  - specialize H0 with x.
    easy.
Qed.

Lemma pnf_conjoin_correct:
  forall env (P Q : PNFProp env) v,
    denote_pnf (pnf_conjoin P Q) v <-> (denote_pnf P v /\ denote_pnf Q v).
Proof.
  induction P; cbn; intuition.
  - solve [eapply pnf_conjoin_right_correct; eauto].
  - solve [eapply pnf_conjoin_right_correct; eauto].
  - solve [eapply pnf_conjoin_right_correct; eauto].
  - destruct H0 as [x H0].
    apply IHP in H0.
    exists x.
    easy.
  - destruct H0 as [x H0].
    apply IHP in H0.
    eapply wrap_pnf_correct.
    intuition eauto.
  - destruct H1 as [x ?].
    exists x.
    apply IHP.
    rewrite wrap_pnf_correct.
    easy.
  - specialize H0 with x.
    apply IHP in H0.
    easy.
  - destruct H as [inhab_pf].
    destruct inhab_pf as [x].
    specialize H0 with x.
    rewrite IHP in H0.
    rewrite wrap_pnf_correct in H0.
    easy.
  - apply IHP.
    rewrite wrap_pnf_correct.
    easy.
Qed.

Lemma pnf_exists_or:
  forall T (witness : T) (P : T -> Prop) (Q : Prop),
    (ex P \/ Q) <->
    (exists x, P x \/ Q).
Proof.
  firstorder.
Qed.

Lemma pnf_forall_or:
  forall T (witness : T) (P : T -> Prop) (Q : Prop),
    (all P \/ Q) <->
    (forall x, P x \/ Q).
Proof.
  intros.
  destruct (classic Q); firstorder.
Qed.

Lemma pnf_disjoin_right_correct:
  forall env (P : Valuation env -> Prop) (Q : PNFProp env) v,
    denote_pnf (pnf_disjoin_right P Q) v <-> (P v \/ denote_pnf Q v).
Proof.
  intros.
  generalize dependent P.
  generalize dependent v.

  induction Q; cbn.
  - easy.
  - destruct H as [H].
    destruct H as [witness].
    setoid_rewrite IHQ.
    setoid_rewrite or_comm.
    setoid_rewrite pnf_exists_or; easy.
  - destruct H as [H].
    destruct H as [witness].
    setoid_rewrite IHQ.
    setoid_rewrite or_comm.
    setoid_rewrite pnf_forall_or; easy.
Qed.

Lemma pnf_disjoin_correct:
  forall env (P Q : PNFProp env) v,
    denote_pnf (pnf_disjoin P Q) v <-> (denote_pnf P v \/ denote_pnf Q v).
Proof.
  induction P; cbn.
  - setoid_rewrite pnf_disjoin_right_correct.
    easy.
  - destruct H as [H].
    destruct H as [witness].
    setoid_rewrite IHP.
    setoid_rewrite wrap_pnf_correct.
    setoid_rewrite pnf_exists_or; easy.
  - destruct H as [H].
    destruct H as [witness].
    setoid_rewrite IHP.
    setoid_rewrite wrap_pnf_correct.
    setoid_rewrite pnf_forall_or; easy.
Qed.

Lemma pnf_correct:
  forall env (P : NNFProp env) v,
    denote_pnf (pnf P) v <-> denote_nnf P v.
Proof.
  induction P; cbn; intros;
    try rewrite pnf_conjoin_correct;
    try rewrite pnf_disjoin_correct;
    try setoid_rewrite IHP;
    try setoid_rewrite IHP1;
    try setoid_rewrite IHP2;
    easy.
Qed.
