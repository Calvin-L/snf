(*
 * Definition of our main tactic, `snf`.
 *
 * In Ltac1: use `snf.`
 * In Ltac2: use `snf ().`
 *)

Require Import Ltac2.Ltac2.

Require Export Inhabited.
Require Import Context.
Require Import DataProp.
Require Import PNFProp.
Require Import NNFProp.
Require Import SNFProp.
Require Import TacticUtil.


Definition snf {env} (P : DataProp env) : SNFExists env :=
  PNFProp_to_SNFExists (pnf (nnf P)).

Lemma snf_correct:
  forall env (P : DataProp env) v,
    denote P v <->
    denote_snf_exists (snf P) v.
Proof.
  intros.
  unfold snf.
  rewrite <- PNFProp_to_SNFExists_correct.
  rewrite pnf_correct.
  rewrite nnf_correct.
  reflexivity.
Qed.

Lemma to_snf:
  forall env (P : DataProp env) v,
    denote P v ->
    denote_snf_exists (snf P) v.
Proof.
  intros.
  rewrite <- snf_correct.
  assumption.
Qed.

Ltac2 snf_hyp (hypname : ident) : unit :=
  lift_hyp hypname;
  apply to_snf in $hypname;
  cbv [
    snf
    universalize universalize_exists universalize_forall universalize_body
    push_forall_under_exists defunctionalize_env functionalize_wrt id
    generalize_over SNFExists_xform_free SNFForall_xform_free SNFBody_xform_free
    PNFProp_to_SNFExists
    without
    nnf nnf' nnf_negb head tail nth venv_nth insert
    pnf pnf_conjoin pnf_conjoin_right pnf_disjoin pnf_disjoin_right
    denote_snf_exists denote_snf_forall denote_snf_body
    wrap wrap_pnf swizzle xform_free
    ] in $hypname;
  break hypname.

Ltac2 snf () :=
  Control.enter (fun () =>
    intros >
    [convert_goal_to_false ()] >
    [break_all ()] >
    [List.iter (fun h => match h with (hname, _, _) => try (fun () => snf_hyp hname) end) (Control.hyps ())]).

Ltac snf := ltac2:(snf ()).
