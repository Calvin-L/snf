(*
 * Definition of our main tactic, `snf`.
 *
 * In Ltac1: use `snf.`
 * In Ltac2: use `snf ().`
 *)

Require Import Ltac2.Ltac2.

Require Export SNF.Inhabited.
Require Import SNF.Context.
Require Import SNF.DataProp.
Require Import SNF.PNFProp.
Require Import SNF.NNFProp.
Require Import SNF.SNFProp.
Require Import SNF.TacticUtil.


Lemma to_snf:
  forall env (P : DataProp env) v,
    denote P v ->
    denote_snf_exists (snf (pnf (nnf P))) v.
Proof.
  intros.
  apply snf_correct.
  apply pnf_correct.
  apply nnf_correct.
  assumption.
Qed.

Ltac2 snf_hyp (hypname : ident) : unit :=
  lift_hyp hypname;
  apply to_snf in $hypname;
  cbv [
    (* basics *)
    head tail nth venv_nth insert without

    (* NNF *)
    nnf nnf' nnf_negb

    (* PNF *)
    pnf pnf_conjoin pnf_conjoin_right pnf_disjoin pnf_disjoin_right
    wrap wrap_pnf swizzle xform_free

    (* SNF *)
    snf
    universalize_forall universalize_body
    push_forall_under_exists defunctionalize_env functionalize_wrt
    SNFForall_xform_free SNFBody_xform_free
    denote_snf_exists denote_snf_forall denote_snf_body
    ] in $hypname;
  break hypname.

Ltac2 snf () :=
  Control.enter (fun () =>
    intros >
    [convert_goal_to_false ()] >
    [break_all ()] >
    [List.iter (fun h => match h with (hname, _, _) => try (fun () => snf_hyp hname) end) (Control.hyps ())]).

Ltac snf := ltac2:(snf ()).
