(*
 * Some Ltac2 tactics that aren't really specific to this project.
 *)

Require Import Ltac2.Ltac2.
Require Import Classical.


(*
 * `break @H` recursively destructs H until it is not a conjunction or
 * existential.
 *)
Ltac2 rec break (hypname : ident) : unit :=
  let hh := Control.hyp hypname in
  lazy_match! (Constr.type hh) with
  | ex _ =>
    let witname := Fresh.in_goal @x in
    let newname := Fresh.in_goal @H in
    destruct $hh as [$witname $newname] > [break newname]
  | _ /\ _ =>
    let aname := Fresh.in_goal @H in
    let bname := Fresh.fresh (Fresh.Free.union (Fresh.Free.of_goal ()) (Fresh.Free.of_ids [aname])) @H in
    destruct $hh as [$aname $bname] > [break aname > [break bname]]
  | _ => ()
  end.

(*
 * Apply `break` to every hypothesis in the current context.
 *)
Ltac2 break_all () :=
  List.iter
    (fun h => match h with (hname, _, _) => break hname end)
    (Control.hyps ()).

(*
 * Invert the current goal: instead of `|- P`, show `~P |- False`.
 *)
Ltac2 convert_goal_to_false () : unit :=
  lazy_match! goal with
  | [ |- False ] => ()
  | [ |- _ ] => apply NNPP; intro
  end.

(*
 * Try to take an action.  If it fails, do nothing.
 *)
Ltac2 try (f : unit -> unit) : unit :=
  Control.plus f (fun _ => ()).

(*
 * `app f x` returns the term (f x).  Unlike the `constr:(...)` quotation, for
 * reasons I don't fully understand, this implementation is less aggressive
 * about typechecking.
 *)
Ltac2 app1 (f : constr) (x : constr) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list [x])).

(*
 * Useful to construct a lambda term with a bit more safety.  Very similar to
 * `Constr.in_context`, but with a more convenient signature for `body`.
 *)
Ltac2 make_lambda_somewhat_safely (x : ident) (t : constr) (body : constr -> constr) : constr :=
  let x' := Fresh.in_goal x in
  Constr.in_context x' t (fun () =>
    Control.refine (fun () => body (Control.hyp x'))).
