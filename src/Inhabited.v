Require Import String.
Require Import ZArith.

Class IsInhabited (T : Type) : Prop := { inhabited_proof: inhabited T }.

#[export] Instance bool_inhabited : IsInhabited bool := { inhabited_proof := inhabits false }.
#[export] Instance nat_inhabited : IsInhabited nat := { inhabited_proof := inhabits 0 }.
#[export] Instance int_inhabited : IsInhabited Z := { inhabited_proof := inhabits 0%Z }.
#[export] Instance list_inhabited T : IsInhabited (list T) := { inhabited_proof := inhabits nil }.
#[export] Instance string_inhabited : IsInhabited string := { inhabited_proof := inhabits EmptyString }.
#[export] Instance func_inhabited (T U : Type) `{U_inhabited : IsInhabited U} : IsInhabited (T -> U) := { inhabited_proof := let (x) := inhabited_proof in inhabits (fun _ => x) }.
