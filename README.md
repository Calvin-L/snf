# The `snf` Tactic

This is a Coq tactic that converts your goal into
[skolem normal form (SNF)](https://en.wikipedia.org/wiki/Skolem_normal_form):

```
Coq < Require Import SNF.


Coq < Goal exists x:nat, forall y:nat, x < y \/ y >= x.
1 goal
  
  ============================
  exists x : nat, forall y : nat, x < y \/ y >= x


Unnamed_thm < snf.
1 goal
  
  x : nat -> nat
  H0 : forall x0 : nat, ~ x0 < x x0 /\ ~ x x0 >= x0
  ============================
  False
```

The `snf` tactic assumes [classical logic](https://coq.inria.fr/library/Coq.Logic.Classical_Prop.html)
and [indefinite description](https://coq.inria.fr/library/Coq.Logic.IndefiniteDescription.html).

You'll need Coq 8.14 or higher to use it.


## Getting Started

Install Coq 8.14+, then run `make`.

You can mess around with the tactic in `src/Example.v`.

I don't (yet) have any specific advice on how to use `snf` in another project.


## Why?

Normal forms are incredibly important in automatic theorem proving.  If someone
wanted to, say, write an SMT solver in Gallina that can be used to solve Coq
proof obligations, they will need to implement something like this as a
starting point.

Mostly this project is a demonstration of proof by reflection.  It shows a
relatively clean way to (1) reflect quantified propositions into concrete
datatypes using Ltac2 (see `DataProp.v`) and (2) write Gallina functions to
manipulate those terms, with proofs that validity is preserved (see e.g.
`NNFProp.v`).
