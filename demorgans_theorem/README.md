# Demorgan's Theorem Learning Example

Here I try to prove that two circuits have the same behacviour according to [Demorgan's Laws](https://en.wikipedia.org/wiki/De_Morgan%27s_laws). Here is the first circuit:

The first circuit:
```
val DM1_def = Define `DM1 a b = ~(a \/ b)` ;
```

This is a circuit which performs an `AND2` gate over the inputs `a` and `b` and then inverts the result with a INV gate.

The second circuit:
```
val DM2_def = Define `DM2 a b = ~a /\ ~b` ;
```
This is a circuit which negates the inputs `a` and `b` with an `INV` gate and then feeds the negated inputs to an `OR2` gate.

We can highlight these two definitions in our Emacs buffer and issuing `m-h r` to read these definitions into HOL.

```
> Definition has been stored under "DM1_def"
val DM1_def = ⊢ ∀a b. DM1 a b ⇔ ¬(a ∨ b): thm
> Definition has been stored under "DM2_def"
val DM2_def = ⊢ ∀a b. DM2 a b ⇔ ¬a ∧ ¬b: thm
```

Now let's define our goal to be to prove that `DM1 = DM2` by highlighting the text `` `DM1 = DM2` `` and issuing `m-h g` to push this goal onto the goal-stack:

```
> val it =
   Proof manager status: 1 proof.
   1. Incomplete goalstack:
        Initial goal:

        DM1 = DM2


   : proofs
```

To help establish the equivalence of `DM1` and `DM2` lets using a simplification tactic:

```
simp[FUN_EQ_THM]
```

by issuing `m-h e` which yields a goal which appropriately wires up the arguments of the `DM1` and `DM2` definitions:

```
1 subgoal:
val it =


   ∀x x'. DM1 x x' ⇔ DM2 x x'

   : proof
```

Now we can use the general:

```
metis_tac[DM1_def, DM2_def]
```

tactic (giving it the definitions of `DM1` and `DM2` as arguments) by issuing `m-h e` to complete the proof:

```
metis: r[+0+12]+0+0+0+0+0+0+0+1+0+1+0+1#
r[+0+12]+0+0+0+0+0+1+0+1+0+0+0+0+1#

Goal proved.
⊢ ∀x x'. DM1 x x' ⇔ DM2 x x'
val it =
   Initial goal proved.
   ⊢ DM1 = DM2: proof
```

The script file now contains:

```
open HolKernel boolLib bossLib Parse
val _ = new_theory "demorgan";

val DM1_def = Define `DM1 a b = ~(a \/ b)` ;
val DM2_def = Define `DM2 a b = ~a /\ ~b` ;

Theorem dm `DM1 = DM2`
  (simp[FUN_EQ_THM] >>
   metis_tac[DM1_def, DM2_def]) ;

val _ = export_theory();
```

which can be using by `Holamke`:

```bash
$ ls
README.md		demorganScript.sml
$ Holmake
demorganTheory                       OK
$ ls
README.md		demorganTheory.dat	demorganTheory.sml	demorganTheory.uo
demorganScript.sml	demorganTheory.sig	demorganTheory.ui
```
