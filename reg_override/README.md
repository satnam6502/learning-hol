# Register with Override Learning Example

This learning example builds a register with an overridable output
(when `clr` is asserted the output becomes 0) out of a multiplexor
and a register and proves it have the desired behaviour.

First, let's define a 2-to-1 multiplexor:

```
val MUX2to1_def = Define `MUX2to1 sel a b t = if sel t then a t else b t` ;
```

to which HOL responds:

```
Definition has been stored under "MUX2to1_def"
val MUX2to1_def =
   ⊢ ∀sel a b t. MUX2to1 sel a b t = if sel t then a t else b t: thm
```

Let's also define a flip-flop:

```
> # # # # Definition has been stored under "REG_def"
val REG_def = ⊢ ∀input t. REG input t ⇔ if t = 0 then F else input (t − 1):
   thm
```

Using these two components we can build a circuit which has a register with an overridable output:

```
val REGCLR_def = Define `REGCLR input clr t
  = let regOut = REG input ;
        output = MUX2to1 clr (K F) regOut ;
    in output t` ;
```

reading into HOL:

```
> > # # # Definition has been stored under "REGCLR_def"
val REGCLR_def =
   ⊢ ∀input clr t.
         REGCLR input clr t ⇔
         (let
            regOut = REG input ;
            output = MUX2to1 clr (K F) regOut
          in
            output t): thm
```

Let's define the goal we want to prove:

```
`REGCLR input clr t
 = if clr t \/ (t = 0) then
     F
   else
     input (t - 1)`
```

which says the output of the circuit is `F` when either the `clr` signal is asserted or if it is the first cycle after reset, otherwise the output is the value of the previous input. Our goal is now set up in HOL:

```
> # # # # val it =
   Proof manager status: 1 proof.
   1. Incomplete goalstack:
        Initial goal:

        REGCLR input clr t ⇔ if clr t ∨ (t = 0) then F else input (t − 1)


   : proofs
> val it = (): unit
```

Applying the tactic `rw[REGCLR_def, MUX2to1_def, REG_def]` yields:

```
1 subgoal:
val it =


   ¬clr t ∧ t ≠ 0 ∧ input (t − 1) ⇔ (¬clr t ∧ t ≠ 0) ∧ input (t − 1)

   : proof
```

to which we can apply the tactic `metis_tac[]` to complete the proof:

```
metis:
Goal proved.
⊢ ¬clr t ∧ t ≠ 0 ∧ input (t − 1) ⇔ (¬clr t ∧ t ≠ 0) ∧ input (t − 1)
val it =
   Initial goal proved.
   ⊢ REGCLR input clr t ⇔ if clr t ∨ (t = 0) then F else input (t − 1): proof
```

The complete proof script is:

```
open HolKernel boolLib bossLib Parse
val _ = new_theory "regOverride";

val MUX2to1_def = Define `MUX2to1 sel a b t = if sel t then a t else b t` ;
val REG_def = Define `REG input t
  = if t = 0 then
      F
    else
      input (t - 1)` ;
val REGCLR_def = Define `REGCLR input clr t
  = let regOut = REG input ;
        output = MUX2to1 clr (K F) regOut ;
    in output t` ;

Theorem regclr `REGCLR input clr t
  = if clr t \/ (t = 0) then
      F
    else
      input (t - 1)`
    (rw[REGCLR_def, MUX2to1_def, REG_def] >>
     metis_tac[]) ;

val _ = export_theory();
```
