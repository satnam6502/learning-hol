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