open HolKernel boolLib bossLib Parse
val _ = new_theory "demorgan";

val DM1_def = Define `DM1 a b = ~(a \/ b)` ;
val DM2_def = Define `DM2 a b = ~a /\ ~b` ;

Theorem dm `DM1 = DM2`
  (simp[FUN_EQ_THM] >>
   metis_tac[DM1_def, DM2_def]) ;

val _ = export_theory();