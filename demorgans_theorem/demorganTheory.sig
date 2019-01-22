signature demorganTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val DM1_def : thm
    val DM2_def : thm
  
  (*  Theorems  *)
    val dm : thm
  
  val demorgan_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [indexedLists] Parent theory of "demorgan"
   
   [patternMatches] Parent theory of "demorgan"
   
   [DM1_def]  Definition
      
      ⊢ ∀a b. DM1 a b ⇔ ¬(a ∨ b)
   
   [DM2_def]  Definition
      
      ⊢ ∀a b. DM2 a b ⇔ ¬a ∧ ¬b
   
   [dm]  Theorem
      
      ⊢ DM1 = DM2
   
   
*)
end
