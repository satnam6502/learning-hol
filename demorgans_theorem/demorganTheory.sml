structure demorganTheory :> demorganTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading demorganTheory ... "
    else ()
  
  open Type Term Thm
  local open indexedListsTheory patternMatchesTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "demorgan"
        (holpathdb.subst_pathvars "/Users/satnam/learning-hol/demorgans_theorem/demorganTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op DM1_def _ = () val op DM1_def = TDB.find "DM1_def"
  fun op DM2_def _ = () val op DM2_def = TDB.find "DM2_def"
  fun op dm _ = () val op dm = TDB.find "dm"
  
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val demorgan_grammars = merge_grammars ["indexedLists", "patternMatches"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="demorgan"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val demorgan_grammars = 
    Portable.## (addtyUDs,addtmUDs) demorgan_grammars
  val _ = Parse.grammarDB_insert("demorgan",demorgan_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "demorgan"

end
