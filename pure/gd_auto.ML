structure GDAuto =
struct

  fun uncond_rules ctxt = Named_Theorems.get ctxt @{named_theorems auto}
  fun cond_rules   ctxt = Named_Theorems.get ctxt @{named_theorems cond}

  fun solver_tac _    0 = K no_tac
    | solver_tac ctxt k =
      let
        fun transform i th =
          DETERM (
            match_tac ctxt [th] i
            THEN SOLVED' (solver_tac ctxt (k-1)) i
          )
        fun cond_tacs i =
          FIRST (map (transform i)
            (cond_rules ctxt))
        val tac = assume_tac ctxt ORELSE' cond_tacs ORELSE' resolve_tac ctxt (uncond_rules ctxt) ORELSE' resolve_tac ctxt (reflexive_thm :: Simplifier.prems_of ctxt)
        val one_iter = CHANGED o DETERM o tac
        val recurse = solver_tac ctxt (k-1)
        val succeed' = K all_tac
      in
        one_iter THEN_ALL_NEW (recurse ORELSE' succeed')
    end

  fun gd_auto_tac ctxt i =
    let val fuel = 20 in
      CHANGED (REPEAT (CHANGED (solver_tac ctxt fuel i)))
    end

  fun simp_tac ctxt =
    Simplifier.asm_full_simp_tac ctxt

  fun get_rewrites _ _: thm list = []

  fun proof_search _    0 _ = no_tac
    | proof_search ctxt k i =
    let
      val rws = get_rewrites ctxt i
      fun try_solve i th =
        SOLVED' (resolve_tac ctxt [th] THEN' proof_search ctxt (k-1)) i
    in
      (TRY (REPEAT_DETERM (simp_tac ctxt i)))
      THEN FIRST (map (try_solve i) rws)
    end

  fun proof_search_tac ctxt i =
    let val fuel = 30 in
      proof_search ctxt fuel i
    end

end

val _ =
  Theory.setup (
    Method.setup @{binding auto}
      (Scan.succeed (fn ctxt => SIMPLE_METHOD' (GDAuto.gd_auto_tac ctxt)))
      "Simple proof automation for GD logic"
  )
