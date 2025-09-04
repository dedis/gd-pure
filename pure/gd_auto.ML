structure GDAuto =
struct

  fun uncond_rules ctxt = Named_Theorems.get ctxt @{named_theorems auto}
  fun cond_rules ctxt = Named_Theorems.get ctxt @{named_theorems cond}

  fun repeat_all_bounded 0 _   = K no_tac
    | repeat_all_bounded k tac =
      let
        val one_iter = CHANGED o DETERM o tac
        val rec_call = repeat_all_bounded (k-1) tac
      in
        one_iter THEN_ALL_NEW (rec_call ORELSE' K all_tac)
      end

  fun uncond_rewrite_tac_bounded ctxt fuel =
    let
      val tac = assume_tac ctxt ORELSE' resolve_tac ctxt (uncond_rules ctxt)
    in
      repeat_all_bounded fuel tac
    end

  fun solver_tac ctxt fuel i =
    if fuel = 0 then no_tac
    else
      let
        fun transform th =
          DETERM (
            match_tac ctxt [th] i
            THEN SOLVED' (solver_tac ctxt (fuel-1)) i
          )
        val cond_tacs =
          FIRST (map transform
            (cond_rules ctxt))
      in
        FIRST [assume_tac ctxt i, uncond_rewrite_tac_bounded ctxt (fuel-1) i, cond_tacs]
        THEN (TRY (solver_tac ctxt (fuel-1) i))
    end

  fun gd_auto_tac ctxt i =
    let val fuel = 24 in
      CHANGED (solver_tac ctxt fuel i)
    end
end

val _ =
  Theory.setup (
    Method.setup @{binding auto}
      (Scan.succeed (fn ctxt => SIMPLE_METHOD' (GDAuto.gd_auto_tac ctxt)))
      "Simple proof automation for GD logic"
  )
