structure GDAuto =
struct

  fun uncond_rules ctxt = Named_Theorems.get ctxt @{named_theorems auto}
  fun cond_rules ctxt = Named_Theorems.get ctxt @{named_theorems cond}

  fun auto_rewrite_tac ctxt =
    REPEAT_ALL_NEW (assume_tac ctxt ORELSE' resolve_tac ctxt (uncond_rules ctxt))

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
        CHANGED (FIRST [assume_tac ctxt i, auto_rewrite_tac ctxt i, cond_tacs])
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
