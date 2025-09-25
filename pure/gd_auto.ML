val gd_auto_depth_limit =
  Attrib.setup_config_int @{binding gd_auto_depth_limit} (K 6)

fun TRY' tac i = TRY (tac i)

structure GDAuto =
struct

  fun uncond_rules ctxt = Named_Theorems.get ctxt @{named_theorems auto}
  fun cond_rules   ctxt = Named_Theorems.get ctxt @{named_theorems cond}

  fun solver_tac _    0 = K no_tac
    | solver_tac ctxt k =
      let
        fun apply_and_solve_subgoal i th =
          match_tac ctxt [th] i
          THEN SOLVED' (solver_tac ctxt (k-1)) i
        fun cond_tacs i =
          FIRST (map (apply_and_solve_subgoal i)
            (cond_rules ctxt))
        val tac = assume_tac ctxt ORELSE'
                  resolve_tac ctxt (Simplifier.prems_of ctxt) ORELSE'
                  resolve_tac ctxt (uncond_rules ctxt) ORELSE'
                  cond_tacs
        val one_iter = CHANGED o tac
        val recurse = solver_tac ctxt (k-1)
      in
        REPEAT_ALL_NEW one_iter
    end

  fun gd_auto_tac ctxt i =
    let
      val fuel = Config.get ctxt gd_auto_depth_limit
    in
      CHANGED (REPEAT (CHANGED (solver_tac ctxt fuel i)))
    end
end

val parse_nat =
  Scan.optional (Scan.lift Parse.nat >> SOME) NONE

val _ =
  Theory.setup (
    Method.setup @{binding auto}
      (parse_nat >> (fn opt_n => fn ctxt =>
        let
          val ctxt' = (case opt_n of NONE => ctxt | SOME n => Config.put gd_auto_depth_limit n ctxt)
        in
          SIMPLE_METHOD' (GDAuto.gd_auto_tac ctxt')
        end))
      "Simple proof automation for GD logic"
  )
