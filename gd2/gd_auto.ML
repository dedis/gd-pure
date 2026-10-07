(*  Title:      gd2/gd_auto.ML

The auto method: depth-limited resolution with the [auto] rules (applied
unconditionally) and the [cond] rules (applied only if all their premises can
be solved), plus assumptions and the simplifier's premises.  Also used as the
simplifier's solver (gd_simp.ML), where it discharges N and B side conditions.
Ported from pure/gd_auto.ML.
*)

val gd_auto_depth_limit =
  Attrib.setup_config_int @{binding gd_auto_depth_limit} (K 6);

structure GDAuto =
struct

fun uncond_rules ctxt = Named_Theorems.get ctxt @{named_theorems auto};
fun cond_rules ctxt = Named_Theorems.get ctxt @{named_theorems cond};

fun solver_tac _ 0 = K no_tac
  | solver_tac ctxt k =
      let
        fun apply_and_solve_subgoal i th =
          match_tac ctxt [th] i THEN SOLVED' (solver_tac ctxt (k - 1)) i;
        fun cond_tacs i = FIRST (map (apply_and_solve_subgoal i) (cond_rules ctxt));
        val tac =
          assume_tac ctxt ORELSE'
          resolve_tac ctxt (Simplifier.prems_of ctxt) ORELSE'
          resolve_tac ctxt (uncond_rules ctxt) ORELSE'
          cond_tacs;
      in REPEAT_ALL_NEW (CHANGED o tac) end;

fun gd_auto_tac ctxt i =
  let val fuel = Config.get ctxt gd_auto_depth_limit
  in CHANGED (REPEAT (CHANGED (solver_tac ctxt fuel i))) end;

end;

val _ =
  Theory.setup
    (Method.setup @{binding auto}
      (Scan.optional (Scan.lift Parse.nat >> SOME) NONE >> (fn opt_n => fn ctxt =>
        let
          val ctxt' =
            (case opt_n of
              NONE => ctxt
            | SOME n => Config.put gd_auto_depth_limit n ctxt);
        in SIMPLE_METHOD' (GDAuto.gd_auto_tac ctxt') end))
      "depth-limited resolution with [auto] and [cond] rules");
