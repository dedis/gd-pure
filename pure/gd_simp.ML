structure GD_Simp =
struct
  fun reflect_eq th: thm = th RS @{thm eq_reflection};
  fun reflect_iff th: thm = th RS @{thm iff_reflection};

  fun match_object_rule th trm =
    case trm of
      Const (@{const_name GD.eq},  _) $ _ $ _ =>
        (case try reflect_eq th of SOME th' => [th'] | NONE => [])
    | Const (@{const_name GD.iff},  _) $ _ $ _ =>
        (case try reflect_iff th of SOME th' => [th'] | NONE => [])
    | _ => []

  fun mksimps (_: Proof.context) th =
    case Thm.concl_of th of
       Const (\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _ => [th]
     | Const (\<^const_name>\<open>GD.Trueprop\<close>, _) $ x => match_object_rule th x
     | _ => []
  fun gd_mk_meta_cong (_: Proof.context) rl =
    (case Thm.concl_of rl of
      Const (\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _ => rl
    | _ => raise THM ("gd_mk_meta_cong: conclusion must be meta equality (\<equiv>)", 0, [rl]));
  fun step_tac ctxt i =
    let
      val close = reflexive_thm :: Simplifier.prems_of ctxt
      val tac =
        assume_tac ctxt
        ORELSE' resolve_tac ctxt close
        ORELSE' GDAuto.gd_auto_tac ctxt
    in
      REPEAT_DETERM (CHANGED (tac i))
    end
  val gd_solver =
    Raw_Simplifier.mk_solver "GD_solver"
      step_tac;
end;

let
  fun set_mks ctxt =
    ctxt
    |> Simplifier.set_mksimps GD_Simp.mksimps
    |> Simplifier.set_mkcong GD_Simp.gd_mk_meta_cong
  fun set_subgoaler ctxt =
    ctxt
    |> Simplifier.set_subgoaler asm_full_simp_tac
  fun set_solver ctxt =
    Raw_Simplifier.setSolver (set_subgoaler (set_mks ctxt), GD_Simp.gd_solver)
  fun set_ssolver ctxt =
    Raw_Simplifier.setSSolver (set_solver ctxt, GD_Simp.gd_solver)
in
  Theory.setup
    (Simplifier.map_theory_simpset set_ssolver)
end;

val parse_nat =
  Scan.optional (Scan.lift Parse.nat >> SOME) NONE

val _ =
  Theory.setup
    (Method.setup @{binding gd_simp}
      (parse_nat >> (fn opt_n => fn ctxt =>
        let
          val ctxt' = (case opt_n of NONE => ctxt | SOME n => Config.put gd_auto_depth_limit n ctxt)
        in
          SIMPLE_METHOD' (fn i => CHANGED (asm_simp_tac ctxt' i))
        end))
      "simp with GD solver; optional fuel")
