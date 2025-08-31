structure GD_Simp =
struct
  fun reflect_eq th: thm = th RS @{thm eq_reflection};

  fun match_object_rule th trm =
    case trm of
    Const (@{const_name GD.eq},  _) $ _ $ _ =>
        (case try reflect_eq th of SOME th' => [th'] | NONE => [])
    | _ => []

  fun mksimps (_: Proof.context) th =
    (case Thm.concl_of th of
       Const (\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _ => [th]  (* already t \<equiv> u *)
     | Const (\<^const_name>\<open>GD.Trueprop\<close>, _) $ x => match_object_rule th x
     | _ => (case try reflect_eq th of SOME th' => [th'] | NONE => []))
  fun gd_mk_meta_cong (_: Proof.context) rl =
    (case Thm.concl_of rl of
      Const (\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _ => rl
    | _ => raise THM ("gd_mk_meta_cong: conclusion must be meta equality (\<equiv>)", 0, [rl]));
  fun step_tac ctxt : int -> tactic =
    let
      val close = reflexive_thm :: Simplifier.prems_of ctxt
    in
      assume_tac ctxt
      ORELSE' resolve_tac ctxt close
      ORELSE' GDAuto.gd_auto_tac ctxt
    end
  fun solver_tac ctxt i =
    DEPTH_SOLVE (step_tac ctxt i);
  val gd_solver =
    Raw_Simplifier.mk_solver "GD_solver"
      (fn ctxt => fn i =>
        REPEAT_DETERM (CHANGED (step_tac ctxt i)));
end;

let
  fun set_mks ctxt =
    ctxt
    |> Simplifier.set_mksimps GD_Simp.mksimps
    |> Simplifier.set_mkcong GD_Simp.gd_mk_meta_cong
  fun set_subgoaler ctxt =
    ctxt
    |> Simplifier.set_subgoaler GDAuto.gd_auto_tac
    |> Simplifier.set_subgoaler asm_simp_tac
  fun set_solver ctxt =
    Raw_Simplifier.setSolver (set_subgoaler (set_mks ctxt), GD_Simp.gd_solver)
  fun set_ssolver ctxt =
    Raw_Simplifier.setSSolver (set_solver ctxt, GD_Simp.gd_solver)
in
  Theory.setup
    (Simplifier.map_theory_simpset set_ssolver)
end
