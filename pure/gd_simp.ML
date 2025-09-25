structure GD_Simp =
struct
  fun convert_eq_to_meta_eq th: thm = th RS @{thm eq_reflection}
  fun convert_iff_to_meta_eq th: thm = th RS @{thm iff_reflection}

  fun match_object_rule th trm =
    case trm of
      Const (@{const_name GD.eq},  _) $ _ $ _  => [convert_eq_to_meta_eq th]
    | Const (@{const_name GD.iff},  _) $ _ $ _ => [convert_iff_to_meta_eq th]
    | _ => []

  fun th_to_meta_eq_th _ th =
    case Thm.concl_of th of
       Const (@{const_name Pure.eq}, _) $ _ $ _ => [th]
     | Const (@{const_name GD.Trueprop}, _) $ x => match_object_rule th x
     | _ => []
end;

let
  val gd_solver =
    Raw_Simplifier.mk_solver "GD_solver" GDAuto.gd_auto_tac
  fun set_solver ctxt =
    Raw_Simplifier.setSolver (ctxt, gd_solver)
  fun set_ssolver ctxt =
    Raw_Simplifier.setSSolver (ctxt, gd_solver)
  fun configure ctxt =
    ctxt
    |> Simplifier.set_mksimps GD_Simp.th_to_meta_eq_th
    |> set_solver
    |> set_ssolver
in
  Theory.setup (Simplifier.map_theory_simpset configure)
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
