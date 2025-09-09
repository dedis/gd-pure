structure GD_Induct =
struct
  val induct_thm = @{thm ind}
  val strong_induct_thm = @{thm strong_induction}

  fun inst_thm ctxt t th =
    let val ct = Thm.cterm_of ctxt t in
      Drule.infer_instantiate' ctxt [SOME ct] th
    end

  fun apply_tac tac st =
    let
      val res = DETERM tac st
    in
      case Seq.pull res of
          SOME (st', _) => st'
      | NONE => raise THM ("tactic failed", 0, [st])
    end

  fun induct_tac strong t =
    CONTEXT_SUBGOAL (fn (_, i) => fn (ctxt, st) =>
    let
      val th  = if strong then strong_induct_thm else induct_thm
      val th' = inst_thm ctxt t th
      val tac =
        DETERM (match_tac ctxt [th'] i)
      val st' = apply_tac tac st
      val (spec, _) = Rule_Cases.get th
      val cases_prop =
        Thm.prop_of (Rule_Cases.internalize_params st')
      val cases = Rule_Cases.make_common ctxt cases_prop spec
    in
      CONTEXT_CASES cases all_tac (ctxt, st')
    end)

  fun gd_induct_method (strong, t) _ =
    Method.CONTEXT_METHOD (K (induct_tac strong t 1))
end

val parse_induct_args =
  Scan.lift (Scan.optional ((Args.$$$ "strong") >> K true) false)
  -- Args.term

val _ =
  Theory.setup
    (Method.setup @{binding induct}
    (parse_induct_args >> GD_Induct.gd_induct_method)
    "Apply rule ind with where a = <term>"
  )
