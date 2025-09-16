structure GD_Induct =
struct
  val induct_thm = @{thm ind}
  val strong_induct_thm = @{thm strong_induction}

  fun try_inst_thm ctxt t th =
    let val ct = Thm.cterm_of ctxt t in
      try (fn th => Drule.infer_instantiate' ctxt [SOME ct] th) th
    end

  fun closes_first_prem ctxt i th st =
    let
      val tac =
      DETERM (
        resolve_tac ctxt [th] i
        THEN ((SOLVED' (assume_tac ctxt)) i)
      )
    in
      Option.isSome (Seq.pull (tac st))
    end

  fun select_induct_thm ctxt t i st =
    let
      val induct_thms = Named_Theorems.get ctxt @{named_theorems induct}
      fun is_instantiable th =
        case (try_inst_thm ctxt t th) of
          NONE     => NONE
        | SOME th' => if (closes_first_prem ctxt i th' st) then SOME th else NONE
    in
      case (get_first is_instantiable induct_thms) of
        SOME th => th
      | NONE    => induct_thm
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
      val th  = if strong then strong_induct_thm else (select_induct_thm ctxt t i st)
      val th' = try_inst_thm ctxt t th
      val tac =
        case th' of
          SOME th'' => DETERM (match_tac ctxt [th''] i)
        | NONE      => no_tac
      val st' = apply_tac tac st
      val (spec, _) = Rule_Cases.get th
      val cases_prop = Thm.prop_of (Rule_Cases.internalize_params st')
      val cases = Rule_Cases.make_common ctxt cases_prop spec
      val post_tac = TRY (SOLVED' (assume_tac ctxt) i)
    in
      CONTEXT_CASES cases post_tac (ctxt, st')
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
