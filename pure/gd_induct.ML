structure GD_Induct =
struct
  val induct_thm = @{thm ind}
  val strong_induct_thm = @{thm strong_induction}

  fun inst_thm ctxt t th =
    let val ct = Thm.cterm_of ctxt t in
      Drule.infer_instantiate' ctxt [SOME ct] th
    end

  fun TRY_SOLVE_FIRST' (tac : int -> tactic): tactic =
    COND (fn st => 1 <= Thm.nprems_of st)
      (TRY (DETERM (SOLVED' tac 1)))
      all_tac

  fun remove_quant_entail ctxt i =
    REPEAT (FIRST [resolve_tac ctxt [@{thm forallI}] i,
                    resolve_tac ctxt [@{thm entailsI}] i])

  fun induct_tac strong ctxt t i =
    let
      val th  = if strong then strong_induct_thm else induct_thm
      val th' = inst_thm ctxt t th
    in
      DETERM (match_tac ctxt [th'] i)
      THEN remove_quant_entail ctxt 3
      THEN TRY_SOLVE_FIRST' (assume_tac ctxt)
    end

  fun gd_induct_method (strong, t) ctxt =
    SIMPLE_METHOD' (induct_tac strong ctxt t)
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
