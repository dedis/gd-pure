datatype input = AsThm of thm | AsTrm of term

structure GD_Subst =
struct
  fun strip_asms t =
    case t of
      @{term "(\<Longrightarrow>)"} $ _ $ t' => strip_asms t'
    | _ => t

  fun get_lhs_rhs_of_eq t =
      case t of
        @{term "(Trueprop)"} $ t'                  => get_lhs_rhs_of_eq t'
      | Const (@{const_name GD.eq}, _) $ lhs $ rhs => (SOME lhs, SOME rhs)
      | _                                          => (NONE, NONE)

  fun get_eq (AsTrm t)   = let val (l, r) = get_lhs_rhs_of_eq t in (r, l) end
    | get_eq (AsThm thm) = get_lhs_rhs_of_eq (strip_asms (Thm.prop_of thm))

  fun eq_subst_tac input ctxt =
    case (get_eq input) of
      (SOME pat, SOME rhs) =>
        let
          val l = (Thm.cterm_of ctxt pat)
          val r = (Thm.cterm_of ctxt rhs)
          val eqSub = Proof_Context.get_thm ctxt "eqSubst"
          val eqSub' =
            Drule.infer_instantiate' ctxt
            [SOME r, SOME l]
            eqSub
        in
          resolve_tac ctxt [eqSub']
        end
      | (_,_) => K no_tac

  fun gd_subst_tac (AsThm thm) ctxt =
    let val eqSym = Proof_Context.get_thm ctxt "eqSym" in
      (eq_subst_tac (AsThm thm) ctxt) THEN'
      resolve_tac ctxt [eqSym] THEN'
      resolve_tac ctxt [thm]
    end
  | gd_subst_tac (AsTrm trm) ctxt =
    (eq_subst_tac (AsTrm trm) ctxt) THEN'
    (fn i => TRY (SOLVED' (Simplifier.asm_full_simp_tac ctxt) i))

end

val parse_subst_args : input context_parser =
  (Scan.lift (Args.$$$ "rule" |-- Args.colon) |-- Attrib.thm >> AsThm)
  || (Args.term >> AsTrm)

val _ =
Theory.setup
    (Method.setup @{binding subst}
    (parse_subst_args >>
      (fn inp => fn ctxt => SIMPLE_METHOD' (GD_Subst.gd_subst_tac inp ctxt)))
    "Substitute using the given theorem name or term."
)
