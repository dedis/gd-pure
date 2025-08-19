structure GD_Subst =
struct
  fun get_thm_eq thm =
    let
      fun get_eq t =
        case t of
          @{term "(Trueprop)"} $ t' => get_eq t'
        | Const (@{const_name GD.eq}, _) $ lhs $ rhs => (SOME lhs, SOME rhs)
        | _ => (NONE, NONE)
      fun strip_asms t =
        case t of
          @{term "(\<Longrightarrow>)"} $ _ $ t' => strip_asms t'
        | _ => t
      val consq = strip_asms (Thm.prop_of thm)
    in
      get_eq consq
    end

  fun matcher ctxt pat =
    let
      val thy = Proof_Context.theory_of ctxt
      fun try_match t =
        if can (Pattern.match thy (pat, t)) (Vartab.empty, Vartab.empty)
        then SOME t else NONE
      fun walk t =
        case try_match t of
          SOME m => SOME m
        | NONE =>
          let
            val (_, args) = Term.strip_comb t
          in
            get_first walk args
          end
    in
      walk
    end

  fun rw ctxt thm t i =
    case get_thm_eq thm of
      (SOME pat, SOME rhs) =>
        let
          val match = matcher ctxt pat t
        in
          case match of
            SOME t' =>
              let
                val l = (Thm.cterm_of ctxt t')
                val r = (Thm.cterm_of ctxt rhs)
                val eqSub = Proof_Context.get_thm ctxt "eqSubst"
                val eqSym = Proof_Context.get_thm ctxt "eqSym"
                val eqSub' =
                  Drule.infer_instantiate' ctxt
                    [SOME r, SOME l]
                    eqSub
              in
                resolve_tac ctxt [eqSub'] i
                THEN resolve_tac ctxt [eqSym] i
                THEN resolve_tac ctxt [thm] i
              end
          | NONE => no_tac
        end
    | _ => no_tac

  fun gd_subst_method thm_name ctxt =
    SIMPLE_METHOD' (
        let
          val thm = Proof_Context.get_thm ctxt thm_name
          val auto_tac = GDAuto.gd_auto_tac ctxt 1
        in
          SUBGOAL (fn (t, _) =>
              (rw ctxt thm t 1) THEN TRY auto_tac
              )
        end)

end

val _ =
Theory.setup
    (Method.setup @{binding subst}
    (Scan.lift Args.name >> GD_Subst.gd_subst_method)
    "Rewrite once using the given theorem."
)
