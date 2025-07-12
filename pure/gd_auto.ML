structure GDAuto =
struct

  val structural_rules = [
    @{thm eqRefl}, @{thm eqSym}, @{thm nat0}, @{thm natS}, @{thm natP},
    @{thm eqSubst}, @{thm sucInj}, @{thm sucNonZero}, @{thm predSucSym}
  ]

  fun get_rewrites ctxt =
    Named_Theorems.get ctxt @{named_theorems gd_simp}

  fun auto_rewrite_tac rewrites ctxt =
    REPEAT_ALL_NEW (resolve_tac ctxt rewrites)

  fun combine [] i = no_tac
    | combine (tac :: tacs) i = tac i ORELSE combine tacs i

  fun chain_rules_tac ctxt rules d : int -> tactic =
    let
      fun chain 0 = K no_tac
        | chain n =
            let
              val tacs =
                map (fn rule =>
                  resolve_tac ctxt [rule] THEN' chain (n - 1)
                ) rules
            in
              combine tacs
            end
    in
      chain d
    end

  fun auto_step_tac rewrites ctxt i =
    FIRST [
      assume_tac ctxt i,
      chain_rules_tac ctxt structural_rules 3 i,
      auto_rewrite_tac rewrites ctxt i
    ]

  fun gd_auto_tac ctxt i =
    let
      val rewrites = get_rewrites ctxt
    in
      REPEAT_DETERM_N 5 (auto_step_tac rewrites ctxt i ORELSE assume_tac ctxt i)
    end

end

val _ =
  Theory.setup (
    Method.setup @{binding gd_auto}
      (Scan.succeed (fn ctxt => SIMPLE_METHOD' (GDAuto.gd_auto_tac ctxt)))
      "Simple proof automation for GD logic"
  )
