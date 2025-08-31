structure GDAuto =
struct

  val structural_rules = [
    @{thm disjI3}, @{thm nat0}, @{thm natS}, @{thm natP},
    @{thm eqSubst},
    @{thm nat0}, @{thm natS}, @{thm natP}, @{thm sucNonZero}, @{thm sucInj},
    @{thm predSucInv}, @{thm pred0}, @{thm neq_def}, @{thm eqBool},
    @{thm sucCong}, @{thm disjI3}, @{thm dNegI}
  ]

  fun get_rewrites ctxt =
    Named_Theorems.get ctxt @{named_theorems gd_auto}

  fun auto_rewrite_tac rewrites ctxt =
    REPEAT_ALL_NEW (assume_tac ctxt ORELSE' resolve_tac ctxt rewrites)

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

  fun base_tac ctxt i =
    let
      val rewrites = get_rewrites ctxt
    in
      CHANGED (REPEAT_DETERM_N 5 (assume_tac ctxt i ORELSE auto_step_tac rewrites ctxt i))
    end

  fun sidecond_tac ctxt : int -> tactic =
    SOLVED' (base_tac ctxt)

  fun try_rule ctxt i (th: thm) =
    DETERM (resolve_tac ctxt [th] i THEN sidecond_tac ctxt i)

  fun cond_tac ctxt i =
    let
      val rules = Named_Theorems.get ctxt @{named_theorems gd_cond}
      val tacs  = map (try_rule ctxt i) rules
    in
      CHANGED (FIRST tacs)
    end

  fun gd_auto_tac ctxt i =
    FIRST [
      base_tac ctxt i,
      cond_tac ctxt i
    ]
end

val _ =
  Theory.setup (
    Method.setup @{binding gd_auto}
      (Scan.succeed (fn ctxt => SIMPLE_METHOD' (GDAuto.gd_auto_tac ctxt)))
      "Simple proof automation for GD logic"
  )
