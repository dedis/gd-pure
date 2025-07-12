structure GDAuto =
struct

  (* Get GD-style rewrite rules tagged with [gd_simp] *)
  fun get_rewrites ctxt =
    Named_Theorems.get ctxt @{named_theorems gd_simp}

  (* Apply a list of rewrite rules repeatedly to all subgoals *)
  fun auto_rewrite_tac ctxt =
    let
      val rewrites = get_rewrites ctxt
    in
      REPEAT_ALL_NEW (resolve_tac ctxt rewrites)
    end

  (* Also apply structural rules like eqRefl, eqSym, etc. *)
  fun auto_step_tac ctxt =
    FIRST' [
      assume_tac ctxt,
      resolve_tac ctxt [@{thm eqRefl}, @{thm eqSym}, @{thm nat0}, @{thm natS}, @{thm natP}, @{thm eqSubst},
      @{thm sucInj}, @{thm natS}, @{thm natP}, @{thm sucNonZero}, @{thm predSucSym}],
      auto_rewrite_tac ctxt
    ]

  (* Try everything we know in a reasonable loop *)
  fun gd_auto_tac ctxt =
    REPEAT_ALL_NEW (
      auto_step_tac ctxt
      ORELSE' assume_tac ctxt
    )

end

val _ =
  Theory.setup (
    Method.setup @{binding gd_auto}
      (Scan.succeed (SIMPLE_METHOD' o GDAuto.gd_auto_tac))
      "Simple proof automation for GD logic"
  )
