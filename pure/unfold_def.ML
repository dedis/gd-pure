structure Unfold_Def =
struct
  fun fold_def_method thm_name ctxt =
    SIMPLE_METHOD' (fn i =>
      let
        val defI_thm = Proof_Context.get_thm ctxt "defI"
        val target_thm = Proof_Context.get_thm ctxt thm_name
      in
        CHANGED (resolve_tac ctxt [defI_thm OF [target_thm]] i)
      end)

  fun unfold_def_method thm_name ctxt =
    SIMPLE_METHOD' (fn i =>
      let
        val defE_thm = Proof_Context.get_thm ctxt "defE"
        val target_thm = Proof_Context.get_thm ctxt thm_name
      in
        CHANGED (resolve_tac ctxt [defE_thm OF [target_thm]] i)
      end)
end

val _ =
  Theory.setup
    (Method.setup @{binding unfold_def}
      (Scan.lift Args.name >> Unfold_Def.unfold_def_method)
      "Unfold a definition using defE"
  )

val _ =
  Theory.setup
    (Method.setup @{binding fold_def}
      (Scan.lift Args.name >> Unfold_Def.fold_def_method)
      "Fold a definition using defI"
  )
