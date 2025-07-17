structure Unfold_Def =
struct
  fun unfold_def_method thm_name ctxt =
    SIMPLE_METHOD' (fn i =>
      let
        val defU_thm = Proof_Context.get_thm ctxt "defE"
        val target_thm = Proof_Context.get_thm ctxt thm_name
      in
        resolve_tac ctxt [defU_thm OF [target_thm]] i
      end)
end

val _ =
  Theory.setup
    (Method.setup @{binding unfold_def}
      (Scan.lift Args.name >> Unfold_Def.unfold_def_method)
      "Unfold a definition using defU"
  )
