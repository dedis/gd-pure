locale suff_semantics = suff_syntax +
  (*Semantics. sat checks whether the encoding of a formula is satisfied by an assignment. eval reduces a term under an assignment*)

  fixes evals :: "tm ⇒ asn ⇒ val ⇒ o"
  fixes sat_fm :: "fm ⇒ asn ⇒ o"
  fixes sat_hyp :: "hyp ⇒ asn ⇒ o"

  assumes sat_hyp_nil: "sat_hyp Nil A"

  (* Evaluation is deterministic *)
  assumes evals_det: "⟦t N; A N; evals t A r; evals t A q⟧ ⟹ r = q"

  (* What equations mean in the model: the two sides evaluate to a common value
     (resp. to distinct values). *)
  assumes sat_eqE:
    "⟦a N; b N; sat_fm (mk_eq a b) A;
      ⋀q. ⟦q N; evals a A q; evals b A q⟧ ⟹ R⟧ ⟹ R"
  assumes sat_neqE:
    "⟦a N; b N; sat_fm (mk_neq a b) A;
      ⋀x y. ⟦x N; y N; evals a A x; evals b A y; x ≠ y⟧ ⟹ R⟧ ⟹ R"
