sublocale consistent mk_eq mk_neq dfns is_valid_proof evals sat_fuel sat_hyp_fuel
proof (unfold_locales)
  show "⋀a b. a N ⟹ b N ⟹ mk_eq a b N"
    by (rule mk_eq_N')
  show "⋀a b. a N ⟹ b N ⟹ mk_neq a b N"
    by (rule mk_neq_N')
  show "⋀p J. p N ⟹ J N ⟹ is_valid_proof p J B"
    by (rule proof_is_bool)
  show "⋀A. sat_hyp_fuel Nil A"
    by (rule sat_hyp_fuel_nil)
  show "⋀t A r q. t N ⟹ A N ⟹ evals t A r ⟹ evals t A q ⟹ r = q"
    by (rule evals_functional)
  show "⋀a b A R. a N ⟹ b N ⟹ sat_fuel (mk_eq a b) A ⟹
        (⋀q. q N ⟹ evals a A q ⟹ evals b A q ⟹ R) ⟹ R"
    by (rule sat_fuel_mk_eqE)
  show "⋀a b A R. a N ⟹ b N ⟹ sat_fuel (mk_neq a b) A ⟹
        (⋀x y. x N ⟹ y N ⟹ evals a A x ⟹ evals b A y ⟹ x ≠ y ⟹ R) ⟹ R"
    by (rule sat_fuel_mk_neqE)
  show "⋀p J A. is_valid_proof p J ⟹ sat_hyp_fuel (hyp_of J) A ⟹ A N ⟹ sat_fuel (conc_of J) A"
    by (rule soundness_bridge_fuel)
