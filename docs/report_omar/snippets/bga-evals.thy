definition evals :: "tm ⇒ asn ⇒ val ⇒ o" where
  "evals t A r ≡ ∃k. eval_fuel k t A = S r"
