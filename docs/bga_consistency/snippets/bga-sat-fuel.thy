definition sat_fuel :: "fm ⇒ asn ⇒ o" where
  "sat_fuel f A ≡ ∃x. ∃y. evals (hyp_of (load_F f)) A x ∧ (evals (conc_of (load_F f)) A y ∧ (if tag_F f = F_EQ then x = y else x ≠ y))"
