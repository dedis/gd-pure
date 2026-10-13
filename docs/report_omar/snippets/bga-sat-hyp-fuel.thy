definition sat_hyp_fuel :: "hyp ⇒ asn ⇒ o" where
  "sat_hyp_fuel G A ≡ ∀f. f ∈ G ⟶ sat_fuel f A"
