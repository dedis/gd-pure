definition sat :: "num ⇒ num  ⇒ o" where
    "sat f A ≡ if tag_F f = 0 
               then eval (cpx (load_F f)) A = eval (cpy (load_F f)) A
               else eval (cpx (load_F f)) A ≠ eval (cpy (load_F f)) A"

definition sat_hyp :: "hyp ⇒ asn ⇒ o" where
  "sat_hyp G A ≡ ∀f. (mem f G) ⟶ (sat f A)"
