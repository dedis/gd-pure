theorem BGA_syntactically_consistent:
  assumes "a N" and "b N" and "p1 N" and "p2 N"
  shows "¬ (is_valid_proof p1 ⟨Nil, conc2.mk_eq a b⟩ ∧
             is_valid_proof p2 ⟨Nil, conc2.mk_neq a b⟩)"
  using assms by (rule conc2.syntactically_consistent)
