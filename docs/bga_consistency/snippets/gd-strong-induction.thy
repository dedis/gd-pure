lemma strong_induction [consumes 1, case_names HQ Base Step]:
  shows "a N ⟹ Q 0 ⟹ (⋀x. x N ⟹ (⋀y. y N ⟹ y≤x = 1 ⟹ Q y) ⟹ (Q S(x))) ⟹ Q a"
