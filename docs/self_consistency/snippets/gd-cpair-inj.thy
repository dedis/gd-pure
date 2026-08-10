lemma cpair_inj:
  assumes eq: "⟨a, b⟩ = ⟨c, d⟩"
  shows "a N ⟹ b N ⟹ c N ⟹ d N ⟹ a = c ∧ b = d"
