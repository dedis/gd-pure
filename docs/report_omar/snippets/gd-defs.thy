definition neq :: ‹num ⇒ num ⇒ o› (infixl ‹≠› 45)
  where ‹a ≠ b ≡ ¬ (a = b)›
definition bJudg :: ‹o ⇒ o› (‹_ B› [21] 20)
  where ‹(p B) ≡ (p ∨ ¬p)›
definition isNat :: ‹num ⇒ o› (‹_ N› [21] 20)
where "x N ≡ x = x"
definition conj :: ‹o ⇒ o ⇒ o› (infixl ‹∧› 35)
  where ‹p ∧ q ≡ ¬(¬p ∨ ¬q)›
definition impl :: ‹o ⇒ o ⇒ o› (infixr ‹⟶› 25)
  where ‹p ⟶ q ≡ ¬p ∨ q›
definition iff :: ‹o ⇒ o ⇒ o› (infixl ‹⟷› 25)
  where ‹p ⟷ q ≡ (p ⟶ q) ∧ (q ⟶ p)›
