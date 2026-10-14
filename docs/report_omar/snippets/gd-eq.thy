  eq :: ‹num ⇒ num ⇒ o›  (infixl ‹=› 45)
where
  eqSubst: ‹⟦a = b; Q a⟧ ⟹ Q b› and
  eqSym: ‹a = b ⟹ b = a› and
  eq_reflection: ‹x = y ⟹ x ≡ y›
