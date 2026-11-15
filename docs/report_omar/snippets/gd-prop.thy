typedecl o

judgment
  Trueprop :: ‹o ⇒ prop›  (‹_› 5)

axiomatization
  disj :: ‹o ⇒ o ⇒ o›  (infixr ‹∨› 30) and
  not :: ‹o ⇒ o› (‹¬ _› [40] 40)where
  disjI1: ‹P ⟹ P ∨ Q› and
  disjI2: ‹Q ⟹ P ∨ Q› and
  disjI3: ‹⟦¬P; ¬Q⟧ ⟹ ¬(P ∨ Q)› and
  disjE1: ‹⟦P ∨ Q; P ⟹ R; Q ⟹ R⟧ ⟹ R› and
  disjE2: ‹¬(P ∨ Q) ⟹ ¬P› and
  disjE3: ‹¬(P ∨ Q) ⟹ ¬Q› and
  dNegI: ‹P ⟹ (¬¬P)› and
  dNegE: ‹(¬¬P) ⟹ P› and
  exF: ‹⟦P; ¬P⟧ ⟹ Q›
