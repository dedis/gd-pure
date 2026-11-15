  entails :: "o ⇒ o ⇒ o"    (infixr "⊢" 10)
where
  entailsI: "⟦a ⟹ b⟧ ⟹ (a ⊢ b)" and
  entailsE: "⟦a ⊢ b; a⟧ ⟹ b"
