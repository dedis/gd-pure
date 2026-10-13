  forall :: "(num ⇒ o) ⇒ o"  (binder "∀" [8] 9) and
  exists :: "(num ⇒ o) ⇒ o"  (binder "∃" [8] 9)
where
  forallI: "⟦⋀x. x N ⟹ Q x⟧ ⟹ ∀x. Q x" and
  forallE: "⟦∀c'. Q c'; a N⟧ ⟹ Q a" and
  existsI: "⟦a N; Q a⟧ ⟹ ∃x. Q x" and
  existsE: "⟦∃i. Q i; ⋀a. a N ⟹ Q a ⟹ R⟧ ⟹ R"
