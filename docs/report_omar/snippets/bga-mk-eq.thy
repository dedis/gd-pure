definition mk_eq :: "num ⇒ num ⇒ num" where
    "mk_eq a b ≡ pack_F 0 ⟨a, b⟩"

definition mk_neq :: "num ⇒ num ⇒ num" where
    "mk_neq a b ≡ pack_F 1 ⟨a, b⟩"
