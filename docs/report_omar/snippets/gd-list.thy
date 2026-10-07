type_synonym List = num

definition Nil :: "List" where
  "Nil ≡ 0"

definition Cons :: "num ⇒ List ⇒ List" where
  "Cons n xs ≡ ⟨n, xs⟩ + 1"

definition list_hd :: "List ⇒ num" where
  "list_hd x ≡ cpx (P x)"

definition list_tl :: "List ⇒ List" where
  "list_tl x ≡ cpy (P x)"
