lemma list_induct [case_names HQ Nil Cons]:
  "a N ⟹ Q Nil ⟹ (⋀x xs. x N ⟹ xs N ⟹ Q xs ⟹ Q (Cons x xs)) ⟹ Q a"
