locale suff_syntax =
  (*Encoding  *)
  fixes mk_eq :: "tm ⇒ tm ⇒ fm"
  fixes mk_neq :: "tm ⇒ tm ⇒ fm"
  (* Fixed Definition List*)
  fixes dfns :: "dfn"
  (*Provability. is_valid_proof \<lbrace> p \<rbrace> \<lbrace>Γ ⊢ f \<rbrace> ≡ p \<P> ⟦ Γ ⊢ f ⟧*)
  fixes is_valid_proof :: "pf ⇒ jdg ⇒ o"

  (*Habeas Quid for Syntax Constructors *)
  assumes mk_eq_N:  "⟦a N; b N⟧ ⟹ mk_eq a b N"
  assumes mk_neq_N: "⟦a N; b N⟧ ⟹ mk_neq a b N"

  (*  Habeas Quid for the Proof Checker *)
  assumes proof_bool: "⟦p N; J N⟧ ⟹ ((is_valid_proof p J) B)"
