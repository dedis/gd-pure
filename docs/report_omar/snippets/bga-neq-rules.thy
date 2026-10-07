  fixes check_neq_rules :: "hyp ⇒ tm ⇒ tm ⇒ tmtag ⇒ tmtag ⇒ pf ⇒ o"
(* Not-Equality Rules
1. Γ ⊢ a≠b ⟹ Γ ⊢ b≠a
2. Γ ⊢ a N ⟹ Γ ⊢ S(a)≠0
3. Γ ⊢ a≠b ⟹ Γ ⊢ S(a)≠S(b)
4. Γ ⊢ S(a)≠S(b) ⟹ Γ ⊢ a≠b
*)
  assumes check_neq_rules_def: "check_neq_rules G lhs rhs tg_L tg_R rest :=
    if mem (G ⊩ pack_F F_NEQ ⟨rhs, lhs⟩) rest then True
    else if tg_L = T_SUC ∧ rhs = pack_T T_ZERO 0 ∧ 
            mem (G ⊩ pack_F F_EQ ⟨load_T lhs, load_T lhs⟩) rest then True
    else if tg_L = T_SUC ∧ tg_R = T_SUC ∧ 
            mem (G ⊩ pack_F F_NEQ ⟨load_T lhs, load_T rhs⟩) rest then True
    else if mem (G ⊩ pack_F F_NEQ ⟨pack_T T_SUC lhs, pack_T T_SUC rhs⟩) rest then True
    else False"
