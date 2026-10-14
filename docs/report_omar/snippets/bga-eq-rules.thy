  fixes check_eq_rules  :: "hyp ⇒ tm ⇒ tm ⇒ tmtag ⇒ tmtag ⇒ pf ⇒ o"
(* Equality Rules
1. Γ ⊢ 0 N
2. Γ ⊢ a=b ⟹ Γ ⊢ b=a
3. Γ ⊢ a=b ⟹ Γ ⊢ S(a)=S(b)
4. Γ ⊢ S(a)=S(b) ⟹ Γ ⊢ a=b
5. Γ ⊢ a N ⟹ Γ ⊢ P(S(a))=a
6. Γ ⊢ c≠0 ⟹ Γ ⊢ b N ⟹ Γ ⊢ (c 0? a: b)=b
7. Γ ⊢ c=0 ⟹ Γ ⊢ a N ⟹ Γ ⊢ (c 0? a: b)=a
*)
  assumes check_eq_rules_def: "check_eq_rules G lhs rhs tg_L tg_R rest :=
    if lhs = pack_T T_ZERO 0 ∧ rhs = pack_T T_ZERO 0 then True
    else if mem (G ⊩ pack_F F_EQ ⟨rhs, lhs⟩) rest then True
    else if tg_L = T_SUC ∧ tg_R = T_SUC ∧ 
            mem (G ⊩ pack_F F_EQ ⟨load_T lhs, load_T rhs⟩) rest then True
    else if mem (G ⊩ pack_F F_EQ ⟨pack_T T_SUC lhs, pack_T T_SUC rhs⟩) rest then True
    else if tg_L = T_PRED ∧ tag_T (load_T lhs) = T_SUC ∧ 
            (load_T (load_T lhs)) = rhs ∧ 
            mem (G ⊩ pack_F F_EQ ⟨rhs, rhs⟩) rest then True
    else if tg_L = T_IFZ ∧ rhs = cpy (cpy (load_T lhs)) ∧ 
            mem (G ⊩ pack_F F_NEQ ⟨cpx (load_T lhs), pack_T T_ZERO 0⟩) rest ∧
            mem (G ⊩ pack_F F_EQ ⟨rhs, rhs⟩) rest then True
    else if tg_L = T_IFZ ∧ rhs = cpx (cpy (load_T lhs)) ∧ 
            mem (G ⊩ pack_F F_EQ ⟨cpx (load_T lhs), pack_T T_ZERO 0⟩) rest ∧
            mem (G ⊩ pack_F F_EQ ⟨rhs, rhs⟩) rest then True
    else False"
