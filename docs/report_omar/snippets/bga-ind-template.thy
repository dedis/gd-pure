fixes check_ind_template :: "fm ⇒ fm ⇒ tm ⇒ hyp ⇒ fm ⇒ tm ⇒ pf ⇒ o"
(*counts down 'p', testing if it is the valid induction template 
checks for a p such that:
p[v_i → a] = φ
Γ ⊢ p[v_i → 0] in proof
[v_i = v_i, p]+Γ ⊢ p[v_i → S(v_i)] in proof

*)
  assumes check_ind_template_def: "check_ind_template f phi a G p i rest :=
    if subst_F p i a = f ∧ 
       subst_F p i (pack_T T_ZERO 0) = phi ∧
       mem (pack_F F_EQ ⟨pack_T T_VAR i, pack_T T_VAR i⟩ ▹ p ▹ G ⊩ 
                subst_F p i (pack_T T_SUC (pack_T T_VAR i))) rest
    then True
    else if p > 0 = 1 then check_ind_template f phi a G (p - 1) i rest
    else False"
