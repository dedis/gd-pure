  fixes find_eq        :: "jdg ⇒ pf ⇒ pf ⇒ o"
(* Scans the proof list (ptr) for an equality judgment J_eq = ⟨Γ, a = b⟩
   such that Γ matches J's context, and calls find_phi *)
  assumes find_eq_def: "find_eq J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J ∧ tag_F (conc_of (list_hd ptr)) = F_EQ then
      if find_phi J (cpx (load_F (conc_of (list_hd ptr)))) (cpy (load_F (conc_of (list_hd ptr)))) rest then True
      else find_eq J rest (list_tl ptr)
    else find_eq J rest (list_tl ptr)"
  fixes check_subst    :: "jdg ⇒ pf ⇒ o"

(* checking the substitution rule *)
assumes check_subst_def: "check_subst J rest := find_eq J rest rest"
