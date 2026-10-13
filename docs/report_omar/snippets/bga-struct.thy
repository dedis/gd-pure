locale bga_struct_rule = bga_encoding +


fixes find_cut    :: "jdg ⇒ pf ⇒ pf ⇒ o"
fixes check_cut   :: "jdg ⇒ pf ⇒ o"

  (* Cut Rule:
  Γ ⊢ a ⟹ a + Γ ⊢ c ⟹ Γ ⊢ c
  *)
  assumes find_cut_def: "find_cut J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J then
      if mem ((conc_of (list_hd ptr)) ▹ (hyp_of J) ⊩ (conc_of J)) rest then True
      else find_cut J rest (list_tl ptr)
    else find_cut J rest (list_tl ptr)"

  assumes check_cut_def: "check_cut J rest := find_cut J rest rest"

  fixes find_struct :: "jdg ⇒ hyp ⇒ pf ⇒ o"
  assumes find_struct_def: "find_struct J G ptr :=
    if ptr = Nil then False
    else if conc_of (list_hd ptr) = conc_of J ∧ subset (hyp_of (list_hd ptr)) G then True
    else find_struct J G (list_tl ptr)"

  fixes check_struct :: "jdg ⇒ pf ⇒ o"
  assumes check_struct_def: "check_struct J rest := find_struct J (hyp_of J) rest"
