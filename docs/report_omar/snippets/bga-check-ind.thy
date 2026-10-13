  fixes check_ind       :: "jdg ⇒ pf ⇒ o"
  (* check_ind triggers the search if the Habeas Quid premise Γ ⊢ a N (encoded as a=a) exists *)
  assumes check_ind_def: "check_ind J rest :=
    if fresh_H (J + 1) (hyp_of J) ∧ mem (hyp_of J ⊩ pack_F F_EQ ⟨cpx (load_F (conc_of J)), cpx (load_F (conc_of J))⟩) rest then
       find_ind_base J (cpx (load_F (conc_of J))) rest rest
    else False"
