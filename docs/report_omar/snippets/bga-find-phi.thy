  fixes find_phi       :: "jdg ⇒ tm ⇒ tm ⇒ pf ⇒ o"
(* Scans the proof list (ptr) for a valid premise J_phi = ⟨Γ, φ⟩
   such that Γ matches J's context, and p[v_(f+1) ↦ a] = φ and p[v_(f+1) ↦ b] = f *)
  assumes find_phi_def: "find_phi J a b ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J ∧ 
            check_template (conc_of J) (conc_of (list_hd ptr)) a b 
                           (rep_vars_F (conc_of J) (J + 1)) (J + 1) then True
    else find_phi J a b (list_tl ptr)"
