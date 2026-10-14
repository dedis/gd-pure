fixes app_try :: "jdg ⇒ num ⇒ num ⇒ num ⇒ pf ⇒ o"
  assumes app_try_def: "app_try J d x y rest :=
    dfn_is d 2 (nth d dfns) ∧
    mem (hyp_of J ⊩ pack_F F_EQ ⟨x, x⟩) rest ∧ 
    mem (hyp_of J ⊩ pack_F F_EQ ⟨y, y⟩) rest ∧  
    find_phi J (subst_body (nth d dfns) x y) (pack_T T_APP ⟨d, ⟨x, y⟩⟩) rest"

(* Tries to see if application is satisfied for some y*)
fixes app_y :: "jdg ⇒ num ⇒ num ⇒ num ⇒ pf ⇒ o"
  assumes app_y_def: "app_y J d x y rest :=
    if app_try J d x y rest then True
    else if y > 0 = 1 then app_y J d x (y - 1) rest
    else False"

(* Tries to see if application is satisfied for some x, y with y bounded by f (where J= Γ⊢f) *)
  fixes app_x :: "jdg ⇒ num ⇒ num ⇒ pf ⇒ o"
  assumes app_x_def: "app_x J d x rest :=
    if app_y J d x (conc_of J) rest then True
    else if x > 0 = 1 then app_x J d (x - 1) rest
    else False"

(*Given a J and an upperbound for def, sees if application can be satisfied by any d,x,y triplet *)
  fixes app_d :: "jdg ⇒ num ⇒ pf ⇒ o"
  assumes app_d_def: "app_d J d rest :=
    if d < len dfns = 1 then
      (if app_x J d (conc_of J) rest then True
       else if d > 0 = 1 then app_d J (d - 1) rest else False)
    else
      (if d > 0 = 1 then app_d J (d - 1) rest else False)"

  fixes check_app :: "jdg ⇒ pf ⇒ o"
  assumes check_app_def: "check_app J rest := app_d J (len dfns - 1) rest"
