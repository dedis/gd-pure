fixes valid_step :: "jdg ⇒ pf ⇒ o"

(* The main step check
1. 1 hyp Rule
2. 1 Cut Rule
3. 1 Subst Rule
4. 1 Induction Rule
5. 7 Equality Rules
6. 4 Not-equality rules
7. 1 app2I rule
8. 1 wk1 rule
sub1
 *)
  assumes valid_step_def: "valid_step J rest :=
    if mem (conc_of J) (hyp_of J) then True
    else if check_cut J rest then True
    else if check_subst J rest then True
    else if check_ind J rest then True
    else if check_app J rest then True
    else if check_struct J rest then True
    else if tag_F (conc_of J) = F_EQ then
      check_eq_rules (hyp_of J) (cpx (load_F (conc_of J))) (cpy (load_F (conc_of J))) 
                     (tag_T (cpx (load_F (conc_of J)))) (tag_T (cpy (load_F (conc_of J)))) rest
    else
      check_neq_rules (hyp_of J) (cpx (load_F (conc_of J))) (cpy (load_F (conc_of J))) 
                      (tag_T (cpx (load_F (conc_of J)))) (tag_T (cpy (load_F (conc_of J)))) rest"
