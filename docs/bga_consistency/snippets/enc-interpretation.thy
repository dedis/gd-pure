interpretation conc2: bga_fuller
  tag_T load_T pack_T tag_F load_F pack_F fresh_T fresh_F fresh_H dfns dfn_is
  eval_fuel
  subst_T subst_F subst_body asn_put
  check_template rep_vars_T rep_vars_F find_phi find_eq check_subst
  check_eq_rules check_neq_rules
  check_ind_template find_ind_base check_ind
  find_cut check_cut find_struct check_struct
  app_try app_y app_x app_d check_app
  valid_step check_list is_valid_proof
  apply unfold_locales
  apply (fact dfns_N pack_F_N tag_F_N load_F_N pack_T_N tag_T_N load_T_N
              tag_pack_F load_pack_F tag_pack_T load_pack_T pack_tag_F pack_tag_T
              decrease_F decrease_T tag_T_zero mono_pack_T mono_pack_F
              fresh_T_def fresh_F_def fresh_H_def dfn_is_def eval_fuel_def
              subst_T_def subst_F_def subst_body_def asn_put_def
              check_template_def rep_vars_T_def rep_vars_F_def find_phi_def
              find_eq_def check_subst_def check_eq_rules_def check_neq_rules_def
              check_ind_template_def find_ind_base_def check_ind_def
              find_cut_def check_cut_def find_struct_def check_struct_def
              app_try_def app_y_def app_x_def app_d_def check_app_def
              valid_step_def check_list_def is_valid_proof_def)+
  done
