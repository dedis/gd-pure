axiomatization
  eval               :: "tm ⇒ asn ⇒ val"                              and
  eval_fuel          :: "num ⇒ tm ⇒ asn ⇒ val" and
  subst_T            :: "tm ⇒ tm ⇒ tm ⇒ tm"                          and
  subst_F            :: "fm ⇒ tm ⇒ tm ⇒ fm"                          and
  subst_body         :: "tm ⇒ tm ⇒ tm ⇒ tm"                          and
  check_template     :: "fm ⇒ fm ⇒ tm ⇒ tm ⇒ fm ⇒ tm ⇒ o"        and
  rep_vars_T         :: "tm ⇒ tm ⇒ tm"                               and
  rep_vars_F         :: "fm ⇒ tm ⇒ fm"                               and
  find_phi           :: "jdg ⇒ tm ⇒ tm ⇒ pf ⇒ o"                    and
  find_eq            :: "jdg ⇒ pf ⇒ pf ⇒ o"                         and
  check_subst        :: "jdg ⇒ pf ⇒ o"                              and
  check_eq_rules     :: "hyp ⇒ tm ⇒ tm ⇒ tmtag ⇒ tmtag ⇒ pf ⇒ o"  and
  check_neq_rules    :: "hyp ⇒ tm ⇒ tm ⇒ tmtag ⇒ tmtag ⇒ pf ⇒ o"  and
  check_ind_template :: "fm ⇒ fm ⇒ tm ⇒ hyp ⇒ fm ⇒ tm ⇒ pf ⇒ o"  and
  find_ind_base      :: "jdg ⇒ tm ⇒ pf ⇒ pf ⇒ o"                   and
  check_ind          :: "jdg ⇒ pf ⇒ o"                              and
  find_cut           :: "jdg ⇒ pf ⇒ pf ⇒ o"                         and
  check_cut          :: "jdg ⇒ pf ⇒ o"                              and
  find_struct        :: "jdg ⇒ hyp ⇒ pf ⇒ o"                        and
  check_struct       :: "jdg ⇒ pf ⇒ o"                              and
  app_try            :: "jdg ⇒ num ⇒ num ⇒ num ⇒ pf ⇒ o"           and
  app_y              :: "jdg ⇒ num ⇒ num ⇒ num ⇒ pf ⇒ o"           and
  app_x              :: "jdg ⇒ num ⇒ num ⇒ pf ⇒ o"                 and
  app_d              :: "jdg ⇒ num ⇒ pf ⇒ o"                        and
  check_app          :: "jdg ⇒ pf ⇒ o"                              and
  valid_step         :: "jdg ⇒ pf ⇒ o"                              and
  check_list         :: "pf ⇒ o"                                    and
  is_valid_proof     :: "pf ⇒ jdg ⇒ o"                              and
  fresh_T            :: "num ⇒ tm ⇒ o"                              and
  fresh_F            :: "num ⇒ fm ⇒ o"                              and
  fresh_H            :: "num ⇒ hyp ⇒ o"                             and
  dfn_is             :: "dfn ⇒ num ⇒ tm ⇒ o"                        and
  asn_put            :: "asn ⇒ num ⇒ val ⇒ asn"
