theory bijective_enc
  imports BGA_on_GA
begin


section \<open>1.   concrete encoders (Cantor-pairing based -- injective)\<close>

definition swap01 :: "num \<Rightarrow> num" where
  "swap01 t \<equiv> if t = 0 then 1 else if t = 1 then 0 else t"

definition tag_T  :: "tm \<Rightarrow> tmtag"        where "tag_T  n    \<equiv> swap01 (cpx n)"
definition load_T :: "tm \<Rightarrow> tm"           where "load_T n    \<equiv> cpy n"
definition pack_T :: "tmtag \<Rightarrow> tm \<Rightarrow> tm"   where "pack_T tg L \<equiv> \<langle>swap01 tg, L\<rangle>"
definition tag_F  :: "fm \<Rightarrow> fmtag"        where "tag_F  n    \<equiv> cpx n"
definition load_F :: "fm \<Rightarrow> tm"           where "load_F n    \<equiv> cpy n"
definition pack_F :: "fmtag \<Rightarrow> fm \<Rightarrow> fm"   where "pack_F tg L \<equiv> \<langle>tg, L\<rangle>"

lemma swap01_0 [simp]: "swap01 0 = 1"
  unfolding swap01_def by (cases bool: "(0::num) = 0", simp+)

lemma swap01_N [simp, auto]: "t N \<Longrightarrow> swap01 t N"
  unfolding swap01_def
  apply (cases bool: "t = 0", simp+)
  done

lemma swap01_inv [simp]: "t N \<Longrightarrow> swap01 (swap01 t) = t"
  unfolding swap01_def
  apply (cases bool: "t = 0", simp+)
  apply (cases bool: "t = 1", simp+)
  done


section \<open>2.  Concrete definitions of every derived function\<close>

axiomatization
  eval               :: "tm \<Rightarrow> asn \<Rightarrow> val"                              and
  subst_T            :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"                          and
  subst_F            :: "fm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"                          and
  subst_body         :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"                          and
  check_template     :: "fm \<Rightarrow> fm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm \<Rightarrow> tm \<Rightarrow> o"        and
  rep_vars_T         :: "tm \<Rightarrow> tm \<Rightarrow> tm"                               and
  rep_vars_F         :: "fm \<Rightarrow> tm \<Rightarrow> fm"                               and
  find_phi           :: "jdg \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> o"                    and
  find_eq            :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"                         and
  check_subst        :: "jdg \<Rightarrow> pf \<Rightarrow> o"                              and
  check_eq_rules     :: "hyp \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tmtag \<Rightarrow> tmtag \<Rightarrow> pf \<Rightarrow> o"  and
  check_neq_rules    :: "hyp \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tmtag \<Rightarrow> tmtag \<Rightarrow> pf \<Rightarrow> o"  and
  check_ind_template :: "fm \<Rightarrow> fm \<Rightarrow> tm \<Rightarrow> hyp \<Rightarrow> fm \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> o"  and
  find_ind_base      :: "jdg \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"                   and
  check_ind          :: "jdg \<Rightarrow> pf \<Rightarrow> o"                              and
  find_cut           :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"                         and
  check_cut          :: "jdg \<Rightarrow> pf \<Rightarrow> o"                              and
  find_struct        :: "jdg \<Rightarrow> hyp \<Rightarrow> pf \<Rightarrow> o"                        and
  check_struct       :: "jdg \<Rightarrow> pf \<Rightarrow> o"                              and
  app_try            :: "jdg \<Rightarrow> num \<Rightarrow> num \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"           and
  app_y              :: "jdg \<Rightarrow> num \<Rightarrow> num \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"           and
  app_x              :: "jdg \<Rightarrow> num \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"                 and
  app_d              :: "jdg \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"                        and
  check_app          :: "jdg \<Rightarrow> pf \<Rightarrow> o"                              and
  valid_step         :: "jdg \<Rightarrow> pf \<Rightarrow> o"                              and
  check_list         :: "pf \<Rightarrow> o"                                    and
  is_valid_proof     :: "pf \<Rightarrow> jdg \<Rightarrow> o"                              and
  fresh_T            :: "num \<Rightarrow> tm \<Rightarrow> o"                              and
  fresh_F            :: "num \<Rightarrow> fm \<Rightarrow> o"                              and
  fresh_H            :: "num \<Rightarrow> hyp \<Rightarrow> o"                             and
  dfn_is             :: "dfn \<Rightarrow> num \<Rightarrow> tm \<Rightarrow> o"                        and
  asn_put            :: "asn \<Rightarrow> num \<Rightarrow> val \<Rightarrow> asn"
where

  eval_def: "eval t A :=
    if tag_T t = T_VAR then nth (load_T t) A
    else if tag_T t = T_ZERO then 0
    else if tag_T t = T_SUC then S(eval (load_T t) A)
    else if tag_T t = T_PRED then P(eval (load_T t) A)
    else if tag_T t = T_IFZ then
      (if eval (cpx (load_T t)) A = 0
         then eval (cpx (cpy (load_T t))) A
         else eval (cpy (cpy (load_T t))) A)
    else
      eval (nth (cpx (load_T t)) dfns)
           ((eval (cpx (cpy (load_T t))) A)\<triangleright> ((eval (cpy (cpy (load_T t))) A) \<triangleright> Nil))" and

  subst_T_def: "subst_T t j v :=
    if tag_T t = T_VAR then
      (if load_T t = j then v else t)
    else if tag_T t = T_ZERO then (pack_T T_ZERO 0)
    else if tag_T t = T_SUC then (pack_T T_SUC (subst_T (load_T t) j v))
    else if tag_T t = T_PRED then (pack_T T_PRED (subst_T (load_T t) j v))
    else if tag_T t = T_IFZ then
      (pack_T T_IFZ \<langle>subst_T (cpx (load_T t)) j v
            , \<langle>(subst_T (cpx (cpy (load_T t))) j v),
            (subst_T (cpy (cpy (load_T t))) j v)\<rangle>\<rangle>)
    else
      (pack_T T_APP \<langle>(cpx (load_T t)), \<langle>
             (subst_T (cpx (cpy (load_T t))) j v),
             (subst_T (cpy (cpy (load_T t))) j v)\<rangle>\<rangle>)" and

  subst_F_def: "subst_F f j v :=
    if tag_F f = F_EQ then
      pack_F F_EQ \<langle>(subst_T (cpx (load_F f)) j v), (subst_T (cpy (load_F f)) j v)\<rangle>
    else
      pack_F F_NEQ \<langle>(subst_T (cpx (load_F f)) j v), (subst_T (cpy (load_F f)) j v)\<rangle>" and

  subst_body_def: "subst_body b x y :=
    if tag_T b = T_VAR then
      (if load_T b = 0 then x else if load_T b = 1 then y else b)
    else if tag_T b = T_ZERO then b
    else if tag_T b = T_SUC  then pack_T T_SUC  (subst_body (load_T b) x y)
    else if tag_T b = T_PRED then pack_T T_PRED (subst_body (load_T b) x y)
    else if tag_T b = T_IFZ  then
      pack_T T_IFZ \<langle>subst_body (cpx (load_T b)) x y,
               \<langle>subst_body (cpx (cpy (load_T b))) x y,
                subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
    else
      pack_T T_APP \<langle>cpx (load_T b),
               \<langle>subst_body (cpx (cpy (load_T b))) x y,
                subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>" and

  fresh_T_def: "fresh_T k t :=
       if tag_T t = T_VAR then load_T t < k = 1
       else if tag_T t = T_ZERO then True
       else if tag_T t = T_SUC then fresh_T k (load_T t)
       else if tag_T t = T_PRED then fresh_T k (load_T t)
       else if tag_T t = T_IFZ then
         fresh_T k (cpx (load_T t)) \<and>
         fresh_T k (cpx (cpy (load_T t))) \<and>
         fresh_T k (cpy (cpy (load_T t)))
       else if tag_T t = T_APP then
         fresh_T k (cpx (cpy (load_T t))) \<and>
         fresh_T k (cpy (cpy (load_T t)))
       else False" and

  fresh_F_def: "fresh_F k f := fresh_T k (cpx (load_F f)) \<and> fresh_T k (cpy (load_F f))" and

  fresh_H_def: "fresh_H k G := if G = Nil then True else fresh_F k (list_hd G) \<and> fresh_H k (list_tl G)" and

  dfn_is_def: "dfn_is d k b := if d < len dfns = 1 then nth d dfns = b \<and> fresh_T k b else False" and

  asn_put_def: "asn_put A i v :=
      if i = 0 then
        if A = Nil then v \<triangleright> Nil
        else v \<triangleright> list_tl A
      else if A = Nil then 0 \<triangleright> asn_put Nil (i - 1) v
      else list_hd A \<triangleright> asn_put (list_tl A) (i - 1) v" and

  check_template_def: "check_template f phi a b p i :=
    if subst_F p i a = phi \<and> subst_F p i b = f then True
    else if p > 0 = 1 then check_template f phi a b (p - 1) i
    else False" and

  rep_vars_T_def: "rep_vars_T t i :=
    if tag_T t = T_VAR then pack_T T_VAR i
    else if tag_T t = T_ZERO then pack_T T_VAR i
    else if tag_T t = T_SUC then pack_T T_SUC (rep_vars_T (load_T t) i)
    else if tag_T t = T_PRED then pack_T T_PRED (rep_vars_T (load_T t) i)
    else if tag_T t = T_IFZ then
      pack_T T_IFZ \<langle>rep_vars_T (cpx (load_T t)) i,
               \<langle>rep_vars_T (cpx (cpy (load_T t))) i,
                rep_vars_T (cpy (cpy (load_T t))) i\<rangle>\<rangle>
    else
      pack_T T_APP \<langle>cpx (load_T t),
               \<langle>rep_vars_T (cpx (cpy (load_T t))) i,
                rep_vars_T (cpy (cpy (load_T t))) i\<rangle>\<rangle>" and

  rep_vars_F_def: "rep_vars_F f i :=
    if tag_F f = F_EQ then
      pack_F F_EQ \<langle>rep_vars_T (cpx (load_F f)) i, rep_vars_T (cpy (load_F f)) i\<rangle>
    else
      pack_F F_NEQ \<langle>rep_vars_T (cpx (load_F f)) i, rep_vars_T (cpy (load_F f)) i\<rangle>" and

  find_phi_def: "find_phi J a b ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J \<and>
            check_template (conc_of J) (conc_of (list_hd ptr)) a b
                           (rep_vars_F (conc_of J) (J + 1)) (J + 1) then True
    else find_phi J a b (list_tl ptr)" and

  find_eq_def: "find_eq J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J \<and> tag_F (conc_of (list_hd ptr)) = F_EQ then
      if find_phi J (cpx (load_F (conc_of (list_hd ptr)))) (cpy (load_F (conc_of (list_hd ptr)))) rest then True
      else find_eq J rest (list_tl ptr)
    else find_eq J rest (list_tl ptr)" and

  check_subst_def: "check_subst J rest := find_eq J rest rest" and

  check_eq_rules_def: "check_eq_rules G lhs rhs tg_L tg_R rest :=
    if lhs = pack_T T_ZERO 0 \<and> rhs = pack_T T_ZERO 0 then True
    else if mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, lhs\<rangle>) rest then True
    else if tg_L = T_SUC \<and> tg_R = T_SUC \<and>
            mem (G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T rhs\<rangle>) rest then True
    else if mem (G \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle>) rest then True
    else if tg_L = T_PRED \<and> tag_T (load_T lhs) = T_SUC \<and>
            (load_T (load_T lhs)) = rhs \<and>
            mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) rest then True
    else if tg_L = T_IFZ \<and> rhs = cpy (cpy (load_T lhs)) \<and>
            mem (G \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) rest \<and>
            mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) rest then True
    else if tg_L = T_IFZ \<and> rhs = cpx (cpy (load_T lhs)) \<and>
            mem (G \<tturnstile> pack_F F_EQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) rest \<and>
            mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) rest then True
    else False" and

  check_neq_rules_def: "check_neq_rules G lhs rhs tg_L tg_R rest :=
    if mem (G \<tturnstile> pack_F F_NEQ \<langle>rhs, lhs\<rangle>) rest then True
    else if tg_L = T_SUC \<and> rhs = pack_T T_ZERO 0 \<and>
            mem (G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T lhs\<rangle>) rest then True
    else if tg_L = T_SUC \<and> tg_R = T_SUC \<and>
            mem (G \<tturnstile> pack_F F_NEQ \<langle>load_T lhs, load_T rhs\<rangle>) rest then True
    else if mem (G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle>) rest then True
    else False" and

  check_ind_template_def: "check_ind_template f phi a G p i rest :=
    if subst_F p i a = f \<and>
       subst_F p i (pack_T T_ZERO 0) = phi \<and>
       mem (pack_F F_EQ \<langle>pack_T T_VAR i, pack_T T_VAR i\<rangle> \<triangleright> p \<triangleright> G \<tturnstile>
                subst_F p i (pack_T T_SUC (pack_T T_VAR i))) rest
    then True
    else if p > 0 = 1 then check_ind_template f phi a G (p - 1) i rest
    else False" and

  find_ind_base_def: "find_ind_base J a rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J then
      if check_ind_template (conc_of J) (conc_of (list_hd ptr)) a (hyp_of J)
                            (rep_vars_F (conc_of J) (J + 1)) (J + 1) rest
      then True
      else find_ind_base J a rest (list_tl ptr)
    else find_ind_base J a rest (list_tl ptr)" and

  check_ind_def: "check_ind J rest :=
    if fresh_H (J + 1) (hyp_of J) \<and> mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest then
       find_ind_base J (cpx (load_F (conc_of J))) rest rest
    else False" and

  find_cut_def: "find_cut J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J then
      if mem ((conc_of (list_hd ptr)) \<triangleright> (hyp_of J) \<tturnstile> (conc_of J)) rest then True
      else find_cut J rest (list_tl ptr)
    else find_cut J rest (list_tl ptr)" and

  check_cut_def: "check_cut J rest := find_cut J rest rest" and

  find_struct_def: "find_struct J G ptr :=
    if ptr = Nil then False
    else if conc_of (list_hd ptr) = conc_of J \<and> subset (hyp_of (list_hd ptr)) G then True
    else find_struct J G (list_tl ptr)" and

  check_struct_def: "check_struct J rest := find_struct J (hyp_of J) rest" and

  app_try_def: "app_try J d x y rest :=
    dfn_is d 2 (nth d dfns) \<and>
    mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) rest \<and>
    mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) rest \<and>
    find_phi J (subst_body (nth d dfns) x y) (pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>) rest" and

  app_y_def: "app_y J d x y rest :=
    if app_try J d x y rest then True
    else if y > 0 = 1 then app_y J d x (y - 1) rest
    else False" and

  app_x_def: "app_x J d x rest :=
    if app_y J d x (conc_of J) rest then True
    else if x > 0 = 1 then app_x J d (x - 1) rest
    else False" and

  app_d_def: "app_d J d rest :=
    if d < len dfns = 1 then
      (if app_x J d (conc_of J) rest then True
       else if d > 0 = 1 then app_d J (d - 1) rest else False)
    else
      (if d > 0 = 1 then app_d J (d - 1) rest else False)" and

  check_app_def: "check_app J rest := app_d J (len dfns - 1) rest" and

  valid_step_def: "valid_step J rest :=
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
                      (tag_T (cpx (load_F (conc_of J)))) (tag_T (cpy (load_F (conc_of J)))) rest" and

  check_list_def: "check_list prf :=
    if prf = Nil then True
    else if valid_step (list_hd prf) (list_tl prf) then check_list (list_tl prf)
    else False" and

  is_valid_proof_def: "is_valid_proof prf J :=
    if prf = Nil then False
    else if list_hd prf = J then check_list prf
    else False"


axiomatization dfns :: "dfn" where dfns_N: "dfns N"

section \<open>3.  Encoder obligations\<close>

lemma pack_F_N:
  assumes t: "t N" and L: "L N" shows "pack_F t L N"
  unfolding pack_F_def by (rule cpair_terminates[OF t L])

lemma tag_F_N:
  assumes f: "f N" shows "tag_F f N"
  unfolding tag_F_def by (rule cpx_terminates[OF f])

lemma load_F_N:
  assumes f: "f N" shows "load_F f N"
  unfolding load_F_def by (rule cpy_terminates[OF f])

lemma pack_T_N:
  assumes t: "t N" and L: "L N" shows "pack_T t L N"
  unfolding pack_T_def by (rule cpair_terminates[OF swap01_N[OF t] L])

lemma tag_T_N:
  assumes t: "t N" shows "tag_T t N"
  unfolding tag_T_def by (rule swap01_N[OF cpx_terminates[OF t]])

lemma load_T_N:
  assumes t: "t N" shows "load_T t N"
  unfolding load_T_def by (rule cpy_terminates[OF t])

lemma tag_pack_F:
  assumes t: "t N" and L: "L N" shows "tag_F (pack_F t L) = t"
  unfolding tag_F_def pack_F_def by (rule cpx_proj[OF t L])

lemma load_pack_F:
  assumes t: "t N" and L: "L N" shows "load_F (pack_F t L) = L"
  unfolding load_F_def pack_F_def by (rule cpy_proj[OF t L])

lemma tag_pack_T:
  assumes t: "t N" and L: "L N" shows "tag_T (pack_T t L) = t"
  unfolding tag_T_def pack_T_def
  using t by (simp add: cpx_proj[OF swap01_N[OF t] L] swap01_inv[OF t])

lemma load_pack_T:
  assumes t: "t N" and L: "L N" shows "load_T (pack_T t L) = L"
  unfolding load_T_def pack_T_def by (rule cpy_proj[OF swap01_N[OF t] L])

lemma pack_tag_F:
  assumes f: "f N" shows "pack_F (tag_F f) (load_F f) = f"
  unfolding pack_F_def tag_F_def load_F_def
  apply (rule eqSym) using f apply auto done

lemma pack_tag_T:
  assumes t: "t N" shows "pack_T (tag_T t) (load_T t) = t"
  unfolding pack_T_def tag_T_def load_T_def
  apply (simp only: swap01_inv[OF cpx_terminates[OF t]])
  apply (rule eqSym) using t apply auto done

lemma decrease_F:
  assumes f: "f N" and nz: "f \<noteq> 0" shows "load_F f < f = 1"
  unfolding load_F_def using f nz by simp

lemma decrease_T:
  assumes t: "t N" and nz: "t \<noteq> 0" shows "load_T t < t = 1"
  unfolding load_T_def using t nz by simp

lemma tag_T_zero: "tag_T 0 = T_ZERO"
  unfolding tag_T_def by simp

(* single successor step: \<langle>a,k\<rangle> \<le> \<langle>a,S k\<rangle>, from cpair_suc + leq_monotone_add_r *)
lemma pair_step:
  assumes a: "a N" and k: "k N"
  shows "\<langle>a, k\<rangle> \<le> \<langle>a, S k\<rangle> = 1"
proof -
  have ak: "\<langle>a, k\<rangle> N"       by (rule cpair_terminates[OF a k])
  have sk: "S k N"          by (rule natS[OF k])
  have one: "(1::num) N"    by simp
  have aka:  "\<langle>a, k\<rangle> + a N"          using ak a by simp
  have akask: "\<langle>a, k\<rangle> + a + S k N"   using aka sk by simp
  have s1: "\<langle>a, k\<rangle> \<le> \<langle>a, k\<rangle> = 1"                     by (rule leq_refl[OF ak])
  have s2: "\<langle>a, k\<rangle> \<le> \<langle>a, k\<rangle> + a = 1"                 by (rule leq_monotone_add_r[OF s1 ak ak a])
  have s3: "\<langle>a, k\<rangle> \<le> \<langle>a, k\<rangle> + a + S k = 1"           by (rule leq_monotone_add_r[OF s2 ak aka sk])
  have s4: "\<langle>a, k\<rangle> \<le> \<langle>a, k\<rangle> + a + S k + 1 = 1"       by (rule leq_monotone_add_r[OF s3 ak akask one])
  have e:  "\<langle>a, S k\<rangle> = \<langle>a, k\<rangle> + a + S k + 1"          by (rule cpair_suc[OF a k])
  show ?thesis using s4 e by simp
qed

lemma pair_mono_2:
  assumes a: "a N" and x: "x N" and y: "y N" and h: "x \<le> y = 1"
  shows "\<langle>a, x\<rangle> \<le> \<langle>a, y\<rangle> = 1"
proof -
  have one: "(1::num) N" by simp
  have main: "(x \<le> y = 1) \<longrightarrow> (\<langle>a, x\<rangle> \<le> \<langle>a, y\<rangle> = 1)"
  proof (rule ind[where a = y])
    show "y N" by (rule y)
  next
    show "(x \<le> 0 = 1) \<longrightarrow> (\<langle>a, x\<rangle> \<le> \<langle>a, 0\<rangle> = 1)"
    proof (rule implI)
      show "(x \<le> 0 = 1) B" by (rule eqBool[OF leq_terminates[OF x nat0] one])
    next
      assume x0: "x \<le> 0 = 1"
      have "x = 0" by (rule leq_0[OF x x0])
      thus "\<langle>a, x\<rangle> \<le> \<langle>a, 0\<rangle> = 1"
        by (simp add: leq_refl[OF cpair_terminates[OF a nat0]])
    qed
  next
    fix k assume k: "k N" and IH: "(x \<le> k = 1) \<longrightarrow> (\<langle>a, x\<rangle> \<le> \<langle>a, k\<rangle> = 1)"
    show "(x \<le> S k = 1) \<longrightarrow> (\<langle>a, x\<rangle> \<le> \<langle>a, S k\<rangle> = 1)"
    proof (rule implI)
      show "(x \<le> S k = 1) B" by (rule eqBool[OF leq_terminates[OF x natS[OF k]] one])
    next
      assume xsk: "x \<le> S k = 1"
      have ax:  "\<langle>a, x\<rangle> N"   by (rule cpair_terminates[OF a x])
      have ak:  "\<langle>a, k\<rangle> N"   by (rule cpair_terminates[OF a k])
      have ask: "\<langle>a, S k\<rangle> N" by (rule cpair_terminates[OF a natS[OF k]])
      have step: "\<langle>a, k\<rangle> \<le> \<langle>a, S k\<rangle> = 1" by (rule pair_step[OF a k])
      show "\<langle>a, x\<rangle> \<le> \<langle>a, S k\<rangle> = 1"
      proof (rule cases_bool[where q = "x \<le> k = 1"])
        show "(x \<le> k = 1) B" by (rule eqBool[OF leq_terminates[OF x k] one])
      next
        assume xk: "x \<le> k = 1"
        have xy: "\<langle>a, x\<rangle> \<le> \<langle>a, k\<rangle> = 1" by (rule implE[OF IH xk])
        show "\<langle>a, x\<rangle> \<le> \<langle>a, S k\<rangle> = 1" by (rule leq_trans[OF ax ak ask xy step])
      next
        assume nxk: "\<not> (x \<le> k = 1)"
        have "x = S k" by (rule leq_suc_not_leq_implies_eq[OF x k nxk xsk])
        thus "\<langle>a, x\<rangle> \<le> \<langle>a, S k\<rangle> = 1" by (simp add: leq_refl[OF ask])
      qed
    qed
  qed
  show ?thesis by (rule implE[OF main h])
qed

lemma mono_pack_T:
  assumes tg: "tg N" and x: "x N" and y: "y N" and h: "x \<le> y = 1"
  shows "pack_T tg x \<le> pack_T tg y = 1"
  unfolding pack_T_def by (rule pair_mono_2[OF swap01_N[OF tg] x y h])

lemma mono_pack_F:
  assumes tg: "tg N" and x: "x N" and y: "y N" and h: "x \<le> y = 1"
  shows "pack_F tg x \<le> pack_F tg y = 1"
  unfolding pack_F_def by (rule pair_mono_2[OF tg x y h])


section \<open>4.  Interpret bga_full. transfers `consistent` to this instance\<close>

interpretation conc: bga_full
  tag_T load_T pack_T tag_F load_F pack_F fresh_T fresh_F fresh_H dfns dfn_is
  eval
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
              fresh_T_def fresh_F_def fresh_H_def dfn_is_def asn_put_def
              eval_def subst_T_def subst_F_def subst_body_def
              check_template_def rep_vars_T_def rep_vars_F_def find_phi_def
              find_eq_def check_subst_def check_eq_rules_def check_neq_rules_def
              check_ind_template_def find_ind_base_def check_ind_def
              find_cut_def check_cut_def find_struct_def check_struct_def
              app_try_def app_y_def app_x_def app_d_def check_app_def
              valid_step_def check_list_def is_valid_proof_def)+
  done

end
