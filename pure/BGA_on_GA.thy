theory BGA_on_GA
  imports GD
begin

(* The idea is to abstract the encodings into a locale with the minimum assumptions needed to prove consistency. 
And we deal with the arithmetic nightmare exactly once during instantiation. *)

(* Type Aliases for Readability *)
type_synonym tm  = num  (* BGA Term *)
type_synonym fm  = num  (* BGA Formula *)
type_synonym asn = num  (* Assignment *)
type_synonym dfn = num  (* Definition *)
type_synonym pf = num  (* Proof: List of judgements *)
type_synonym val = num  (* Evaluated Value *)

type_synonym hyp = num  (* Hypothesis: list/set of formulas *)
type_synonym jdg = num  (* Judgment: \<langle>hyp, fm\<rangle> *)

abbreviation hyp_of :: "jdg \<Rightarrow> hyp" where "hyp_of J \<equiv> cpx J"
abbreviation conc_of :: "jdg \<Rightarrow> fm" where "conc_of J \<equiv> cpy J"

abbreviation mk_jdg :: "hyp \<Rightarrow> fm \<Rightarrow> jdg" (infix "\<tturnstile>" 50)
  where "G \<tturnstile> c \<equiv> \<langle>G, c\<rangle>"
abbreviation emptyH :: "hyp" ("\<emptyset>")
  where "\<emptyset> \<equiv> Nil"
abbreviation cons  :: "fm \<Rightarrow> List \<Rightarrow> List" (infixr "\<triangleright>" 65)
  where "f \<triangleright> G \<equiv> Cons f G"

locale suff_syntax =
  (*Encoding  *)
  fixes mk_eq :: "tm \<Rightarrow> tm \<Rightarrow> fm"
  fixes mk_neq :: "tm \<Rightarrow> tm \<Rightarrow> fm"
  (* Fixed Definition List*)
  fixes dfns :: "dfn"
  (*Provability. is_valid_proof \<lbrace> p \<rbrace> \<lbrace>\<Gamma> \<turnstile> f \<rbrace> \<equiv> p \<P> \<lbrakk> \<Gamma> \<turnstile> f \<rbrakk>*)
  fixes is_valid_proof :: "pf \<Rightarrow> jdg \<Rightarrow> o"

  (*Habeas Quid for Syntax Constructors *)
  assumes mk_eq_N:  "\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow> mk_eq a b N"
  assumes mk_neq_N: "\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow> mk_neq a b N"

  (*  Habeas Quid for the Proof Checker *)
  assumes proof_bool: "\<lbrakk>p N; J N\<rbrakk> \<Longrightarrow> ((is_valid_proof p J) B)"

locale suff_semantics = suff_syntax +
  (*Semantics. sat checks whether the encoding of a formula is satisfied by an assignment. eval reduces a term under an assignment*)

  fixes evals :: "tm \<Rightarrow> asn \<Rightarrow> val \<Rightarrow> o"
  fixes sat_fm :: "fm \<Rightarrow> asn \<Rightarrow> o"
  fixes sat_hyp :: "hyp \<Rightarrow> asn \<Rightarrow> o"

  assumes sat_hyp_nil: "sat_hyp Nil A"

  (* Evaluation is deterministic *)
  assumes evals_det: "\<lbrakk>t N; A N; evals t A r; evals t A q\<rbrakk> \<Longrightarrow> r = q"

  (* What equations mean in the model: the two sides evaluate to a common value
     (resp. to distinct values). *)
  assumes sat_eqE:
    "\<lbrakk>a N; b N; sat_fm (mk_eq a b) A;
      \<And>q. \<lbrakk>q N; evals a A q; evals b A q\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  assumes sat_neqE:
    "\<lbrakk>a N; b N; sat_fm (mk_neq a b) A;
      \<And>x y. \<lbrakk>x N; y N; evals a A x; evals b A y; x \<noteq> y\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"

locale consistent =  suff_semantics +
  (* Valid proofs yield satisfied formulas *)
  assumes soundness: "\<lbrakk>is_valid_proof p J; sat_hyp (hyp_of J) A; A N\<rbrakk> \<Longrightarrow> sat_fm (conc_of J) A"
begin

lemma syntactically_consistent:
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  assumes p1_nat: "p1 N"
  assumes p2_nat: "p2 N"
  shows " \<not> (is_valid_proof p1 \<langle>Nil, (mk_eq a b)\<rangle> \<and> is_valid_proof p2 \<langle>Nil, (mk_neq a b)\<rangle>)"

  apply (rule contradiction[where p=" \<not> (is_valid_proof p1 \<langle>Nil, (mk_eq a b)\<rangle> \<and> is_valid_proof p2 \<langle>Nil, (mk_neq a b)\<rangle>)"])
   apply simp

proof - 
  have mk_eq_nat: " mk_eq a b N"
    using a_nat b_nat apply (rule mk_eq_N)
    done

  have mk_neq_nat: " mk_neq a b N"
    using a_nat b_nat apply (rule mk_neq_N)
    done
  have J_eq_nat: "\<langle>Nil, mk_eq a b\<rangle> N"
    using mk_eq_nat apply simp
    done

  have J_neq_nat: "\<langle>Nil, mk_neq a b\<rangle> N"
    using mk_neq_nat apply simp
    done
  show " is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> B"
    using p1_nat J_eq_nat apply (rule proof_bool)
    done

  show " is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle> B"
    using p2_nat J_neq_nat apply (rule proof_bool)
    done
  show " \<not> \<not> (is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>) \<Longrightarrow> False "

  proof -
    assume double_neg: "\<not> \<not> (is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>)"

    have conj_holds: "is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>"
      apply (rule dNegE)
      apply (rule double_neg)
      done

    have eq_pf: "is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle>"
      apply (rule conjE1)
      apply (rule conj_holds)
      done

    have neq_pf: "is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>"
      apply (rule conjE2)
      apply (rule conj_holds)
      done

    have eq_sat: "sat_fm  (conc_of \<langle>Nil, mk_eq a b\<rangle>) zero"
      apply (rule soundness)
        apply (rule eq_pf)
       using mk_eq_nat apply simp
      apply (rule sat_hyp_nil)
      apply (rule nat0)
      done

    have eq_sat1: "sat_fm (mk_eq a b) zero"
      using eq_sat mk_eq_nat apply simp
      done

    have neq_sat: "sat_fm  (conc_of \<langle>Nil, mk_neq a b\<rangle>) zero"
      apply (rule soundness)
        apply (rule neq_pf)
       using mk_neq_nat apply simp
      apply (rule sat_hyp_nil)
      apply (rule nat0)
      done
    have neq_sat1: "sat_fm (mk_neq a b) zero"
      using neq_sat mk_neq_nat apply simp
      done

    show "False"
    proof (rule sat_eqE[OF a_nat b_nat eq_sat1])
      fix q assume qN: "q N" and eaq: "evals a zero q" and ebq: "evals b zero q"
      show "False"
      proof (rule sat_neqE[OF a_nat b_nat neq_sat1])
        fix x y assume xN: "x N" and yN: "y N"
          and eax: "evals a zero x" and eby: "evals b zero y" and xy: "x \<noteq> y"
        have xq: "x = q" by (rule evals_det[OF a_nat nat0 eax eaq])
        have yq: "y = q" by (rule evals_det[OF b_nat nat0 eby ebq])
        have xyeq: "x = y" by (rule eq_trans[OF xq eqSym[OF yq]])
        show "False" by (rule exF[OF xyeq xy[unfolded neq_def]])
      qed
    qed
  qed
qed

end

type_synonym tmtag = num
type_synonym fmtag = num


(*
Term Tags: Constructor Name : Syntax : Argument
0 : Variable : v_j : j
1 : Zero : 0 : (Ignored)
2 : Successor : S(a) : a encoded term)
3 : Predecessor : P(a) : a
4 : If-Zero : c0?a:b : \<langle>c, \<langle>a, b\<rangle>\<rangle>
5 : Application : d_i(a,b) : \<langle>i, \<langle>a, b\<rangle>\<rangle>

Formula Tags: Constructor Name : Syntax : Argument
0 : Equality : a=b : \<langle>a, b\<rangle>
1 : Inequality : a\<noteq>b : \<langle>a, b\<rangle>
*)

  (* Term Constructor Tags *)
  abbreviation T_VAR  :: num where "T_VAR \<equiv> 0"
  abbreviation T_ZERO :: num where "T_ZERO \<equiv> 1"
  abbreviation T_SUC  :: num where "T_SUC \<equiv> 2"
  abbreviation T_PRED :: num where "T_PRED \<equiv> 3"
  abbreviation T_IFZ  :: num where "T_IFZ \<equiv> 4"
  abbreviation T_APP  :: num where "T_APP \<equiv> 5"

  (* Formula Constructor Tags *)
  abbreviation F_EQ   :: num where "F_EQ \<equiv> 0"
  abbreviation F_NEQ  :: num where "F_NEQ \<equiv> 1"

(* Using the following convention:
Definitions not fundamental to the logic (like arithmetic, list etc) will be made in locales and not as axioms.
*)

locale bga_bijective_encoding =
  (*Term Encoding *)
  (* Tag of the current Constructor *)
  fixes tag_T :: "tm \<Rightarrow> tmtag"
  (* Encoding of the argument *)
  fixes load_T :: "tm \<Rightarrow> tm"
  (* Encodes the term *)
  fixes pack_T :: "tmtag \<Rightarrow> tm \<Rightarrow> tm"

  (* Formula Encoding *)
  fixes tag_F :: "fm \<Rightarrow> fmtag"
  fixes load_F :: "fm \<Rightarrow> tm"
  fixes pack_F :: "fmtag \<Rightarrow> fm \<Rightarrow> fm"

(* Fixing Definition*)
  fixes fresh_T :: "num \<Rightarrow> tm \<Rightarrow> o"
  fixes fresh_F :: "num \<Rightarrow> fm \<Rightarrow> o"
  fixes fresh_H :: "num \<Rightarrow> hyp \<Rightarrow> o"

  assumes fresh_T_def:
    "fresh_T k t :=
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
       else False"
  assumes fresh_F_def: "fresh_F k f := fresh_T k (cpx (load_F f)) \<and> fresh_T k (cpy (load_F f))"
  assumes fresh_H_def: "fresh_H k G := if G = Nil then True else fresh_F k (list_hd G) \<and> fresh_H k (list_tl G)"
  (* AXIOMS *)
  (*Habeas Quid for the Encoder *)
  assumes pack_F_N: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> pack_F t L N"
  assumes tag_F_N:  "f N \<Longrightarrow> tag_F f N"
  assumes load_F_N: "f N \<Longrightarrow> load_F f N"

  assumes pack_T_N: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> (pack_T t L) N"
  assumes tag_T_N:  "t N \<Longrightarrow> tag_T t N"
  assumes load_T_N: "t N \<Longrightarrow> load_T t N"

  (*Injective *)
  assumes tag_pack_F:  "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> tag_F (pack_F t L) = t"
  assumes load_pack_F: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> load_F (pack_F t L) = L"
  
  assumes tag_pack_T:  "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> tag_T (pack_T t L) = t"
  assumes load_pack_T: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> load_T (pack_T t L) = L"

  (*Surjective *)
  assumes pack_tag_F:  "f N \<Longrightarrow> pack_F (tag_F f) (load_F f) = f"
  assumes pack_tag_T:  "t N \<Longrightarrow> pack_T (tag_T t) (load_T t) = t"

  (*Structural Decrease (For Induction) *)
  (* This will require load of atomic terms(without arguments) to return 0 *)
  assumes decrease_F: "\<lbrakk>f N; f \<noteq> 0 \<rbrakk> \<Longrightarrow> load_F f < f = 1"
  assumes decrease_T: "\<lbrakk>t N; t \<noteq> 0\<rbrakk> \<Longrightarrow> load_T t < t = 1"

  assumes tag_T_zero: "tag_T 0 = T_ZERO"

  (*Monotone assumptions for Bounding *)
  assumes mono_pack_T: "\<lbrakk>tg N; x N; y N; x \<le> y = 1\<rbrakk> \<Longrightarrow> (pack_T tg x \<le> pack_T tg y = 1)"
  assumes mono_pack_F: "\<lbrakk>tg N; x N; y N; x \<le> y = 1\<rbrakk> \<Longrightarrow> (pack_F tg x \<le> pack_F tg y = 1)"
begin

lemma fresh_T_bool [auto]:
  assumes k: "k N"
      and t: "t N"
  shows "fresh_T k t B"
proof (rule strong_induction[where a=t])
  show "t N"
    using t .
next
  show "fresh_T k 0 B"
    apply (rule defE[OF fresh_T_def[where k=k and t=0]])
    apply (simp add: tag_T_zero)
    done
next
  fix w
  assume w: "w N"
     and IH: "\<And>z. z N \<Longrightarrow> z \<le> w = 1 \<Longrightarrow> fresh_T k z B"
  have swN: "S w N"
    using w by simp
  have swnz: "S w \<noteq> 0"
    by (rule sucNonZero[OF w])
  have L: "load_T (S w) N"
    by (rule load_T_N[OF swN])
  have Lw: "load_T (S w) \<le> w = 1"
    by (rule le_suc_implies_leq[OF decrease_T[OF swN swnz] L w])
  have cxL: "cpx (load_T (S w)) N"
    using L by simp
  have cyL: "cpy (load_T (S w)) N"
    using L by simp
  have cxLw: "cpx (load_T (S w)) \<le> w = 1"
    by (rule leq_trans[OF cxL L w cpx_mono[OF L] Lw])
  have cyLw: "cpy (load_T (S w)) \<le> w = 1"
    by (rule leq_trans[OF cyL L w cpy_mono[OF L] Lw])
  have cxcyL: "cpx (cpy (load_T (S w))) N"
    using cyL by simp
  have cycyL: "cpy (cpy (load_T (S w))) N"
    using cyL by simp
  have cxcyLw: "cpx (cpy (load_T (S w))) \<le> w = 1"
    by (rule leq_trans[OF cxcyL cyL w cpx_mono[OF cyL] cyLw])
  have cycyLw: "cpy (cpy (load_T (S w))) \<le> w = 1"
    by (rule leq_trans[OF cycyL cyL w cpy_mono[OF cyL] cyLw])
  have r0: "fresh_T k (load_T (S w)) B"
    by (rule IH[OF L Lw])
  have r1: "fresh_T k (cpx (load_T (S w))) B"
    by (rule IH[OF cxL cxLw])
  have r2: "fresh_T k (cpx (cpy (load_T (S w)))) B"
    by (rule IH[OF cxcyL cxcyLw])
  have r3: "fresh_T k (cpy (cpy (load_T (S w)))) B"
    by (rule IH[OF cycyL cycyLw])
  have tgN: "tag_T (S w) N"
    by (rule tag_T_N[OF swN])
  have gVAR: "(tag_T (S w) = T_VAR) B"
    by (rule eqBool[OF tgN], simp)
  have gZERO: "(tag_T (S w) = T_ZERO) B"
    by (rule eqBool[OF tgN], simp)
  have gSUC: "(tag_T (S w) = T_SUC) B"
    by (rule eqBool[OF tgN], simp)
  have gPRED: "(tag_T (S w) = T_PRED) B"
    by (rule eqBool[OF tgN], simp)
  have gIFZ: "(tag_T (S w) = T_IFZ) B"
    by (rule eqBool[OF tgN], simp)
  have gAPP: "(tag_T (S w) = T_APP) B"
    by (rule eqBool[OF tgN], simp)
  have oneN: "(1::num) N"
    by simp
  have ltN: "load_T (S w) < k N"
    by (rule less_terminates[OF L k])
  have varB: "(load_T (S w) < k = 1) B"
    by (rule eqBool[OF ltN oneN])
  have ifzB:
    "(fresh_T k (cpx (load_T (S w))) \<and>
      fresh_T k (cpx (cpy (load_T (S w)))) \<and>
      fresh_T k (cpy (cpy (load_T (S w))))) B"
    using r1 r2 r3 by auto
  have appB:
    "(fresh_T k (cpx (cpy (load_T (S w)))) \<and>
      fresh_T k (cpy (cpy (load_T (S w))))) B"
    using r2 r3 by auto
  show "fresh_T k (S w) B"
    apply (rule defE[OF fresh_T_def[where k=k and t="S w"]])
    apply (rule condTB[OF gVAR varB])
    apply (rule condTB[OF gZERO true_bool])
    apply (rule condTB[OF gSUC r0])
    apply (rule condTB[OF gPRED r0])
    apply (rule condTB[OF gIFZ ifzB])
    apply (rule condTB[OF gAPP appB false_bool])
    done
qed

lemma fresh_F_bool [auto]:
  assumes k: "k N" and f: "f N"
  shows "fresh_F k f B"
proof -
  have L: "load_F f N"
    by (rule load_F_N[OF f])
  have l: "cpx (load_F f) N"
    by (rule cpx_terminates[OF L])
  have r: "cpy (load_F f) N"
    by (rule cpy_terminates[OF L])
  have fl: "fresh_T k (cpx (load_F f)) B"
    by (rule fresh_T_bool[OF k l])
  have fr: "fresh_T k (cpy (load_F f)) B"
    by (rule fresh_T_bool[OF k r])
  show ?thesis
    apply (rule defE[OF fresh_F_def[where k=k and f=f]])
    using fl fr by auto
qed

lemma fresh_H_bool [auto]:
  assumes k: "k N" and G: "G N"
  shows "fresh_H k G B"
proof (rule list_induct[OF G])
  show "fresh_H k Nil B"
    apply (rule defE[OF fresh_H_def[where k=k and G=Nil]])
    apply simp
    done
next
  fix h t
  assume h: "h N" and t: "t N" and IH: "fresh_H k t B"
  have ht: "h \<triangleright> t N"
    using h t by simp
  have nilB: "(h \<triangleright> t = Nil) B"
    by (rule eqBool[OF ht nil_nat])
  have fh: "fresh_F k h B"
    by (rule fresh_F_bool[OF k h])
  have conjB: "(fresh_F k h \<and> fresh_H k t) B"
    using fh IH by auto
  show "fresh_H k (h \<triangleright> t) B"
    apply (rule defE[OF fresh_H_def[where k=k and G="h \<triangleright> t"]])
    apply (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
    apply (rule condTB[OF nilB true_bool conjB])
    done
qed

end

locale bga_dfns = bga_bijective_encoding + 
  fixes dfns :: "dfn"
  fixes dfn_is :: "dfn \<Rightarrow> num \<Rightarrow> tm \<Rightarrow> o"
  assumes dfns_N: "dfns N"
  (* lazy range check instea of direct conjunction which makes it kind of awkward to work with *)
  assumes dfn_is_def: "dfn_is d k b := if d < len dfns = 1 then nth d dfns = b \<and> fresh_T k b else False"
begin
lemma dfn_is_bool [auto]:
  assumes d: "d N"
      and k: "k N"
      and b: "b N"
  shows "dfn_is d k b B"
proof -
  have ldN: "len dfns N"
    by (rule len_nat[OF dfns_N])
  have oneN: "(1::num) N"
    by simp
  have ltN: "d < len dfns N"
    by (rule less_terminates[OF d ldN])
  have rangeB: "(d < len dfns = 1) B"
    by (rule eqBool[OF ltN oneN])
  show "dfn_is d k b B"
  proof (rule defE[OF dfn_is_def[where d=d and k=k and b=b]])
    show "(if d < len dfns = 1 then  nth d dfns = b \<and> fresh_T k b  else False) B"
    proof (rule condTB'[OF rangeB])
      assume dr: "d < len dfns = 1"
      have nthN: "nth d dfns N"
        using dfns_N dr
        by (rule nth_in_range_N)
      have eqB: "(nth d dfns = b) B"
        by (rule eqBool[OF nthN b])
      have freshB: "fresh_T k b B"
        by (rule fresh_T_bool[OF k b])
      show "(nth d dfns = b \<and> fresh_T k b) B"
        using eqB freshB by auto
    next
      assume "\<not> d < len dfns = 1"
      show "False B"
        by (rule false_bool)
    qed
  qed
qed

end

locale bga_fuel_semantics = bga_dfns +
  fixes eval_fuel :: "num \<Rightarrow> tm \<Rightarrow> asn \<Rightarrow> val"
  assumes eval_fuel_def: "eval_fuel k t A :=
    if k = 0 then 0
    else if tag_T t = T_VAR then S (nth (load_T t) A)
    else if tag_T t = T_ZERO then S 0
    else if tag_T t = T_SUC then
      if eval_fuel (P k) (load_T t) A = 0 then 0
      else S (S (P (eval_fuel (P k) (load_T t) A)))
    else if tag_T t = T_PRED then
      if eval_fuel (P k) (load_T t) A = 0 then 0
      else S (P (P (eval_fuel (P k) (load_T t) A)))
    else if tag_T t = T_IFZ then
      if eval_fuel (P k) (hyp_of (load_T t)) A = 0 then 0
      else if P (eval_fuel (P k) (hyp_of (load_T t)) A) = 0
      then eval_fuel (P k) (hyp_of (conc_of (load_T t))) A
      else eval_fuel (P k) (conc_of (conc_of (load_T t))) A
    else
      if eval_fuel (P k) (hyp_of (conc_of (load_T t))) A = 0 then 0
      else if eval_fuel (P k) (conc_of (conc_of (load_T t))) A = 0 then 0
      else eval_fuel (P k) (nth (hyp_of (load_T t)) dfns)
        (P (eval_fuel (P k) (hyp_of (conc_of (load_T t))) A) \<triangleright>
         P (eval_fuel (P k) (conc_of (conc_of (load_T t))) A) \<triangleright> Nil)"
begin

lemma eval_fuel_zero [simp]: "eval_fuel 0 t A = 0"
proof -
  show ?thesis
    apply (rule defE[OF eval_fuel_def[where k=0 and t=t and A=A]])
    apply (rule condI1Eq[where d=0])
    apply (rule zeroRefl)
    apply (rule nat0)
    apply (rule zeroRefl)
    done
qed

definition eval_fuel_body :: "num \<Rightarrow> tm \<Rightarrow> asn \<Rightarrow> val" where
  "eval_fuel_body k t A \<equiv>
    if tag_T t = T_VAR then S (nth (load_T t) A)
    else if tag_T t = T_ZERO then S 0
    else if tag_T t = T_SUC then
      if eval_fuel k (load_T t) A = 0 then 0
      else S (S (P (eval_fuel k (load_T t) A)))
    else if tag_T t = T_PRED then
      if eval_fuel k (load_T t) A = 0 then 0
      else S (P (P (eval_fuel k (load_T t) A)))
    else if tag_T t = T_IFZ then
      if eval_fuel k (cpx (load_T t)) A = 0 then 0
      else if P (eval_fuel k (cpx (load_T t)) A) = 0 then eval_fuel k (cpx (cpy (load_T t))) A
      else eval_fuel k (cpy (cpy (load_T t))) A
    else
      if eval_fuel k (cpx (cpy (load_T t))) A = 0 then 0
      else if eval_fuel k (cpy (cpy (load_T t))) A = 0 then 0
      else eval_fuel k (nth (cpx (load_T t)) dfns)
        (P (eval_fuel k (cpx (cpy (load_T t))) A) \<triangleright> P (eval_fuel k (cpy (cpy (load_T t))) A) \<triangleright> Nil)"

lemma eval_fuel_def_body: "eval_fuel k t A := if k = 0 then 0 else eval_fuel_body (P k) t A"
  unfolding eval_fuel_body_def
  by (rule eval_fuel_def)

lemma eval_fuel_sucI:
  assumes kN: "k N" and H: "Q (eval_fuel_body k t A)"
  shows "Q (eval_fuel (S k) t A)"
proof -
  have nz: "\<not> S k = 0"
    using kN apply simp
    done
  have pk: "P (S k) = k"
    by (rule predSucInv[OF kN])
  show ?thesis
    apply (rule defE[OF eval_fuel_def_body[where k="S k" and t=t and A=A]])
    apply (rule cond_elseQ_I[where Q=Q, OF nz])
    using pk H by simp
qed

lemma eval_fuel_sucD:
  assumes k: "k N" and H: "Q (eval_fuel (S k) t A)"
  shows "Q (eval_fuel_body k t A)"
proof -
  have nz: "\<not> S k = 0"
    using k apply simp
    done
  have pk: "P (S k) = k"
    by (rule predSucInv[OF k])
  have body: "Q (eval_fuel_body (P (S k)) t A)"
    using defI[where Q=Q, OF eval_fuel_def_body[where k="S k" and t=t and A=A] H]
    by (rule cond_elseQ_E[OF nz])
  show ?thesis
    using pk body by simp
qed

lemma eval_fuel_suc_eq:
  assumes k: "k N" and bodyN: "eval_fuel_body k t A N"
  shows "eval_fuel (S k) t A = eval_fuel_body k t A"
proof -
  have refl: "eval_fuel_body k t A = eval_fuel_body k t A"
    using bodyN by simp
  show ?thesis
    by (rule eval_fuel_sucI[where Q="\<lambda>z. z = eval_fuel_body k t A", OF k refl])
qed

lemma eval_fuel_var:
  assumes k: "k N" and tg: "tag_T t = T_VAR" and nthN: "nth (load_T t) A N"
  shows "eval_fuel (S k) t A = S (nth (load_T t) A)"
proof -
  have rhsN: "S (nth (load_T t) A) N"
    by (rule natS[OF nthN])
  have refl: "S (nth (load_T t) A) = S (nth (load_T t) A)"
    using rhsN by simp
  have body: "eval_fuel_body k t A = S (nth (load_T t) A)"
    unfolding eval_fuel_body_def
    by (rule condI1Eq[OF tg rhsN refl])
  show ?thesis
    by (rule eval_fuel_sucI[where Q="\<lambda>z. z = S (nth (load_T t) A)", OF k body])
qed

lemma eval_fuel_zero_step:
  assumes k: "k N" and tg: "tag_T t = T_ZERO"
  shows "eval_fuel (S k) t A = S 0"
proof -
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have rhsN: "S 0 N"
    by simp
  have refl: "S 0 = S 0"
    using rhsN by simp
  have body: "eval_fuel_body k t A = S 0"
    unfolding eval_fuel_body_def
    apply (rule condI2Eq[OF nvar rhsN])
    apply (rule condI1Eq[OF tg rhsN refl])
    done
  show ?thesis
    by (rule eval_fuel_sucI[where Q="\<lambda>z. z = S 0", OF k body])
qed

lemma eval_fuel_suc_timeout:
  assumes k: "k N" and tg: "tag_T t = T_SUC" and child: "eval_fuel k (load_T t) A = 0"
  shows "eval_fuel (S k) t A = 0"
proof -
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have body: "eval_fuel_body k t A = 0"
    unfolding eval_fuel_body_def
    apply (rule condI2Eq[OF nvar nat0])
    apply (rule condI2Eq[OF nzero nat0])
    apply (rule condI1Eq[OF tg nat0])
    apply (rule condI1Eq[OF child nat0 zeroRefl])
    done
  show ?thesis
    by (rule eval_fuel_sucI[where Q="\<lambda>z. z = 0", OF k body])
qed

lemma eval_fuel_suc_value:
  assumes k: "k N" and tg: "tag_T t = T_SUC" and child: "eval_fuel k (load_T t) A = S r"
  shows "eval_fuel (S k) t A = S (S r)"
proof -
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have srN: "S r N"
    by (rule eq_impl_term2[OF child])
  have rN: "r N"
    by (rule natSI[OF srN])
  have srnz: "\<not> S r = 0"
    using rN by simp
  have childnz: "\<not> eval_fuel k (load_T t) A = 0"
    by (rule eqSubst[where a="S r" and b="eval_fuel k (load_T t) A" and Q="\<lambda>z. \<not> z = 0", OF eqSym[OF child] srnz])
  have predChild0: "P (eval_fuel k (load_T t) A) = P (S r)"
    by (rule predCong[OF child])
  have predChild: "P (eval_fuel k (load_T t) A) = r"
    using predChild0 predSucInv[OF rN] by (rule eq_trans)
  have sucPredChild: "S (P (eval_fuel k (load_T t) A)) = S r"
    by (rule sucCong[OF predChild])
  have branch: "S (S (P (eval_fuel k (load_T t) A))) = S (S r)"
    by (rule sucCong[OF sucPredChild])
  have rhsN: "S (S r) N"
    by (rule natS[OF srN])
  have body: "eval_fuel_body k t A = S (S r)"
    unfolding eval_fuel_body_def
    apply (rule condI2Eq[OF nvar rhsN])
    apply (rule condI2Eq[OF nzero rhsN])
    apply (rule condI1Eq[OF tg rhsN])
    apply (rule condI2Eq[OF childnz rhsN branch])
    done
  show ?thesis
    by (rule eval_fuel_sucI[where Q="\<lambda>z. z = S (S r)", OF k body])
qed

lemma eval_fuel_pred_timeout:
  assumes k: "k N" and tg: "tag_T t = T_PRED" and child: "eval_fuel k (load_T t) A = 0"
  shows "eval_fuel (S k) t A = 0"
proof -
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have body: "eval_fuel_body k t A = 0"
    unfolding eval_fuel_body_def
    apply (rule condI2Eq[OF nvar nat0])
    apply (rule condI2Eq[OF nzero nat0])
    apply (rule condI2Eq[OF nsuc nat0])
    apply (rule condI1Eq[OF tg nat0])
    apply (rule condI1Eq[OF child nat0 zeroRefl])
    done
  show ?thesis
    by (rule eval_fuel_sucI[where Q="\<lambda>z. z = 0", OF k body])
qed

lemma eval_fuel_pred_value:
  assumes k: "k N" and tg: "tag_T t = T_PRED" and child: "eval_fuel k (load_T t) A = S r"
  shows "eval_fuel (S k) t A = S (P r)"
proof -
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have srN: "S r N"
    by (rule eq_impl_term2[OF child])
  have rN: "r N"
    by (rule natSI[OF srN])
  have srnz: "\<not> S r = 0"
    using rN by simp
  have childnz: "\<not> eval_fuel k (load_T t) A = 0"
    by (rule eqSubst[where a="S r" and b="eval_fuel k (load_T t) A" and Q="\<lambda>z. \<not> z = 0", OF eqSym[OF child] srnz])
  have predChild0: "P (eval_fuel k (load_T t) A) = P (S r)"
    by (rule predCong[OF child])
  have predChild: "P (eval_fuel k (load_T t) A) = r"
    using predChild0 predSucInv[OF rN] by (rule eq_trans)
  have predPredChild: "P (P (eval_fuel k (load_T t) A)) = P r"
    by (rule predCong[OF predChild])
  have branch: "S (P (P (eval_fuel k (load_T t) A))) = S (P r)"
    by (rule sucCong[OF predPredChild])
  have rhsN: "S (P r) N"
    by (rule natS[OF natP[OF rN]])
  have body: "eval_fuel_body k t A = S (P r)"
    unfolding eval_fuel_body_def
    apply (rule condI2Eq[OF nvar rhsN])
    apply (rule condI2Eq[OF nzero rhsN])
    apply (rule condI2Eq[OF nsuc rhsN])
    apply (rule condI1Eq[OF tg rhsN])
    apply (rule condI2Eq[OF childnz rhsN branch])
    done
  show ?thesis
    by (rule eval_fuel_sucI[where Q="\<lambda>z. z = S (P r)", OF k body])
qed

lemma eval_fuel_ifz_cond_timeout:
  assumes k: "k N" and tg: "tag_T t = T_IFZ" and cond: "eval_fuel k (cpx (load_T t)) A = 0"
  shows "eval_fuel (S k) t A = 0"
proof -
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have npred: "\<not> tag_T t = T_PRED"
    using tg by simp
  have ifzBody: "(if eval_fuel k (cpx (load_T t)) A = 0 then 0 else if P (eval_fuel k (cpx (load_T t)) A) = 0 then eval_fuel k (cpx (cpy (load_T t))) A else eval_fuel k (cpy (cpy (load_T t))) A) = 0"
    by (rule condI1Eq[OF cond nat0 zeroRefl])
  have body: "eval_fuel_body k t A = 0"
    unfolding eval_fuel_body_def
    apply (rule condI2Eq[OF nvar nat0])
    apply (rule condI2Eq[OF nzero nat0])
    apply (rule condI2Eq[OF nsuc nat0])
    apply (rule condI2Eq[OF npred nat0])
    apply (rule condI1Eq[OF tg nat0 ifzBody])
    done
  show ?thesis
    by (rule eval_fuel_sucI[where Q="\<lambda>z. z = 0", OF k body])
qed

lemma eval_fuel_ifz_zero:
  assumes k: "k N" and tg: "tag_T t = T_IFZ"
      and cond: "eval_fuel k (cpx (load_T t)) A = S 0"
      and thenN: "eval_fuel k (cpx (cpy (load_T t))) A N"
  shows "eval_fuel (S k) t A = eval_fuel k (cpx (cpy (load_T t))) A"
proof -
  let ?c = "eval_fuel k (cpx (load_T t)) A"
  let ?a = "eval_fuel k (cpx (cpy (load_T t))) A"
  let ?b = "eval_fuel k (cpy (cpy (load_T t))) A"
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have npred: "\<not> tag_T t = T_PRED"
    using tg by simp
  have sucZeroNe: "\<not> S 0 = 0"
    by simp
  have condNe: "\<not> ?c = 0"
    by (rule eqSubst[where a="S 0" and b="?c" and Q="\<lambda>z. \<not> z = 0", OF eqSym[OF cond] sucZeroNe])
  have predCond0: "P ?c = P (S 0)"
    by (rule predCong[OF cond])
  have predCond: "P ?c = 0"
    using predCond0 predSucInv[OF nat0] by (rule eq_trans)
  have thenRefl: "?a = ?a"
    using thenN by simp
  have inner: "(if P ?c = 0 then ?a else ?b) = ?a"
    by (rule condI1Eq[OF predCond thenN thenRefl])
  have ifzBody: "(if ?c = 0 then 0 else if P ?c = 0 then ?a else ?b) = ?a"
    by (rule condI2Eq[OF condNe thenN inner])
  have body: "eval_fuel_body k t A = ?a"
    unfolding eval_fuel_body_def
    apply (rule condI2Eq[OF nvar thenN])
    apply (rule condI2Eq[OF nzero thenN])
    apply (rule condI2Eq[OF nsuc thenN])
    apply (rule condI2Eq[OF npred thenN])
    apply (rule condI1Eq[OF tg thenN ifzBody])
    done
  show ?thesis
    by (rule eval_fuel_sucI[where Q="\<lambda>z. z = ?a", OF k body])
qed

lemma eval_fuel_ifz_nonzero:
  assumes k: "k N" and tg: "tag_T t = T_IFZ"
      and cond: "eval_fuel k (cpx (load_T t)) A = S (S r)"
      and elseN: "eval_fuel k (cpy (cpy (load_T t))) A N"
  shows "eval_fuel (S k) t A = eval_fuel k (cpy (cpy (load_T t))) A"
proof -
  let ?c = "eval_fuel k (cpx (load_T t)) A"
  let ?a = "eval_fuel k (cpx (cpy (load_T t))) A"
  let ?b = "eval_fuel k (cpy (cpy (load_T t))) A"
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have npred: "\<not> tag_T t = T_PRED"
    using tg by simp
  have ssrN: "S (S r) N"
    by (rule eq_impl_term2[OF cond])
  have srN: "S r N"
    by (rule natSI[OF ssrN])
  have rN: "r N"
    by (rule natSI[OF srN])
  have ssrNe: "\<not> S (S r) = 0"
    using srN by simp
  have condNe: "\<not> ?c = 0"
    by (rule eqSubst[where a="S (S r)" and b="?c" and Q="\<lambda>z. \<not> z = 0", OF eqSym[OF cond] ssrNe])
  have predCond0: "P ?c = P (S (S r))"
    by (rule predCong[OF cond])
  have predCond: "P ?c = S r"
    using predCond0 predSucInv[OF srN] by (rule eq_trans)
  have srNe: "\<not> S r = 0"
    using rN by simp
  have predCondNe: "\<not> P ?c = 0"
    by (rule eqSubst[where a="S r" and b="P ?c" and Q="\<lambda>z. \<not> z = 0", OF eqSym[OF predCond] srNe])
  have elseRefl: "?b = ?b"
    using elseN by simp
  have inner: "(if P ?c = 0 then ?a else ?b) = ?b"
    by (rule condI2Eq[OF predCondNe elseN elseRefl])
  have ifzBody: "(if ?c = 0 then 0 else if P ?c = 0 then ?a else ?b) = ?b"
    by (rule condI2Eq[OF condNe elseN inner])
  have body: "eval_fuel_body k t A = ?b"
    unfolding eval_fuel_body_def
    apply (rule condI2Eq[OF nvar elseN])
    apply (rule condI2Eq[OF nzero elseN])
    apply (rule condI2Eq[OF nsuc elseN])
    apply (rule condI2Eq[OF npred elseN])
    apply (rule condI1Eq[OF tg elseN ifzBody])
    done
  show ?thesis
    by (rule eval_fuel_sucI[where Q="\<lambda>z. z = ?b", OF k body])
qed

lemma eval_fuel_ifz_zero_value:
  assumes k: "k N" and tg: "tag_T t = T_IFZ"
      and cond: "eval_fuel k (cpx (load_T t)) A = S 0"
      and branch: "eval_fuel k (cpx (cpy (load_T t))) A = S r"
  shows "eval_fuel (S k) t A = S r"
proof -
  have branchN: "eval_fuel k (cpx (cpy (load_T t))) A N"
    by (rule eq_impl_term[OF branch])
  have step: "eval_fuel (S k) t A = eval_fuel k (cpx (cpy (load_T t))) A"
    by (rule eval_fuel_ifz_zero[OF k tg cond branchN])
  show ?thesis
    using step branch by (rule eq_trans)
qed

lemma eval_fuel_ifz_nonzero_value:
  assumes k: "k N" and tg: "tag_T t = T_IFZ"
      and cond: "eval_fuel k (cpx (load_T t)) A = S (S q)"
      and branch: "eval_fuel k (cpy (cpy (load_T t))) A = S r"
  shows "eval_fuel (S k) t A = S r"
proof -
  have branchN: "eval_fuel k (cpy (cpy (load_T t))) A N"
    by (rule eq_impl_term[OF branch])
  have step: "eval_fuel (S k) t A = eval_fuel k (cpy (cpy (load_T t))) A"
    by (rule eval_fuel_ifz_nonzero[OF k tg cond branchN])
  show ?thesis
    using step branch by (rule eq_trans)
qed

lemma eval_fuel_app_arg1_timeout:
  assumes k: "k N" and nvar: "\<not> tag_T t = T_VAR"
    and nzero: "\<not> tag_T t = T_ZERO" and nsuc: "\<not> tag_T t = T_SUC"
    and npred: "\<not> tag_T t = T_PRED" and nifz: "\<not> tag_T t = T_IFZ"
    and arg1: "eval_fuel k (cpx (cpy (load_T t))) A = 0"
  shows "eval_fuel (S k) t A = 0"
proof -
  have appBody: "(if eval_fuel k (cpx (cpy (load_T t))) A = 0 then 0 else if eval_fuel k (cpy (cpy (load_T t))) A = 0 then 0 else eval_fuel k (nth (cpx (load_T t)) dfns) (P (eval_fuel k (cpx (cpy (load_T t))) A) \<triangleright> (P (eval_fuel k (cpy (cpy (load_T t))) A) \<triangleright> Nil))) = 0"
    by (rule condI1Eq[OF arg1 nat0 zeroRefl])
  have body: "eval_fuel_body k t A = 0"
    unfolding eval_fuel_body_def
    apply (rule condI2Eq[OF nvar nat0])
    apply (rule condI2Eq[OF nzero nat0])
    apply (rule condI2Eq[OF nsuc nat0])
    apply (rule condI2Eq[OF npred nat0])
    apply (rule condI2Eq[OF nifz nat0])
    apply (rule appBody)
    done
  show ?thesis
    by (rule eval_fuel_sucI[where Q="\<lambda>z. z = 0", OF k body])
qed

lemma eval_fuel_app_arg2_timeout:
  assumes k: "k N" and nvar: "\<not> tag_T t = T_VAR"
    and nzero: "\<not> tag_T t = T_ZERO" and nsuc: "\<not> tag_T t = T_SUC"
    and npred: "\<not> tag_T t = T_PRED" and nifz: "\<not> tag_T t = T_IFZ"
    and arg1: "eval_fuel k (cpx (cpy (load_T t))) A = S x"
    and arg2: "eval_fuel k (cpy (cpy (load_T t))) A = 0"
  shows "eval_fuel (S k) t A = 0"
proof -
  let ?a1 = "eval_fuel k (cpx (cpy (load_T t))) A"
  let ?a2 = "eval_fuel k (cpy (cpy (load_T t))) A"
  have sxN: "S x N"
    by (rule eq_impl_term2[OF arg1])
  have xN: "x N"
    by (rule natSI[OF sxN])
  have sxNe: "\<not> S x = 0"
    using xN by simp
  have arg1Ne: "\<not> ?a1 = 0"
    by (rule eqSubst[where a="S x" and b="?a1" and Q="\<lambda>z. \<not> z = 0", OF eqSym[OF arg1] sxNe])
  have inner: "(if ?a2 = 0 then 0 else eval_fuel k (nth (cpx (load_T t)) dfns) (P ?a1 \<triangleright> (P ?a2 \<triangleright> Nil))) = 0"
    by (rule condI1Eq[OF arg2 nat0 zeroRefl])
  have appBody: "(if ?a1 = 0 then 0 else if ?a2 = 0 then 0 else eval_fuel k (nth (cpx (load_T t)) dfns) (P ?a1 \<triangleright> (P ?a2 \<triangleright> Nil))) = 0"
    by (rule condI2Eq[OF arg1Ne nat0 inner])
  have body: "eval_fuel_body k t A = 0"
    unfolding eval_fuel_body_def
    apply (rule condI2Eq[OF nvar nat0])
    apply (rule condI2Eq[OF nzero nat0])
    apply (rule condI2Eq[OF nsuc nat0])
    apply (rule condI2Eq[OF npred nat0])
    apply (rule condI2Eq[OF nifz nat0])
    apply (rule appBody)
    done
  show ?thesis
    by (rule eval_fuel_sucI[where Q="\<lambda>z. z = 0", OF k body])
qed

lemma eval_fuel_app_body:
  assumes k: "k N" and nvar: "\<not> tag_T t = T_VAR"
    and nzero: "\<not> tag_T t = T_ZERO" and nsuc: "\<not> tag_T t = T_SUC"
    and npred: "\<not> tag_T t = T_PRED" and nifz: "\<not> tag_T t = T_IFZ"
    and arg1: "eval_fuel k (cpx (cpy (load_T t))) A = S x"
    and arg2: "eval_fuel k (cpy (cpy (load_T t))) A = S y"
    and bodyN: "eval_fuel k (nth (cpx (load_T t)) dfns) (x \<triangleright> (y \<triangleright> Nil)) N"
  shows "eval_fuel (S k) t A = eval_fuel k (nth (cpx (load_T t)) dfns) (x \<triangleright> (y \<triangleright> Nil))"
proof -
  let ?a1 = "eval_fuel k (cpx (cpy (load_T t))) A"
  let ?a2 = "eval_fuel k (cpy (cpy (load_T t))) A"
  let ?body = "eval_fuel k (nth (cpx (load_T t)) dfns) (x \<triangleright> (y \<triangleright> Nil))"
  let ?rawBody = "eval_fuel k (nth (cpx (load_T t)) dfns) (P ?a1 \<triangleright> (P ?a2 \<triangleright> Nil))"
  have sxN: "S x N"
    by (rule eq_impl_term2[OF arg1])
  have syN: "S y N"
    by (rule eq_impl_term2[OF arg2])
  have xN: "x N"
    by (rule natSI[OF sxN])
  have yN: "y N"
    by (rule natSI[OF syN])
  have sxNe: "\<not> S x = 0"
    using xN by simp
  have syNe: "\<not> S y = 0"
    using yN by simp
  have arg1Ne: "\<not> ?a1 = 0"
    by (rule eqSubst[where a="S x" and b="?a1" and Q="\<lambda>z. \<not> z = 0", OF eqSym[OF arg1] sxNe])
  have arg2Ne: "\<not> ?a2 = 0"
    by (rule eqSubst[where a="S y" and b="?a2" and Q="\<lambda>z. \<not> z = 0", OF eqSym[OF arg2] syNe])
  have predArg1Raw: "P ?a1 = P (S x)"
    by (rule predCong[OF arg1])
  have predArg1: "P ?a1 = x"
    using predArg1Raw predSucInv[OF xN] by (rule eq_trans)
  have predArg2Raw: "P ?a2 = P (S y)"
    by (rule predCong[OF arg2])
  have predArg2: "P ?a2 = y"
    using predArg2Raw predSucInv[OF yN] by (rule eq_trans)
  have bodyRefl: "?body = ?body"
    using bodyN by simp
  have replaceY: "eval_fuel k (nth (cpx (load_T t)) dfns) (x \<triangleright> (P ?a2 \<triangleright> Nil)) = ?body"
    by (rule eqSubst[where a=y and b="P ?a2" and Q="\<lambda>z. eval_fuel k (nth (cpx (load_T t)) dfns) (x \<triangleright> (z \<triangleright> Nil)) = ?body", OF eqSym[OF predArg2] bodyRefl])
  have rawBody: "?rawBody = ?body"
    by (rule eqSubst[where a=x and b="P ?a1" and Q="\<lambda>z. eval_fuel k (nth (cpx (load_T t)) dfns) (z \<triangleright> (P ?a2 \<triangleright> Nil)) = ?body", OF eqSym[OF predArg1] replaceY])
  have inner: "(if ?a2 = 0 then 0 else ?rawBody) = ?body"
    by (rule condI2Eq[OF arg2Ne bodyN rawBody])
  have appBody: "(if ?a1 = 0 then 0 else if ?a2 = 0 then 0 else ?rawBody) = ?body"
    by (rule condI2Eq[OF arg1Ne bodyN inner])
  have body: "eval_fuel_body k t A = ?body"
    unfolding eval_fuel_body_def
    apply (rule condI2Eq[OF nvar bodyN])
    apply (rule condI2Eq[OF nzero bodyN])
    apply (rule condI2Eq[OF nsuc bodyN])
    apply (rule condI2Eq[OF npred bodyN])
    apply (rule condI2Eq[OF nifz bodyN])
    apply (rule appBody)
    done
  show ?thesis
    by (rule eval_fuel_sucI[where Q="\<lambda>z. z = ?body", OF k body])
qed

lemma eval_fuel_app_body_timeout:
  assumes k: "k N" and nvar: "\<not> tag_T t = T_VAR"
    and nzero: "\<not> tag_T t = T_ZERO" and nsuc: "\<not> tag_T t = T_SUC"
    and npred: "\<not> tag_T t = T_PRED" and nifz: "\<not> tag_T t = T_IFZ"
    and arg1: "eval_fuel k (cpx (cpy (load_T t))) A = S x"
    and arg2: "eval_fuel k (cpy (cpy (load_T t))) A = S y"
    and body: "eval_fuel k (nth (cpx (load_T t)) dfns) (x \<triangleright> (y \<triangleright> Nil)) = 0"
  shows "eval_fuel (S k) t A = 0"
proof -
  have bodyN: "eval_fuel k (nth (cpx (load_T t)) dfns) (x \<triangleright> (y \<triangleright> Nil)) N"
    by (rule eq_impl_term[OF body])
  have step: "eval_fuel (S k) t A = eval_fuel k (nth (cpx (load_T t)) dfns) (x \<triangleright> (y \<triangleright> Nil))"
    by (rule eval_fuel_app_body[OF k nvar nzero nsuc npred nifz arg1 arg2 bodyN])
  show ?thesis
    using step body by (rule eq_trans)
qed

lemma eval_fuel_app_value:
  assumes k: "k N" and nvar: "\<not> tag_T t = T_VAR"
    and nzero: "\<not> tag_T t = T_ZERO" and nsuc: "\<not> tag_T t = T_SUC"
    and npred: "\<not> tag_T t = T_PRED" and nifz: "\<not> tag_T t = T_IFZ"
    and arg1: "eval_fuel k (cpx (cpy (load_T t))) A = S x"
    and arg2: "eval_fuel k (cpy (cpy (load_T t))) A = S y"
    and body: "eval_fuel k (nth (cpx (load_T t)) dfns) (x \<triangleright> (y \<triangleright> Nil)) = S r"
  shows "eval_fuel (S k) t A = S r"
proof -
  have bodyN: "eval_fuel k (nth (cpx (load_T t)) dfns) (x \<triangleright> (y \<triangleright> Nil)) N"
    by (rule eq_impl_term[OF body])
  have step: "eval_fuel (S k) t A = eval_fuel k (nth (cpx (load_T t)) dfns) (x \<triangleright> (y \<triangleright> Nil))"
    by (rule eval_fuel_app_body[OF k nvar nzero nsuc npred nifz arg1 arg2 bodyN])
  show ?thesis
    using step body by (rule eq_trans)
qed


lemma nth_suc_cons:
  assumes k: "k N" and h: "h N" and t: "t N" and nk: "nth k t N"
  shows "nth (S k) (h \<triangleright> t) = nth k t"
proof -
  have ne: "\<not> h \<triangleright> t = Nil" using h t by simp
  have nz: "\<not> S k = 0" using k by simp
  have sk1: "S k - 1 = k" using k by simp
  have tl: "list_tl (h \<triangleright> t) = t" using h t by simp
  have deep: "nth (S k - 1) (list_tl (h \<triangleright> t)) = nth k t" using sk1 tl nk by simp
  have inner: "(if S k = 0 then list_hd (h \<triangleright> t) else nth (S k - 1) (list_tl (h \<triangleright> t))) = nth k t"
    using nz nk deep by (rule condI2Eq)
  show ?thesis
    by (rule defE[OF nth_def[where i="S k" and xs="h \<triangleright> t"]], rule condI2Eq[OF ne nk inner])
qed

text \<open>With the totalised nth (out-of-range yields 0 rather
  than omega), "nth i Nil" reduces to 0 and nth
  is everywhere grounded.\<close>
lemma nth_nil: "nth i Nil = 0"
  apply (rule defE[OF nth_def[where i=i and xs=Nil]])
  apply (rule condI1Eq[where d=0])
  apply (rule nil_nat[unfolded isNat_def])
  apply (rule nat0)
  apply (rule nat0[unfolded isNat_def])
  done

lemma nth_N:
  assumes xs: "xs N"
  shows "\<forall>i. nth i xs N"
proof (rule list_induct[OF xs])
  show "\<forall>i. nth i Nil N"
  proof (rule forallI)
    fix i assume iN: "i N"
    show "nth i Nil N"
      using eqSym[OF nth_nil] nat0 by (rule eqSubst[where Q="\<lambda>z. z N"])
  qed
next
  fix h t
  assume h: "h N" and t: "t N" and IH: "\<forall>i. nth i t N"
  show "\<forall>i. nth i (h \<triangleright> t) N"
  proof (rule forallI)
    fix i assume iN: "i N"
    show "nth i (h \<triangleright> t) N"
    proof (rule cases_nat_2[where x=i])
      show "i N" by (rule iN)
    next
      assume "i = 0"
      show "nth 0 (h \<triangleright> t) N"
        using eqSym[OF nth_zero_cons[OF h t]] h
        by (rule eqSubst[where Q="\<lambda>z. z N"])
    next
      fix k assume k: "k N" and ik: "i = S k"
      have nkt: "nth k t N" by (rule forallE[OF IH k])
      have red: "nth (S k) (h \<triangleright> t) = nth k t" by (rule nth_suc_cons[OF k h t nkt])
      show "nth (S k) (h \<triangleright> t) N"
        using eqSym[OF red] nkt by (rule eqSubst[where Q="\<lambda>z. z N"])
    qed
  qed
qed

lemma nth_N':
  assumes xs: "xs N" and i: "i N"
  shows "nth i xs N"
  by (rule forallE[OF nth_N[OF xs] i])

lemma eval_fuel_N:
  assumes k: "k N" and t: "t N" and A: "A N"
  shows "eval_fuel k t A N"
proof -
  have main: "\<forall>u. \<forall>A2 . eval_fuel k u A2 N"
  proof (rule ind[OF k])
    show "\<forall>u. \<forall>A2 . eval_fuel 0 u A2 N"
    proof (rule forallI)
      fix u
      assume u: "u N"
      show "\<forall>A2 . eval_fuel 0 u A2 N"
      proof (rule forallI)
        fix A2
        assume B: "A2 N"
        have z: "eval_fuel 0 u A2 = 0"
          by (rule eval_fuel_zero)
        show "eval_fuel 0 u A2 N"
          using eqSym[OF z] nat0 by (rule eqSubst[where Q="\<lambda>v. v N"])
      qed
    qed
  next
    fix n
    assume n: "n N" and IH: "\<forall>u. \<forall>A2 . eval_fuel n u A2 N"
    show "\<forall>u. \<forall>A2 . eval_fuel (S n) u A2 N"
    proof (rule forallI)
      fix u
      assume u: "u N"
      show "\<forall>A2 . eval_fuel (S n) u A2 N"
      proof (rule forallI)
        fix A2
        assume B: "A2 N"
        have loadN: "load_T u N"
          by (rule load_T_N[OF u])
        have headLoadN: "cpx (load_T u) N"
          by (rule cpx_terminates[OF loadN])
        have tailLoadN: "cpy (load_T u) N"
          by (rule cpy_terminates[OF loadN])
        have headTailN: "cpx (cpy (load_T u)) N"
          by (rule cpx_terminates[OF tailLoadN])
        have tailTailN: "cpy (cpy (load_T u)) N"
          by (rule cpy_terminates[OF tailLoadN])
        have IHload: "\<forall>C. eval_fuel n (load_T u) C N"
          by (rule forallE[where a="load_T u", OF IH loadN])
        have loadEvalN: "eval_fuel n (load_T u) A2 N"
          by (rule forallE[where a=A2, OF IHload B])
        have IHheadLoad: "\<forall>C. eval_fuel n (cpx (load_T u)) C N"
          by (rule forallE[where a="cpx (load_T u)", OF IH headLoadN])
        have headLoadEvalN: "eval_fuel n (cpx (load_T u)) A2 N"
          by (rule forallE[where a=A2, OF IHheadLoad B])
        have IHheadTail: "\<forall>C. eval_fuel n (cpx (cpy (load_T u))) C N"
          by (rule forallE[where a="cpx (cpy (load_T u))", OF IH headTailN])
        have headTailEvalN: "eval_fuel n (cpx (cpy (load_T u))) A2 N"
          by (rule forallE[where a=A2, OF IHheadTail B])
        have IHtailTail: "\<forall>C. eval_fuel n (cpy (cpy (load_T u))) C N"
          by (rule forallE[where a="cpy (cpy (load_T u))", OF IH tailTailN])
        have tailTailEvalN: "eval_fuel n (cpy (cpy (load_T u))) A2 N"
          by (rule forallE[where a=A2, OF IHtailTail B])
        have dfnBodyN: "nth (cpx (load_T u)) dfns N"
          by (rule nth_N'[OF dfns_N headLoadN])
        have leftValueN: "P (eval_fuel n (cpx (cpy (load_T u))) A2) N"
          by (rule natP[OF headTailEvalN])
        have rightValueN: "P (eval_fuel n (cpy (cpy (load_T u))) A2) N"
          by (rule natP[OF tailTailEvalN])
        have appAsnN: "P (eval_fuel n (cpx (cpy (load_T u))) A2) \<triangleright> P (eval_fuel n (cpy (cpy (load_T u))) A2) \<triangleright> Nil N"
          using leftValueN rightValueN by simp
        have IHbody: "\<forall>C. eval_fuel n (nth (cpx (load_T u)) dfns) C N"
          by (rule forallE[where a="nth (cpx (load_T u)) dfns", OF IH dfnBodyN])
        have bodyEvalN: "eval_fuel n (nth (cpx (load_T u)) dfns) (P (eval_fuel n (cpx (cpy (load_T u))) A2) \<triangleright> P (eval_fuel n (cpy (cpy (load_T u))) A2) \<triangleright> Nil) N"
          by (rule forallE[where a="P (eval_fuel n (cpx (cpy (load_T u))) A2) \<triangleright> P (eval_fuel n (cpy (cpy (load_T u))) A2) \<triangleright> Nil", OF IHbody appAsnN])
        have nthEvalN: "nth (load_T u) A2 N"
          by (rule nth_N'[OF B loadN])
        have varValueN: "S (nth (load_T u) A2) N"
          by (rule natS[OF nthEvalN])
        have zeroValueN: "S 0 N"
          by simp
        have loadZeroA2: "(eval_fuel n (load_T u) A2 = 0) B"
          by (rule eqBool[OF loadEvalN nat0])
        have predLoadN: "P (eval_fuel n (load_T u) A2) N"
          by (rule natP[OF loadEvalN])
        have sucSucPredLoadN: "S (S (P (eval_fuel n (load_T u) A2))) N"
          using predLoadN by simp
        have sucA2ranchN: "(if eval_fuel n (load_T u) A2 = 0 then 0 else S (S (P (eval_fuel n (load_T u) A2)))) N"
          by (rule condT[OF loadZeroA2 nat0 sucSucPredLoadN])
        have predPredLoadN: "P (P (eval_fuel n (load_T u) A2)) N"
          by (rule natP[OF predLoadN])
        have sucPredPredLoadN: "S (P (P (eval_fuel n (load_T u) A2))) N"
          by (rule natS[OF predPredLoadN])
        have predA2ranchN: "(if eval_fuel n (load_T u) A2 = 0 then 0 else S (P (P (eval_fuel n (load_T u) A2)))) N"
          by (rule condT[OF loadZeroA2 nat0 sucPredPredLoadN])
        have condZeroA2: "(eval_fuel n (cpx (load_T u)) A2 = 0) B"
          by (rule eqBool[OF headLoadEvalN nat0])
        have predCondN: "P (eval_fuel n (cpx (load_T u)) A2) N"
          by (rule natP[OF headLoadEvalN])
        have predCondZeroA2: "(P (eval_fuel n (cpx (load_T u)) A2) = 0) B"
          by (rule eqBool[OF predCondN nat0])
        have ifzInnerN: "(if P (eval_fuel n (cpx (load_T u)) A2) = 0 then eval_fuel n (cpx (cpy (load_T u))) A2 else eval_fuel n (cpy (cpy (load_T u))) A2) N"
          by (rule condT[OF predCondZeroA2 headTailEvalN tailTailEvalN])
        have ifzA2ranchN: "(if eval_fuel n (cpx (load_T u)) A2 = 0 then 0 else if P (eval_fuel n (cpx (load_T u)) A2) = 0 then eval_fuel n (cpx (cpy (load_T u))) A2 else eval_fuel n (cpy (cpy (load_T u))) A2) N"
          by (rule condT[OF condZeroA2 nat0 ifzInnerN])
        have leftZeroA2: "(eval_fuel n (cpx (cpy (load_T u))) A2 = 0) B"
          by (rule eqBool[OF headTailEvalN nat0])
        have rightZeroA2: "(eval_fuel n (cpy (cpy (load_T u))) A2 = 0) B"
          by (rule eqBool[OF tailTailEvalN nat0])
        have appInnerN: "(if eval_fuel n (cpy (cpy (load_T u))) A2 = 0 then 0 else eval_fuel n (nth (cpx (load_T u)) dfns) (P (eval_fuel n (cpx (cpy (load_T u))) A2) \<triangleright> P (eval_fuel n (cpy (cpy (load_T u))) A2) \<triangleright> Nil)) N"
          by (rule condT[OF rightZeroA2 nat0 bodyEvalN])
        have appA2ranchN: "(if eval_fuel n (cpx (cpy (load_T u))) A2 = 0 then 0 else if eval_fuel n (cpy (cpy (load_T u))) A2 = 0 then 0 else eval_fuel n (nth (cpx (load_T u)) dfns) (P (eval_fuel n (cpx (cpy (load_T u))) A2) \<triangleright> P (eval_fuel n (cpy (cpy (load_T u))) A2) \<triangleright> Nil)) N"
          by (rule condT[OF leftZeroA2 nat0 appInnerN])
        have tagN: "tag_T u N"
          by (rule tag_T_N[OF u])
        have varA2: "(tag_T u = T_VAR) B"
          by (rule eqBool[OF tagN], simp)
        have zeroA2: "(tag_T u = T_ZERO) B"
          by (rule eqBool[OF tagN], simp)
        have sucA2: "(tag_T u = T_SUC) B"
          by (rule eqBool[OF tagN], simp)
        have predA2: "(tag_T u = T_PRED) B"
          by (rule eqBool[OF tagN], simp)
        have ifzA2: "(tag_T u = T_IFZ) B"
          by (rule eqBool[OF tagN], simp)
        have bodyN: "eval_fuel_body n u A2 N"
          unfolding eval_fuel_body_def
          apply (rule condT[OF varA2 varValueN])
          apply (rule condT[OF zeroA2 zeroValueN])
          apply (rule condT[OF sucA2 sucA2ranchN])
          apply (rule condT[OF predA2 predA2ranchN])
          apply (rule condT[OF ifzA2 ifzA2ranchN])
          apply (rule appA2ranchN)
          done
        show "eval_fuel (S n) u A2 N"
          by (rule eval_fuel_sucI[where Q="\<lambda>v. v N", OF n bodyN])
      qed
    qed
  qed
  have allA: "\<forall>A2 . eval_fuel k t A2 N"
    by (rule forallE[where a=t, OF main t])
  show ?thesis
    by (rule forallE[where a=A, OF allA A])
qed

lemma eval_fuel_zero_bool:
  assumes k: "k N" and t: "t N" and A: "A N"
  shows "(eval_fuel k t A = 0) B"
  by (rule eqBool[OF eval_fuel_N[OF k t A] nat0])

lemma eval_fuel_result_N:
  assumes k: "k N" and t: "t N" and A: "A N" and result: "eval_fuel k t A = S r"
  shows "r N"
proof -
  have srN: "S r N"
    by (rule eq_impl_term2[OF result])
  show ?thesis
    by (rule natSI[OF srN])
qed

lemma zero_successE:
  assumes timeout: "v = 0" and success: "v = S r"
  shows Q
proof -
  have srN: "S r N"
    by (rule eq_impl_term2[OF success])
  have rN: "r N"
    by (rule natSI[OF srN])
  have eq: "0 = S r"
    using eqSym[OF timeout] success by (rule eq_trans)
  have neq: "\<not> 0 = S r"
    using rN by simp
  show Q
    by (rule exF[OF eq neq])
qed

lemma same_success:
  assumes left: "v = S x" and right: "v = S y"
  shows "S x = S y"
  using eqSym[OF left] right by (rule eq_trans)

lemma eval_fuel_success_suc:
  assumes k: "k N" and t: "t N" and A: "A N" and result: "eval_fuel k t A = S r"
  shows "eval_fuel (S k) t A = S r"
proof -
  have main: "\<forall>u. \<forall>A2. \<forall>q. (eval_fuel k u A2 = S q) \<longrightarrow> eval_fuel (S k) u A2 = S q"
  proof (rule ind[OF k])
    show "\<forall>u. \<forall>A2. \<forall>q. (eval_fuel 0 u A2 = S q) \<longrightarrow> eval_fuel (S 0) u A2 = S q"
    proof (rule forallI)
      fix u
      assume u: "u N"
      show "\<forall>A2. \<forall>q. (eval_fuel 0 u A2 = S q) \<longrightarrow> eval_fuel (S 0) u A2 = S q"
      proof (rule forallI)
        fix A2
        assume A2: "A2 N"
        show "\<forall>q. (eval_fuel 0 u A2 = S q) \<longrightarrow> eval_fuel (S 0) u A2 = S q"
        proof (rule forallI)
          fix q
          assume q: "q N"
          show "(eval_fuel 0 u A2 = S q) \<longrightarrow> eval_fuel (S 0) u A2 = S q"
          proof (rule implI)
            have evalN: "eval_fuel 0 u A2 N"
              by (rule eval_fuel_N[OF nat0 u A2])
            have sqN: "S q N"
              by (rule natS[OF q])
            show "(eval_fuel 0 u A2 = S q) B"
              by (rule eqBool[OF evalN sqN])
          next
            assume success: "eval_fuel 0 u A2 = S q"
            have timeout: "eval_fuel 0 u A2 = 0"
              by (rule eval_fuel_zero)
            show "eval_fuel (S 0) u A2 = S q"
              by (rule zero_successE[OF timeout success])
          qed
        qed
      qed
    qed
  next
    fix n
    assume n: "n N"
    assume IH: "\<forall>u. \<forall>A2. \<forall>q. (eval_fuel n u A2 = S q) \<longrightarrow> eval_fuel (S n) u A2 = S q"
    show "\<forall>u. \<forall>A2. \<forall>q. (eval_fuel (S n) u A2 = S q) \<longrightarrow> eval_fuel (S (S n)) u A2 = S q"
    proof (rule forallI)
      fix u
      assume u: "u N"
      show "\<forall>A2. \<forall>q. (eval_fuel (S n) u A2 = S q) \<longrightarrow> eval_fuel (S (S n)) u A2 = S q"
      proof (rule forallI)
        fix A2
        assume A2: "A2 N"
        show "\<forall>q. (eval_fuel (S n) u A2 = S q) \<longrightarrow> eval_fuel (S (S n)) u A2 = S q"
        proof (rule forallI)
          fix q
          assume q: "q N"
          show "(eval_fuel (S n) u A2 = S q) \<longrightarrow> eval_fuel (S (S n)) u A2 = S q"
          proof (rule implI)
            have sn: "S n N"
              by (rule natS[OF n])
            have evalN: "eval_fuel (S n) u A2 N"
              by (rule eval_fuel_N[OF sn u A2])
            have sqN: "S q N"
              by (rule natS[OF q])
            show "(eval_fuel (S n) u A2 = S q) B"
              by (rule eqBool[OF evalN sqN])
          next
            assume result: "eval_fuel (S n) u A2 = S q"
            have sn: "S n N"
              by (rule natS[OF n])
            have IHmeta: "\<And>v A3 z. v N \<Longrightarrow> A3 N \<Longrightarrow> eval_fuel n v A3 = S z \<Longrightarrow> eval_fuel (S n) v A3 = S z"
            proof -
              fix v A3 z
              assume v: "v N" and A3: "A3 N" and success: "eval_fuel n v A3 = S z"
              have z: "z N"
                by (rule eval_fuel_result_N[OF n v A3 success])
              have IHv: "\<forall>A3. \<forall>z. (eval_fuel n v A3 = S z) \<longrightarrow> eval_fuel (S n) v A3 = S z"
                by (rule forallE[where a=v, OF IH v])
              have IHva: "\<forall>z. (eval_fuel n v A3 = S z) \<longrightarrow> eval_fuel (S n) v A3 = S z"
                by (rule forallE[where a=A3, OF IHv A3])
              have IHvaz: "(eval_fuel n v A3 = S z) \<longrightarrow> eval_fuel (S n) v A3 = S z"
                by (rule forallE[where a=z, OF IHva z])
              show "eval_fuel (S n) v A3 = S z"
                using IHvaz success by (rule implE)
            qed
            have loadN: "load_T u N"
              by (rule load_T_N[OF u])
            have condTermN: "cpx (load_T u) N"
              by (rule cpx_terminates[OF loadN])
            have tailN: "cpy (load_T u) N"
              by (rule cpy_terminates[OF loadN])
            have leftTermN: "cpx (cpy (load_T u)) N"
              by (rule cpx_terminates[OF tailN])
            have rightTermN: "cpy (cpy (load_T u)) N"
              by (rule cpy_terminates[OF tailN])
            have tagN: "tag_T u N"
              by (rule tag_T_N[OF u])
            have varB: "(tag_T u = T_VAR) B"
              by (rule eqBool[OF tagN], simp)
            have zeroB: "(tag_T u = T_ZERO) B"
              by (rule eqBool[OF tagN], simp)
            have sucB: "(tag_T u = T_SUC) B"
              by (rule eqBool[OF tagN], simp)
            have predB: "(tag_T u = T_PRED) B"
              by (rule eqBool[OF tagN], simp)
            have ifzB: "(tag_T u = T_IFZ) B"
              by (rule eqBool[OF tagN], simp)
            show "eval_fuel (S (S n)) u A2 = S q"
            proof (rule cases_bool[where q="tag_T u = T_VAR"])
              show "(tag_T u = T_VAR) B"
                by (rule varB)
            next
              assume tg: "tag_T u = T_VAR"
              have nthN: "nth (load_T u) A2 N"
                by (rule nth_N'[OF A2 loadN])
              have old: "eval_fuel (S n) u A2 = S (nth (load_T u) A2)"
                by (rule eval_fuel_var[OF n tg nthN])
              have new: "eval_fuel (S (S n)) u A2 = S (nth (load_T u) A2)"
                by (rule eval_fuel_var[OF sn tg nthN])
              have same: "S (nth (load_T u) A2) = S q"
                by (rule same_success[OF old result])
              show "eval_fuel (S (S n)) u A2 = S q"
                using new same by (rule eq_trans)
            next
              assume nvar: "\<not> tag_T u = T_VAR"
              show "eval_fuel (S (S n)) u A2 = S q"
              proof (rule cases_bool[where q="tag_T u = T_ZERO"])
                show "(tag_T u = T_ZERO) B"
                  by (rule zeroB)
              next
                assume tg: "tag_T u = T_ZERO"
                have old: "eval_fuel (S n) u A2 = S 0"
                  by (rule eval_fuel_zero_step[OF n tg])
                have new: "eval_fuel (S (S n)) u A2 = S 0"
                  by (rule eval_fuel_zero_step[OF sn tg])
                have same: "S 0 = S q"
                  by (rule same_success[OF old result])
                show "eval_fuel (S (S n)) u A2 = S q"
                  using new same by (rule eq_trans)
              next
                assume nzero: "\<not> tag_T u = T_ZERO"
                show "eval_fuel (S (S n)) u A2 = S q"
                proof (rule cases_bool[where q="tag_T u = T_SUC"])
                  show "(tag_T u = T_SUC) B"
                    by (rule sucB)
                next
                  assume tg: "tag_T u = T_SUC"
                  have childN: "eval_fuel n (load_T u) A2 N"
                    by (rule eval_fuel_N[OF n loadN A2])
                  show "eval_fuel (S (S n)) u A2 = S q"
                  proof (rule cases_nat_2[where x="eval_fuel n (load_T u) A2"])
                    show "eval_fuel n (load_T u) A2 N"
                      by (rule childN)
                  next
                    assume child: "eval_fuel n (load_T u) A2 = 0"
                    have timeout: "eval_fuel (S n) u A2 = 0"
                      by (rule eval_fuel_suc_timeout[OF n tg child])
                    show "eval_fuel (S (S n)) u A2 = S q"
                      by (rule zero_successE[OF timeout result])
                  next
                    fix v
                    assume v: "v N" and child: "eval_fuel n (load_T u) A2 = S v"
                    have old: "eval_fuel (S n) u A2 = S (S v)"
                      by (rule eval_fuel_suc_value[OF n tg child])
                    have childUp: "eval_fuel (S n) (load_T u) A2 = S v"
                      by (rule IHmeta[OF loadN A2 child])
                    have new: "eval_fuel (S (S n)) u A2 = S (S v)"
                      by (rule eval_fuel_suc_value[OF sn tg childUp])
                    have same: "S (S v) = S q"
                      by (rule same_success[OF old result])
                    show "eval_fuel (S (S n)) u A2 = S q"
                      using new same by (rule eq_trans)
                  qed
                next
                  assume nsuc: "\<not> tag_T u = T_SUC"
                  show "eval_fuel (S (S n)) u A2 = S q"
                  proof (rule cases_bool[where q="tag_T u = T_PRED"])
                    show "(tag_T u = T_PRED) B"
                      by (rule predB)
                  next
                    assume tg: "tag_T u = T_PRED"
                    have childN: "eval_fuel n (load_T u) A2 N"
                      by (rule eval_fuel_N[OF n loadN A2])
                    show "eval_fuel (S (S n)) u A2 = S q"
                    proof (rule cases_nat_2[where x="eval_fuel n (load_T u) A2"])
                      show "eval_fuel n (load_T u) A2 N"
                        by (rule childN)
                    next
                      assume child: "eval_fuel n (load_T u) A2 = 0"
                      have timeout: "eval_fuel (S n) u A2 = 0"
                        by (rule eval_fuel_pred_timeout[OF n tg child])
                      show "eval_fuel (S (S n)) u A2 = S q"
                        by (rule zero_successE[OF timeout result])
                    next
                      fix v
                      assume v: "v N" and child: "eval_fuel n (load_T u) A2 = S v"
                      have old: "eval_fuel (S n) u A2 = S (P v)"
                        by (rule eval_fuel_pred_value[OF n tg child])
                      have childUp: "eval_fuel (S n) (load_T u) A2 = S v"
                        by (rule IHmeta[OF loadN A2 child])
                      have new: "eval_fuel (S (S n)) u A2 = S (P v)"
                        by (rule eval_fuel_pred_value[OF sn tg childUp])
                      have same: "S (P v) = S q"
                        by (rule same_success[OF old result])
                      show "eval_fuel (S (S n)) u A2 = S q"
                        using new same by (rule eq_trans)
                    qed
                  next
                    assume npred: "\<not> tag_T u = T_PRED"
                    show "eval_fuel (S (S n)) u A2 = S q"
                    proof (rule cases_bool[where q="tag_T u = T_IFZ"])
                      show "(tag_T u = T_IFZ) B"
                        by (rule ifzB)
                    next
                      assume tg: "tag_T u = T_IFZ"
                      have condEvalN: "eval_fuel n (cpx (load_T u)) A2 N"
                        by (rule eval_fuel_N[OF n condTermN A2])
                      show "eval_fuel (S (S n)) u A2 = S q"
                      proof (rule cases_nat_2[where x="eval_fuel n (cpx (load_T u)) A2"])
                        show "eval_fuel n (cpx (load_T u)) A2 N"
                          by (rule condEvalN)
                      next
                        assume cond: "eval_fuel n (cpx (load_T u)) A2 = 0"
                        have timeout: "eval_fuel (S n) u A2 = 0"
                          by (rule eval_fuel_ifz_cond_timeout[OF n tg cond])
                        show "eval_fuel (S (S n)) u A2 = S q"
                          by (rule zero_successE[OF timeout result])
                      next
                        fix c
                        assume c: "c N" and cond: "eval_fuel n (cpx (load_T u)) A2 = S c"
                        show "eval_fuel (S (S n)) u A2 = S q"
                        proof (rule cases_nat_2[where x=c])
                          show "c N"
                            by (rule c)
                        next
                          assume cz: "c = 0"
                          have scz: "S c = S 0"
                            by (rule sucCong[OF cz])
                          have condZero: "eval_fuel n (cpx (load_T u)) A2 = S 0"
                            using cond scz by (rule eq_trans)
                          have branchN: "eval_fuel n (cpx (cpy (load_T u))) A2 N"
                            by (rule eval_fuel_N[OF n leftTermN A2])
                          show "eval_fuel (S (S n)) u A2 = S q"
                          proof (rule cases_nat_2[where x="eval_fuel n (cpx (cpy (load_T u))) A2"])
                            show "eval_fuel n (cpx (cpy (load_T u))) A2 N"
                              by (rule branchN)
                          next
                            assume branch: "eval_fuel n (cpx (cpy (load_T u))) A2 = 0"
                            have step: "eval_fuel (S n) u A2 = eval_fuel n (cpx (cpy (load_T u))) A2"
                              by (rule eval_fuel_ifz_zero[OF n tg condZero branchN])
                            have timeout: "eval_fuel (S n) u A2 = 0"
                              using step branch by (rule eq_trans)
                            show "eval_fuel (S (S n)) u A2 = S q"
                              by (rule zero_successE[OF timeout result])
                          next
                            fix v
                            assume v: "v N" and branch: "eval_fuel n (cpx (cpy (load_T u))) A2 = S v"
                            have old: "eval_fuel (S n) u A2 = S v"
                              by (rule eval_fuel_ifz_zero_value[OF n tg condZero branch])
                            have condUp: "eval_fuel (S n) (cpx (load_T u)) A2 = S 0"
                              by (rule IHmeta[OF condTermN A2 condZero])
                            have branchUp: "eval_fuel (S n) (cpx (cpy (load_T u))) A2 = S v"
                              by (rule IHmeta[OF leftTermN A2 branch])
                            have new: "eval_fuel (S (S n)) u A2 = S v"
                              by (rule eval_fuel_ifz_zero_value[OF sn tg condUp branchUp])
                            have same: "S v = S q"
                              by (rule same_success[OF old result])
                            show "eval_fuel (S (S n)) u A2 = S q"
                              using new same by (rule eq_trans)
                          qed
                        next
                          fix d
                          assume d: "d N" and cnz: "c = S d"
                          have scnz: "S c = S (S d)"
                            by (rule sucCong[OF cnz])
                          have condNonzero: "eval_fuel n (cpx (load_T u)) A2 = S (S d)"
                            using cond scnz by (rule eq_trans)
                          have branchN: "eval_fuel n (cpy (cpy (load_T u))) A2 N"
                            by (rule eval_fuel_N[OF n rightTermN A2])
                          show "eval_fuel (S (S n)) u A2 = S q"
                          proof (rule cases_nat_2[where x="eval_fuel n (cpy (cpy (load_T u))) A2"])
                            show "eval_fuel n (cpy (cpy (load_T u))) A2 N"
                              by (rule branchN)
                          next
                            assume branch: "eval_fuel n (cpy (cpy (load_T u))) A2 = 0"
                            have step: "eval_fuel (S n) u A2 = eval_fuel n (cpy (cpy (load_T u))) A2"
                              by (rule eval_fuel_ifz_nonzero[OF n tg condNonzero branchN])
                            have timeout: "eval_fuel (S n) u A2 = 0"
                              using step branch by (rule eq_trans)
                            show "eval_fuel (S (S n)) u A2 = S q"
                              by (rule zero_successE[OF timeout result])
                          next
                            fix v
                            assume v: "v N" and branch: "eval_fuel n (cpy (cpy (load_T u))) A2 = S v"
                            have old: "eval_fuel (S n) u A2 = S v"
                              by (rule eval_fuel_ifz_nonzero_value[OF n tg condNonzero branch])
                            have condUp: "eval_fuel (S n) (cpx (load_T u)) A2 = S (S d)"
                              by (rule IHmeta[OF condTermN A2 condNonzero])
                            have branchUp: "eval_fuel (S n) (cpy (cpy (load_T u))) A2 = S v"
                              by (rule IHmeta[OF rightTermN A2 branch])
                            have new: "eval_fuel (S (S n)) u A2 = S v"
                              by (rule eval_fuel_ifz_nonzero_value[OF sn tg condUp branchUp])
                            have same: "S v = S q"
                              by (rule same_success[OF old result])
                            show "eval_fuel (S (S n)) u A2 = S q"
                              using new same by (rule eq_trans)
                          qed
                        qed
                      qed
                    next
                      assume nifz: "\<not> tag_T u = T_IFZ"
                      have arg1N: "eval_fuel n (cpx (cpy (load_T u))) A2 N"
                        by (rule eval_fuel_N[OF n leftTermN A2])
                      show "eval_fuel (S (S n)) u A2 = S q"
                      proof (rule cases_nat_2[where x="eval_fuel n (cpx (cpy (load_T u))) A2"])
                        show "eval_fuel n (cpx (cpy (load_T u))) A2 N"
                          by (rule arg1N)
                      next
                        assume arg1: "eval_fuel n (cpx (cpy (load_T u))) A2 = 0"
                        have timeout: "eval_fuel (S n) u A2 = 0"
                          by (rule eval_fuel_app_arg1_timeout[OF n nvar nzero nsuc npred nifz arg1])
                        show "eval_fuel (S (S n)) u A2 = S q"
                          by (rule zero_successE[OF timeout result])
                      next
                        fix x
                        assume x: "x N" and arg1: "eval_fuel n (cpx (cpy (load_T u))) A2 = S x"
                        have arg2N: "eval_fuel n (cpy (cpy (load_T u))) A2 N"
                          by (rule eval_fuel_N[OF n rightTermN A2])
                        show "eval_fuel (S (S n)) u A2 = S q"
                        proof (rule cases_nat_2[where x="eval_fuel n (cpy (cpy (load_T u))) A2"])
                          show "eval_fuel n (cpy (cpy (load_T u))) A2 N"
                            by (rule arg2N)
                        next
                          assume arg2: "eval_fuel n (cpy (cpy (load_T u))) A2 = 0"
                          have timeout: "eval_fuel (S n) u A2 = 0"
                            by (rule eval_fuel_app_arg2_timeout[OF n nvar nzero nsuc npred nifz arg1 arg2])
                          show "eval_fuel (S (S n)) u A2 = S q"
                            by (rule zero_successE[OF timeout result])
                        next
                          fix y
                          assume y: "y N" and arg2: "eval_fuel n (cpy (cpy (load_T u))) A2 = S y"
                          have dfnN: "nth (cpx (load_T u)) dfns N"
                            by (rule nth_N'[OF dfns_N condTermN])
                          have appAsnN: "x \<triangleright> y \<triangleright> Nil N"
                            using x y by simp
                          have bodyN: "eval_fuel n (nth (cpx (load_T u)) dfns) (x \<triangleright> y \<triangleright> Nil) N"
                            by (rule eval_fuel_N[OF n dfnN appAsnN])
                          show "eval_fuel (S (S n)) u A2 = S q"
                          proof (rule cases_nat_2[where x="eval_fuel n (nth (cpx (load_T u)) dfns) (x \<triangleright> y \<triangleright> Nil)"])
                            show "eval_fuel n (nth (cpx (load_T u)) dfns) (x \<triangleright> y \<triangleright> Nil) N"
                              by (rule bodyN)
                          next
                            assume body: "eval_fuel n (nth (cpx (load_T u)) dfns) (x \<triangleright> y \<triangleright> Nil) = 0"
                            have timeout: "eval_fuel (S n) u A2 = 0"
                              by (rule eval_fuel_app_body_timeout[OF n nvar nzero nsuc npred nifz arg1 arg2 body])
                            show "eval_fuel (S (S n)) u A2 = S q"
                              by (rule zero_successE[OF timeout result])
                          next
                            fix v
                            assume v: "v N" and body: "eval_fuel n (nth (cpx (load_T u)) dfns) (x \<triangleright> y \<triangleright> Nil) = S v"
                            have old: "eval_fuel (S n) u A2 = S v"
                              by (rule eval_fuel_app_value[OF n nvar nzero nsuc npred nifz arg1 arg2 body])
                            have arg1Up: "eval_fuel (S n) (cpx (cpy (load_T u))) A2 = S x"
                              by (rule IHmeta[OF leftTermN A2 arg1])
                            have arg2Up: "eval_fuel (S n) (cpy (cpy (load_T u))) A2 = S y"
                              by (rule IHmeta[OF rightTermN A2 arg2])
                            have bodyUp: "eval_fuel (S n) (nth (cpx (load_T u)) dfns) (x \<triangleright> y \<triangleright> Nil) = S v"
                              by (rule IHmeta[OF dfnN appAsnN body])
                            have new: "eval_fuel (S (S n)) u A2 = S v"
                              by (rule eval_fuel_app_value[OF sn nvar nzero nsuc npred nifz arg1Up arg2Up bodyUp])
                            have same: "S v = S q"
                              by (rule same_success[OF old result])
                            show "eval_fuel (S (S n)) u A2 = S q"
                              using new same by (rule eq_trans)
                          qed
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  have r: "r N"
    by (rule eval_fuel_result_N[OF k t A result])
  have mainT: "\<forall>A2. \<forall>q. (eval_fuel k t A2 = S q) \<longrightarrow> eval_fuel (S k) t A2 = S q"
    by (rule forallE[where a=t, OF main t])
  have mainA: "\<forall>q. (eval_fuel k t A = S q) \<longrightarrow> eval_fuel (S k) t A = S q"
    by (rule forallE[where a=A, OF mainT A])
  have mainR: "(eval_fuel k t A = S r) \<longrightarrow> eval_fuel (S k) t A = S r"
    by (rule forallE[where a=r, OF mainA r])
  show ?thesis
    using mainR result by (rule implE)
qed

lemma eval_fuel_success_add:
  assumes k: "k N" and n: "n N" and t: "t N" and A: "A N" and result: "eval_fuel k t A = S r"
  shows "eval_fuel (k + n) t A = S r"
proof (rule ind[where a=n])
  show "n N"
    by (rule n)
  have k0: "k + 0 = k"
    by (rule add_zero[OF k])
  show "eval_fuel (k + 0) t A = S r"
    by (rule eqSubst[where a=k and b="k + 0" and Q="\<lambda>z. eval_fuel z t A = S r", OF eqSym[OF k0] result])
next
  fix x
  assume x: "x N" and IH: "eval_fuel (k + x) t A = S r"
  have kxN: "k + x N"
    by (rule add_terminates[OF k x])
  have step: "eval_fuel (S (k + x)) t A = S r"
    by (rule eval_fuel_success_suc[OF kxN t A IH])
  have addSuc: "k + S x = S (k + x)"
    by (rule add_succ[OF k x])
  show "eval_fuel (k + S x) t A = S r"
    by (rule eqSubst[where a="S (k + x)" and b="k + S x" and Q="\<lambda>z. eval_fuel z t A = S r", OF eqSym[OF addSuc] step])
qed

lemma eval_fuel_success_unique:
  assumes k: "k N" and l: "l N" and t: "t N" and A: "A N"
      and left: "eval_fuel k t A = S r" and right: "eval_fuel l t A = S q"
  shows "r = q"
proof -
  have leftUp: "eval_fuel (k + l) t A = S r"
    by (rule eval_fuel_success_add[OF k l t A left])
  have rightUp0: "eval_fuel (l + k) t A = S q"
    by (rule eval_fuel_success_add[OF l k t A right])
  have fuelEq: "l + k = k + l"
    by (rule add_comm[OF l k])
  have rightUp: "eval_fuel (k + l) t A = S q"
    by (rule eqSubst[where a="l + k" and b="k + l" and Q="\<lambda>z. eval_fuel z t A = S q", OF fuelEq rightUp0])
  have encodedEq: "S r = S q"
    by (rule same_success[OF leftUp rightUp])
  show ?thesis
    by (rule sucInj[OF encodedEq])
qed

lemma eval_fuel_success_unique_encoded:
  assumes k: "k N" and l: "l N" and t: "t N" and A: "A N"
      and left: "eval_fuel k t A = S r" and right: "eval_fuel l t A = S q"
  shows "S r = S q"
proof -
  have rq: "r = q"
    by (rule eval_fuel_success_unique[OF k l t A left right])
  show ?thesis
    by (rule sucCong[OF rq])
qed

definition evals :: "tm \<Rightarrow> asn \<Rightarrow> val \<Rightarrow> o" where
  "evals t A r \<equiv> \<exists>k. eval_fuel k t A = S r"

lemma evalsI:
  assumes k: "k N" and result: "eval_fuel k t A = S r"
  shows "evals t A r"
  unfolding evals_def
  using k result by (rule existsI)

lemma evalsE:
  assumes ev: "evals t A r" and step: "\<And>k. k N \<Longrightarrow> eval_fuel k t A = S r \<Longrightarrow> Q"
  shows Q
proof -
  have ex: "\<exists>k. eval_fuel k t A = S r"
    using ev unfolding evals_def .
  show Q
    using ex step by (rule existsE)
qed

lemma evals_result_N:
  assumes t: "t N" and A: "A N" and ev: "evals t A r"
  shows "r N"
proof -
  show ?thesis
    using ev
  proof (rule evalsE)
    fix k
    assume k: "k N" and result: "eval_fuel k t A = S r"
    show "r N"
      by (rule eval_fuel_result_N[OF k t A result])
  qed
qed

lemma evals_functional:
  assumes t: "t N" and A: "A N" and left: "evals t A r" and right: "evals t A q"
  shows "r = q"
proof -
  show ?thesis
    using left
  proof (rule evalsE)
    fix k
    assume k: "k N" and leftK: "eval_fuel k t A = S r"
    show "r = q"
      using right
    proof (rule evalsE)
      fix l
      assume l: "l N" and rightL: "eval_fuel l t A = S q"
      show "r = q"
        by (rule eval_fuel_success_unique[OF k l t A leftK rightL])
    qed
  qed
qed

lemma evals_fuel_unique:
  assumes k: "k N" and t: "t N" and A: "A N" and ev: "evals t A v" and run: "eval_fuel k t A = S r"
  shows "r = v"
proof -
  have runEv: "evals t A r"
    by (rule evalsI[OF k run])
  show ?thesis
    by (rule evals_functional[OF t A runEv ev])
qed

lemma evals_fuel_unique_encoded:
  assumes k: "k N" and t: "t N" and A: "A N" and ev: "evals t A v" and run: "eval_fuel k t A = S r"
  shows "S r = S v"
proof -
  have rv: "r = v"
    by (rule evals_fuel_unique[OF k t A ev run])
  show ?thesis
    by (rule sucCong[OF rv])
qed

end

locale bga_semantics = bga_dfns  +
  (* Semantics *)
  (* eval takes in a term, assignments and definition list
 and returns the valuation of that term*)
fixes eval :: "tm \<Rightarrow> asn \<Rightarrow> val"

  (*  Note that P does not diverge on 0 due to the implementation 
  of P in GD.thy not doing so*)
  (* We can write this definition very cleanly and without having to handle non-termination separately or use step counts as we are working in GA *)
(*
1. v_i \<Down> A(i)
2. 0 \<Down> 0
3. S(x) \<Down> S(eval(x))
4. P(x) \<Down> P(eval(x))
5. ifz a? b:c \<Down> (if eval(a)=0 then eval(b) else eval(c))
6. f_i (a, b) \<Down> eval(D(i)) for asn = \<langle>eval(a), eval(b)\<rangle>
*)
  assumes eval_def: "eval t A :=
    if tag_T t = T_VAR then nth (load_T t) A                          
    else if tag_T t = T_ZERO then 0                                    
    else if tag_T t = T_SUC then S(eval (load_T t) A)              
    else if tag_T t = T_PRED then P(eval (load_T t) A)               
    else if tag_T t = T_IFZ then                                     
      (if eval (cpx (load_T t)) A = 0 
         then eval (cpx (cpy (load_T t))) A
         else eval (cpy (cpy (load_T t))) A)
    else
      (if eval (cpx (cpy (load_T t))) A = eval (cpx (cpy (load_T t))) A
       then (if eval (cpy (cpy (load_T t))) A = eval (cpy (cpy (load_T t))) A
             then eval (nth (cpx (load_T t)) dfns)
                    ((eval (cpx (cpy (load_T t))) A)\<triangleright> ((eval (cpy (cpy (load_T t))) A) \<triangleright> Nil))
             else 0)
       else 0)"
begin
definition sat :: "num \<Rightarrow> num  \<Rightarrow> o" where
    "sat f A \<equiv> if tag_F f = 0 
               then eval (cpx (load_F f)) A = eval (cpy (load_F f)) A
               else eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A"

definition sat_hyp :: "hyp \<Rightarrow> asn \<Rightarrow> o" where
  "sat_hyp G A \<equiv> \<forall>f. (mem f G) \<longrightarrow> (sat f A)"
end

context bga_semantics 
begin 

lemma sat_hyp_nil': "sat_hyp Nil A"
  unfolding sat_hyp_def
  apply (rule forallI)
  apply (rule implI)
   apply simp
proof - 
  fix f
  assume f_nat: "f N"
  assume f_in_empty: "f \<in> \<emptyset>"
  show "sat f A"
    apply (rule exF[where P = "f \<in> \<emptyset>"])
     apply (rule f_in_empty)
    apply (rule mem_nil)
    done
qed

lemma sat_hyp_mem: "f N \<Longrightarrow> f \<in> G \<Longrightarrow> sat_hyp G A \<Longrightarrow> sat f A"
  unfolding sat_hyp_def
proof -
  assume f_nat: "f N" and f_in: "f \<in> G" and all: "\<forall>g. g \<in> G \<longrightarrow> sat g A"
  have imp: "f \<in> G \<longrightarrow> sat f A"
    apply (rule forallE[where a = f]) apply (rule all) apply (rule f_nat) done
  show "sat f A"
    apply (rule implE[where a = "f \<in> G"]) apply (rule imp) apply (rule f_in) done
qed

lemma sat_hyp_consI:
  assumes f: "f N"
      and G: "G N"
      and sf: "sat f A"
      and sG: "sat_hyp G A"
  shows "sat_hyp (f \<triangleright> G) A"
proof -
  show ?thesis
    unfolding sat_hyp_def
  proof (rule forallI)
    fix g
    assume g: "g N"
    show "g \<in> (f \<triangleright> G) \<longrightarrow> sat g A"
    proof (rule implI)
      show "g \<in> (f \<triangleright> G) B"
        by (rule mem_bool[OF g], use f G in simp)
    next
      assume mem: "g \<in> (f \<triangleright> G)"
      have split: "g \<in> (f \<triangleright> G) \<longleftrightarrow> (if f = g then True else g \<in> G)"
        by (rule mem_cons[OF f G g])
      have to_cond: "g \<in> (f \<triangleright> G) \<longrightarrow> (if f = g then True else g \<in> G)"
        by (rule iffE1[OF split])
      have cond: "if f = g then True else g \<in> G"
        by (rule implE[OF to_cond mem])
      show "sat g A"
      proof (rule cases_bool[where q="f = g"])
        show "(f = g) B"
          by (rule eqBool[OF f g])
      next
        assume fg: "f = g"
        show "sat g A"
          using fg sf
          by (rule eqSubst[where a=f and b=g])
      next
        assume fg: "\<not> f = g"
        have gG: "g \<in> G"
          using fg cond
          by (rule notcond_thenE)
        show "sat g A"
          using g gG sG
          by (rule sat_hyp_mem)
      qed
    qed
  qed
qed

lemma sat_hyp_subset: "subset G' G \<Longrightarrow> G' N \<Longrightarrow> G N \<Longrightarrow> sat_hyp G A \<Longrightarrow> sat_hyp G' A"
proof -
  assume sub: "subset G' G" and G'_nat: "G' N" and satG: "sat_hyp G A" and G_nat: "G N"
  show "sat_hyp G' A"
    unfolding sat_hyp_def
    apply (rule forallI)
    apply (rule implI)
     apply (simp add: G'_nat)
    apply (rule G'_nat)
  proof -
    fix f
    assume f_nat: "f N" and f_in': "f \<in> G'"
    have fG: "f \<in> G" using f_nat G'_nat G_nat sub f_in' by (rule subset_mem)
    show "sat f A" using f_nat fG satG by (rule sat_hyp_mem)
  qed
qed

lemma eval_zero [simp]:
  "eval (pack_T T_ZERO 0) A = 0"
proof -
  have z: "pack_T T_ZERO 0 N"
    by (rule pack_T_N[OF _ nat0], simp)
  have tg: "tag_T (pack_T T_ZERO 0) = T_ZERO"
    by (rule tag_pack_T[OF _ nat0], simp)
  show ?thesis
    apply (rule defE[OF eval_def[
      where t="pack_T T_ZERO 0" and A=A]])
    using tg z
    apply simp
    done
qed

lemma eval_suc [simp]:
  assumes t: "t N"
      and e: "eval t A N"
  shows "eval (pack_T T_SUC t) A = S (eval t A)"
proof -
  have tg: "tag_T (pack_T T_SUC t) = T_SUC"
    by (rule tag_pack_T[OF _ t], simp)
  have ld:
    "load_T (pack_T T_SUC t) = t"
    by (rule load_pack_T[OF _ t], simp)
  have tsN: "T_SUC N"
    by simp
  have rhsN: "S (eval t A) N"
    by (rule natS[OF e])
  show ?thesis
    apply (rule defE[OF eval_def[
      where t="pack_T T_SUC t" and A=A]])
    using tg ld tsN rhsN
    apply simp
    done
qed

end

locale bga_subst = bga_bijective_encoding +
  fixes subst_T        :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"
  (* subst_T t j v: Inside term 't', replace variable index 'j' with term 'v' *)
  assumes subst_T_def: "subst_T t j v := 
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
             (subst_T (cpy (cpy (load_T t))) j v)\<rangle>\<rangle>)"

    fixes subst_F        :: "fm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  (* subst_F f j v: Inside formula 'f', replace variable index 'j' with term 'v' *)
  assumes subst_F_def: "subst_F f j v :=
    if tag_F f = F_EQ then
      pack_F F_EQ \<langle>(subst_T (cpx (load_F f)) j v), (subst_T (cpy (load_F f)) j v)\<rangle>
    else
      pack_F F_NEQ \<langle>(subst_T (cpx (load_F f)) j v), (subst_T (cpy (load_F f)) j v)\<rangle>"

  fixes subst_body :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"    
  (* subst_body b x y  =  b[0\<mapsto>x, 1\<mapsto>y] simultaneously *)
  assumes subst_body_def: "subst_body b x y :=
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
                subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>"



locale bga_fuel_subst_semantics = bga_fuel_semantics + bga_subst +
  fixes asn_put :: "asn \<Rightarrow> num \<Rightarrow> val \<Rightarrow> asn"
  assumes asn_put_def: "asn_put A i v :=
    if i = 0 then
      if A = Nil then v \<triangleright> Nil else v \<triangleright> list_tl A
    else if A = Nil then 0 \<triangleright> asn_put Nil (i - 1) v
    else list_hd A \<triangleright> asn_put (list_tl A) (i - 1) v"
begin

lemma fresh_H_mem:
  assumes i: "i N" and G: "G N" and f: "f N"
      and fr: "fresh_H i G" and mm: "f \<in> G"
  shows "fresh_F i f"
proof -
  have main: "fresh_H i G \<longrightarrow> (f \<in> G \<longrightarrow> fresh_F i f)"
  proof (rule list_induct[OF G])
    show "fresh_H i Nil \<longrightarrow> (f \<in> Nil \<longrightarrow> fresh_F i f)"
    proof (rule implI)
      show "fresh_H i Nil B" by (rule fresh_H_bool[OF i nil_nat])
    next
      assume "fresh_H i Nil"
      show "f \<in> Nil \<longrightarrow> fresh_F i f"
      proof (rule implI)
        show "(f \<in> Nil) B" by (rule mem_bool[OF f nil_nat])
      next
        assume mn: "f \<in> Nil"
        show "fresh_F i f" by (rule exF[OF mn mem_nil])
      qed
    qed
  next
    fix h t
    assume h: "h N" and t: "t N"
       and IH: "fresh_H i t \<longrightarrow> (f \<in> t \<longrightarrow> fresh_F i f)"
    have ht: "h \<triangleright> t N" using h t by simp
    show "fresh_H i (h \<triangleright> t) \<longrightarrow> (f \<in> (h \<triangleright> t) \<longrightarrow> fresh_F i f)"
    proof (rule implI)
      show "fresh_H i (h \<triangleright> t) B" by (rule fresh_H_bool[OF i ht])
    next
      assume frht: "fresh_H i (h \<triangleright> t)"
      have ne: "\<not> (h \<triangleright> t = Nil)" using h t by simp
      have unf0: "if (h \<triangleright> t) = Nil then True
                    else fresh_F i (list_hd (h \<triangleright> t)) \<and> fresh_H i (list_tl (h \<triangleright> t))"
        using frht by (rule defI[OF fresh_H_def[where k=i and G="h \<triangleright> t"]])
      have conj0: "fresh_F i (list_hd (h \<triangleright> t)) \<and> fresh_H i (list_tl (h \<triangleright> t))"
        by (rule notcond_thenE[OF ne unf0])
      have frh: "fresh_F i h"
        using conjE1[OF conj0] by (simp only: list_hd_cons[OF h t])
      have frt: "fresh_H i t"
        using conjE2[OF conj0] by (simp only: list_tl_cons[OF h t])
      show "f \<in> (h \<triangleright> t) \<longrightarrow> fresh_F i f"
      proof (rule implI)
        show "(f \<in> (h \<triangleright> t)) B" by (rule mem_bool[OF f ht])
      next
        assume mm2: "f \<in> (h \<triangleright> t)"
        have split: "f \<in> (h \<triangleright> t) \<longleftrightarrow> (if h = f then True else f \<in> t)"
          by (rule mem_cons[OF h t f])
        have cond: "if h = f then True else f \<in> t"
          by (rule implE[OF iffE1[OF split] mm2])
        show "fresh_F i f"
        proof (rule cases_bool[where q="h = f"])
          show "(h = f) B" by (rule eqBool[OF h f])
        next
          assume hf: "h = f"
          show "fresh_F i f"
            using hf frh by (rule eqSubst[where Q="\<lambda>z. fresh_F i z"])
        next
          assume hf: "\<not> h = f"
          have ft: "f \<in> t" by (rule notcond_thenE[OF hf cond])
          have imp1: "f \<in> t \<longrightarrow> fresh_F i f" by (rule implE[OF IH frt])
          show "fresh_F i f" by (rule implE[OF imp1 ft])
        qed
      qed
    qed
  qed
  have imp1: "f \<in> G \<longrightarrow> fresh_F i f" by (rule implE[OF main fr])
  show "fresh_F i f" by (rule implE[OF imp1 mm])
qed

text \<open>These need A N (for a junk A the
  guard A = Nil is not grounded).\<close>

lemma asn_put_N:
  assumes A: "A N" and i: "i N" and v: "v N"
  shows "asn_put A i v N"
proof -
  have main: "\<forall>b. asn_put b i v N"
  proof (rule ind[OF i])
    show "\<forall>b. asn_put b 0 v N"
    proof (rule forallI)
      fix b assume B: "b N"
      show "asn_put b 0 v N"
      proof (rule cases_bool[where q = "b = Nil"])
        show "(b = Nil) B" by (rule eqBool[OF B nil_nat])
      next
        assume c: "b = Nil"
        have d: "v \<triangleright> Nil N" using v by simp
        have r: "asn_put b 0 v = v \<triangleright> Nil"
          apply (rule defE[OF asn_put_def[where A = b and i = 0 and v = v]])
          apply (rule condI1Eq[where d = "v \<triangleright> Nil"], rule zeroRefl, rule d)
          apply (rule condI1Eq[where d = "v \<triangleright> Nil"], rule c, rule d, rule d[unfolded isNat_def])
          done
        show "asn_put b 0 v N" by (rule eq_impl_term[OF r])
      next
        assume c: "\<not> b = Nil"
        have d: "v \<triangleright> list_tl b N" using v B by simp
        have r: "asn_put b 0 v = v \<triangleright> list_tl b"
          apply (rule defE[OF asn_put_def[where A = b and i = 0 and v = v]])
          apply (rule condI1Eq[where d = "v \<triangleright> list_tl b"], rule zeroRefl, rule d)
          apply (rule condI2Eq[where d = "v \<triangleright> list_tl b"], rule c, rule d, rule d[unfolded isNat_def])
          done
        show "asn_put b 0 v N" by (rule eq_impl_term[OF r])
      qed
    qed
  next
    fix k assume k: "k N" and IH: "\<forall>b. asn_put b k v N"
    have nz: "\<not> S k = 0" using k by simp
    have sk1: "S k - 1 = k" using k by simp
    show "\<forall>b. asn_put b (S k) v N"
    proof (rule forallI)
      fix b assume B: "b N"
      show "asn_put b (S k) v N"
      proof (rule cases_bool[where q = "b = Nil"])
        show "(b = Nil) B" by (rule eqBool[OF B nil_nat])
      next
        assume c: "b = Nil"
        have recN: "asn_put Nil k v N" by (rule forallE[OF IH nil_nat])
        have d: "0 \<triangleright> asn_put Nil k v N" using recN by simp
        have r: "asn_put b (S k) v = 0 \<triangleright> asn_put Nil k v"
          apply (rule defE[OF asn_put_def[where A = b and i = "S k" and v = v]])
          apply (rule condI2Eq[where d = "0 \<triangleright> asn_put Nil k v"], rule nz, rule d)
          apply (rule condI1Eq[where d = "0 \<triangleright> asn_put Nil k v"], rule c, rule d)
          apply (rule eqSubst[where Q = "\<lambda>n. 0 \<triangleright> asn_put Nil n v = 0 \<triangleright> asn_put Nil k v", OF eqSym[OF sk1]], rule d[unfolded isNat_def])
          done
        show "asn_put b (S k) v N" by (rule eq_impl_term[OF r])
      next
        assume c: "\<not> b = Nil"
        have recN: "asn_put (list_tl b) k v N" by (rule forallE[OF IH list_tl_nat[OF B]])
        have d: "list_hd b \<triangleright> asn_put (list_tl b) k v N" using B recN by simp
        have r: "asn_put b (S k) v = list_hd b \<triangleright> asn_put (list_tl b) k v"
          apply (rule defE[OF asn_put_def[where A = b and i = "S k" and v = v]])
          apply (rule condI2Eq[where d = "list_hd b \<triangleright> asn_put (list_tl b) k v"], rule nz, rule d)
          apply (rule condI2Eq[where d = "list_hd b \<triangleright> asn_put (list_tl b) k v"], rule c, rule d)
          apply (rule eqSubst[where Q = "\<lambda>n. list_hd b \<triangleright> asn_put (list_tl b) n v = list_hd b \<triangleright> asn_put (list_tl b) k v", OF eqSym[OF sk1]], rule d[unfolded isNat_def])
          done
        show "asn_put b (S k) v N" by (rule eq_impl_term[OF r])
      qed
    qed
  qed
  show ?thesis by (rule forallE[OF main A])
qed

lemma asn_put_0_nil:
  assumes v: "v N" shows "asn_put Nil 0 v = v \<triangleright> Nil"
proof -
  have d: "v \<triangleright> Nil N" using v by simp
  show ?thesis
    apply (rule defE[OF asn_put_def[where A = Nil and i = 0 and v = v]])
    apply (rule condI1Eq[where d = "v \<triangleright> Nil"], rule zeroRefl, rule d)
    apply (rule condI1Eq[where d = "v \<triangleright> Nil"], rule nil_nat[unfolded isNat_def], rule d, rule d[unfolded isNat_def])
    done
qed

lemma asn_put_0_ne:
  assumes A: "A N" and v: "v N" and ne: "\<not> A = Nil"
  shows "asn_put A 0 v = v \<triangleright> list_tl A"
proof -
  have d: "v \<triangleright> list_tl A N" using v A by simp
  show ?thesis
    apply (rule defE[OF asn_put_def[where A = A and i = 0 and v = v]])
    apply (rule condI1Eq[where d = "v \<triangleright> list_tl A"], rule zeroRefl, rule d)
    apply (rule condI2Eq[where d = "v \<triangleright> list_tl A"], rule ne, rule d, rule d[unfolded isNat_def])
    done
qed

lemma asn_put_S_nil:
  assumes v: "v N" and k: "k N"
  shows "asn_put Nil (S k) v = 0 \<triangleright> asn_put Nil k v"
proof -
  have nz: "\<not> S k = 0" using k by simp
  have sk1: "S k - 1 = k" using k by simp
  have recN: "asn_put Nil k v N" by (rule asn_put_N[OF nil_nat k v])
  have d: "0 \<triangleright> asn_put Nil k v N" using recN by simp
  show ?thesis
    apply (rule defE[OF asn_put_def[where A = Nil and i = "S k" and v = v]])
    apply (rule condI2Eq[where d = "0 \<triangleright> asn_put Nil k v"], rule nz, rule d)
    apply (rule condI1Eq[where d = "0 \<triangleright> asn_put Nil k v"], rule nil_nat[unfolded isNat_def], rule d)
    apply (rule eqSubst[where Q = "\<lambda>n. 0 \<triangleright> asn_put Nil n v = 0 \<triangleright> asn_put Nil k v", OF eqSym[OF sk1]], rule d[unfolded isNat_def])
    done
qed

lemma asn_put_S_ne:
  assumes A: "A N" and v: "v N" and k: "k N" and ne: "\<not> A = Nil"
  shows "asn_put A (S k) v = list_hd A \<triangleright> asn_put (list_tl A) k v"
proof -
  have nz: "\<not> S k = 0" using k by simp
  have sk1: "S k - 1 = k" using k by simp
  have recN: "asn_put (list_tl A) k v N" by (rule asn_put_N[OF list_tl_nat[OF A] k v])
  have d: "list_hd A \<triangleright> asn_put (list_tl A) k v N" using A recN by simp
  show ?thesis
    apply (rule defE[OF asn_put_def[where A = A and i = "S k" and v = v]])
    apply (rule condI2Eq[where d = "list_hd A \<triangleright> asn_put (list_tl A) k v"], rule nz, rule d)
    apply (rule condI2Eq[where d = "list_hd A \<triangleright> asn_put (list_tl A) k v"], rule ne, rule d)
    apply (rule eqSubst[where Q = "\<lambda>n. list_hd A \<triangleright> asn_put (list_tl A) n v = list_hd A \<triangleright> asn_put (list_tl A) k v", OF eqSym[OF sk1]], rule d[unfolded isNat_def])
    done
qed

lemma nth_put_eq:
  assumes A: "A N" and i: "i N" and v: "v N"
  shows "nth i (asn_put A i v) = v"
proof -
  have main: "\<forall>b. nth i (asn_put b i v) = v"
  proof (rule ind[OF i])
    show "\<forall>b. nth 0 (asn_put b 0 v) = v"
    proof (rule forallI)
      fix b assume B: "b N"
      show "nth 0 (asn_put b 0 v) = v"
      proof (rule cases_bool[where q = "b = Nil"])
        show "(b = Nil) B" by (rule eqBool[OF B nil_nat])
      next
        assume c: "b = Nil"
        have r: "asn_put b 0 v = v \<triangleright> Nil"
          using eqSym[OF c] asn_put_0_nil[OF v]
          by (rule eqSubst[where Q = "\<lambda>z. asn_put z 0 v = v \<triangleright> Nil"])
        show "nth 0 (asn_put b 0 v) = v"
          using eqSym[OF r] nth_zero_cons[OF v nil_nat]
          by (rule eqSubst[where Q = "\<lambda>z. nth 0 z = v"])
      next
        assume c: "\<not> b = Nil"
        have r: "asn_put b 0 v = v \<triangleright> list_tl b" by (rule asn_put_0_ne[OF B v c])
        show "nth 0 (asn_put b 0 v) = v"
          using eqSym[OF r] nth_zero_cons[OF v list_tl_nat[OF B]]
          by (rule eqSubst[where Q = "\<lambda>z. nth 0 z = v"])
      qed
    qed
  next
    fix k assume k: "k N" and IH: "\<forall>b. nth k (asn_put b k v) = v"
    show "\<forall>b. nth (S k) (asn_put b (S k) v) = v"
    proof (rule forallI)
      fix b assume B: "b N"
      show "nth (S k) (asn_put b (S k) v) = v"
      proof (rule cases_bool[where q = "b = Nil"])
        show "(b = Nil) B" by (rule eqBool[OF B nil_nat])
      next
        assume c: "b = Nil"
        have r: "asn_put b (S k) v = 0 \<triangleright> asn_put Nil k v"
          using eqSym[OF c] asn_put_S_nil[OF v k]
          by (rule eqSubst[where Q = "\<lambda>z. asn_put z (S k) v = 0 \<triangleright> asn_put Nil k v"])
        have ih: "nth k (asn_put Nil k v) = v" by (rule forallE[OF IH nil_nat])
        have nthN: "nth k (asn_put Nil k v) N" by (rule eq_impl_term[OF ih])
        have recN: "asn_put Nil k v N" by (rule asn_put_N[OF nil_nat k v])
        have sc: "nth (S k) (0 \<triangleright> asn_put Nil k v) = nth k (asn_put Nil k v)"
          by (rule nth_suc_cons[OF k nat0 recN nthN])
        have sv: "nth (S k) (0 \<triangleright> asn_put Nil k v) = v" using sc ih by (rule eq_trans)
        show "nth (S k) (asn_put b (S k) v) = v"
          using eqSym[OF r] sv by (rule eqSubst[where Q = "\<lambda>z. nth (S k) z = v"])
      next
        assume c: "\<not> b = Nil"
        have r: "asn_put b (S k) v = list_hd b \<triangleright> asn_put (list_tl b) k v" by (rule asn_put_S_ne[OF B v k c])
        have ih: "nth k (asn_put (list_tl b) k v) = v" by (rule forallE[OF IH list_tl_nat[OF B]])
        have nthN: "nth k (asn_put (list_tl b) k v) N" by (rule eq_impl_term[OF ih])
        have recN: "asn_put (list_tl b) k v N" by (rule asn_put_N[OF list_tl_nat[OF B] k v])
        have sc: "nth (S k) (list_hd b \<triangleright> asn_put (list_tl b) k v) = nth k (asn_put (list_tl b) k v)"
          by (rule nth_suc_cons[OF k list_hd_nat[OF B] recN nthN])
        have sv: "nth (S k) (list_hd b \<triangleright> asn_put (list_tl b) k v) = v" using sc ih by (rule eq_trans)
        show "nth (S k) (asn_put b (S k) v) = v"
          using eqSym[OF r] sv by (rule eqSubst[where Q = "\<lambda>z. nth (S k) z = v"])
      qed
    qed
  qed
  show ?thesis by (rule forallE[OF main A])
qed

lemma nth_zero_ne_nil:
  assumes L: "L N" and ne: "\<not> L = Nil"
  shows "nth 0 L = list_hd L"
proof -
  have rec: "list_hd L \<triangleright> list_tl L = L" by (rule cons_reconstr[OF L ne])
  have z: "nth 0 (list_hd L \<triangleright> list_tl L) = list_hd L"
    by (rule nth_zero_cons[OF list_hd_nat[OF L] list_tl_nat[OF L]])
  show ?thesis
    using rec z by (rule eqSubst[where Q="\<lambda>z. nth 0 z = list_hd L"])
qed

lemma nth_suc_ne_nil:
  assumes m: "m N" and L: "L N" and ne: "\<not> L = Nil"
  shows "nth (S m) L = nth m (list_tl L)"
proof -
  have rec: "list_hd L \<triangleright> list_tl L = L" by (rule cons_reconstr[OF L ne])
  have nmtl: "nth m (list_tl L) N" by (rule nth_N'[OF list_tl_nat[OF L] m])
  have z: "nth (S m) (list_hd L \<triangleright> list_tl L) = nth m (list_tl L)"
    by (rule nth_suc_cons[OF m list_hd_nat[OF L] list_tl_nat[OF L] nmtl])
  show ?thesis
    using rec z by (rule eqSubst[where Q="\<lambda>z. nth (S m) z = nth m (list_tl L)"])
qed

text \<open>Coincidence away from the updated index: for @{text "j \<noteq> i"} the value at
  @{text j} is unaffected by @{text "asn_put A i v"}.  Now that @{text nth} is
  total this holds unconditionally (no range guard).\<close>
lemma nth_put_ne:
  assumes A: "A N" and i: "i N" and v: "v N" and j: "j N" and ne: "\<not> j = i"
  shows "nth j (asn_put A i v) = nth j A"
proof -
  have main: "\<forall>A. \<forall>j. (\<not> j = i) \<longrightarrow> nth j (asn_put A i v) = nth j A"
  proof (rule ind[OF i])
    (* ================= base: i = 0 ================= *)
    show "\<forall>A. \<forall>j. (\<not> j = 0) \<longrightarrow> nth j (asn_put A 0 v) = nth j A"
    proof (rule forallI)
      fix Aa assume Aa: "Aa N"
      show "\<forall>j. (\<not> j = 0) \<longrightarrow> nth j (asn_put Aa 0 v) = nth j Aa"
      proof (rule forallI)
        fix jj assume jj: "jj N"
        show "(\<not> jj = 0) \<longrightarrow> nth jj (asn_put Aa 0 v) = nth jj Aa"
        proof (rule implI)
          show "(\<not> jj = 0) B" by (rule not_bool[OF eqBool[OF jj nat0]])
        next
          assume jnz: "\<not> jj = 0"
          show "nth jj (asn_put Aa 0 v) = nth jj Aa"
          proof (rule cases_nat_2[where x=jj])
            show "jj N" by (rule jj)
          next
            assume jz: "jj = 0"
            show "nth 0 (asn_put Aa 0 v) = nth 0 Aa" by (rule exF[OF jz jnz])
          next
            fix m assume m: "m N" and jm: "jj = S m"
            show "nth (S m) (asn_put Aa 0 v) = nth (S m) Aa"
            proof (rule cases_bool[where q="Aa = Nil"])
              show "(Aa = Nil) B" by (rule eqBool[OF Aa nil_nat])
            next
              assume anil: "Aa = Nil"
              have nmNil: "nth m Nil N" by (rule nth_N'[OF nil_nat m])
              have e1: "asn_put Nil 0 v = v \<triangleright> Nil" by (rule asn_put_0_nil[OF v])
              have e2: "nth (S m) (v \<triangleright> Nil) = nth m Nil"
                by (rule nth_suc_cons[OF m v nil_nat nmNil])
              have e3: "nth (S m) (asn_put Nil 0 v) = nth m Nil"
                using eqSym[OF e1] e2 by (rule eqSubst[where Q="\<lambda>z. nth (S m) z = nth m Nil"])
              have e4: "nth (S m) (asn_put Nil 0 v) = 0" using e3 nth_nil by (rule eq_trans)
              have gNil: "nth (S m) (asn_put Nil 0 v) = nth (S m) Nil"
                using e4 eqSym[OF nth_nil] by (rule eq_trans)
              show "nth (S m) (asn_put Aa 0 v) = nth (S m) Aa"
                using eqSym[OF anil] gNil
                by (rule eqSubst[where Q="\<lambda>z. nth (S m) (asn_put z 0 v) = nth (S m) z"])
            next
              assume ann: "\<not> Aa = Nil"
              have nmtl: "nth m (list_tl Aa) N" by (rule nth_N'[OF list_tl_nat[OF Aa] m])
              have e1: "asn_put Aa 0 v = v \<triangleright> list_tl Aa" by (rule asn_put_0_ne[OF Aa v ann])
              have e2: "nth (S m) (v \<triangleright> list_tl Aa) = nth m (list_tl Aa)"
                by (rule nth_suc_cons[OF m v list_tl_nat[OF Aa] nmtl])
              have lhs: "nth (S m) (asn_put Aa 0 v) = nth m (list_tl Aa)"
                using eqSym[OF e1] e2 by (rule eqSubst[where Q="\<lambda>z. nth (S m) z = nth m (list_tl Aa)"])
              have rhs: "nth (S m) Aa = nth m (list_tl Aa)" by (rule nth_suc_ne_nil[OF m Aa ann])
              show "nth (S m) (asn_put Aa 0 v) = nth (S m) Aa"
                using lhs eqSym[OF rhs] by (rule eq_trans)
            qed
          qed
        qed
      qed
    qed
  next
    (* ================= step: i = S k ================= *)
    fix k assume k: "k N"
      and IH: "\<forall>A. \<forall>j. (\<not> j = k) \<longrightarrow> nth j (asn_put A k v) = nth j A"
    show "\<forall>A. \<forall>j. (\<not> j = S k) \<longrightarrow> nth j (asn_put A (S k) v) = nth j A"
    proof (rule forallI)
      fix Aa assume Aa: "Aa N"
      show "\<forall>j. (\<not> j = S k) \<longrightarrow> nth j (asn_put Aa (S k) v) = nth j Aa"
      proof (rule forallI)
        fix jj assume jj: "jj N"
        show "(\<not> jj = S k) \<longrightarrow> nth jj (asn_put Aa (S k) v) = nth jj Aa"
        proof (rule implI)
          show "(\<not> jj = S k) B" by (rule not_bool[OF eqBool[OF jj natS[OF k]]])
        next
          assume jnz2: "\<not> jj = S k"
          show "nth jj (asn_put Aa (S k) v) = nth jj Aa"
          proof (rule cases_nat_2[where x=jj])
            show "jj N" by (rule jj)
          next
            assume jz: "jj = 0"
            show "nth 0 (asn_put Aa (S k) v) = nth 0 Aa"
            proof (rule cases_bool[where q="Aa = Nil"])
              show "(Aa = Nil) B" by (rule eqBool[OF Aa nil_nat])
            next
              assume anil: "Aa = Nil"
              have recN: "asn_put Nil k v N" by (rule asn_put_N[OF nil_nat k v])
              have e1: "asn_put Nil (S k) v = 0 \<triangleright> asn_put Nil k v" by (rule asn_put_S_nil[OF v k])
              have e2: "nth 0 (0 \<triangleright> asn_put Nil k v) = 0" by (rule nth_zero_cons[OF nat0 recN])
              have e3: "nth 0 (asn_put Nil (S k) v) = 0"
                using eqSym[OF e1] e2 by (rule eqSubst[where Q="\<lambda>z. nth 0 z = 0"])
              have gNil: "nth 0 (asn_put Nil (S k) v) = nth 0 Nil"
                using e3 eqSym[OF nth_nil] by (rule eq_trans)
              show "nth 0 (asn_put Aa (S k) v) = nth 0 Aa"
                using eqSym[OF anil] gNil
                by (rule eqSubst[where Q="\<lambda>z. nth 0 (asn_put z (S k) v) = nth 0 z"])
            next
              assume ann: "\<not> Aa = Nil"
              have recN: "asn_put (list_tl Aa) k v N" by (rule asn_put_N[OF list_tl_nat[OF Aa] k v])
              have e1: "asn_put Aa (S k) v = list_hd Aa \<triangleright> asn_put (list_tl Aa) k v"
                by (rule asn_put_S_ne[OF Aa v k ann])
              have e2: "nth 0 (list_hd Aa \<triangleright> asn_put (list_tl Aa) k v) = list_hd Aa"
                by (rule nth_zero_cons[OF list_hd_nat[OF Aa] recN])
              have lhs: "nth 0 (asn_put Aa (S k) v) = list_hd Aa"
                using eqSym[OF e1] e2 by (rule eqSubst[where Q="\<lambda>z. nth 0 z = list_hd Aa"])
              have rhs: "nth 0 Aa = list_hd Aa" by (rule nth_zero_ne_nil[OF Aa ann])
              show "nth 0 (asn_put Aa (S k) v) = nth 0 Aa"
                using lhs eqSym[OF rhs] by (rule eq_trans)
            qed
          next
            fix m assume m: "m N" and jm: "jj = S m"
            show "nth (S m) (asn_put Aa (S k) v) = nth (S m) Aa"
            proof (rule cases_bool[where q="m = k"])
              show "(m = k) B" by (rule eqBool[OF m k])
            next
              assume mk: "m = k"
              have smsk: "S m = S k" using mk by (rule sucCong)
              have jjsk: "jj = S k" using jm smsk by (rule eq_trans)
              show "nth (S m) (asn_put Aa (S k) v) = nth (S m) Aa"
                by (rule exF[OF jjsk jnz2])
            next
              assume mk: "\<not> m = k"
              show "nth (S m) (asn_put Aa (S k) v) = nth (S m) Aa"
              proof (rule cases_bool[where q="Aa = Nil"])
                show "(Aa = Nil) B" by (rule eqBool[OF Aa nil_nat])
              next
                assume anil: "Aa = Nil"
                have recN: "asn_put Nil k v N" by (rule asn_put_N[OF nil_nat k v])
                have nmrec: "nth m (asn_put Nil k v) N" by (rule nth_N'[OF recN m])
                have e1: "asn_put Nil (S k) v = 0 \<triangleright> asn_put Nil k v" by (rule asn_put_S_nil[OF v k])
                have e2: "nth (S m) (0 \<triangleright> asn_put Nil k v) = nth m (asn_put Nil k v)"
                  by (rule nth_suc_cons[OF m nat0 recN nmrec])
                have lhs1: "nth (S m) (asn_put Nil (S k) v) = nth m (asn_put Nil k v)"
                  using eqSym[OF e1] e2 by (rule eqSubst[where Q="\<lambda>z. nth (S m) z = nth m (asn_put Nil k v)"])
                have ihstep1: "\<forall>j. (\<not> j = k) \<longrightarrow> nth j (asn_put Nil k v) = nth j Nil"
                  by (rule forallE[OF IH nil_nat])
                have ihstep2: "(\<not> m = k) \<longrightarrow> nth m (asn_put Nil k v) = nth m Nil"
                  by (rule forallE[OF ihstep1 m])
                have ihm: "nth m (asn_put Nil k v) = nth m Nil" by (rule implE[OF ihstep2 mk])
                have lhs2: "nth (S m) (asn_put Nil (S k) v) = nth m Nil" using lhs1 ihm by (rule eq_trans)
                have lhsz: "nth (S m) (asn_put Nil (S k) v) = 0" using lhs2 nth_nil by (rule eq_trans)
                have gNil: "nth (S m) (asn_put Nil (S k) v) = nth (S m) Nil"
                  using lhsz eqSym[OF nth_nil] by (rule eq_trans)
                show "nth (S m) (asn_put Aa (S k) v) = nth (S m) Aa"
                  using eqSym[OF anil] gNil
                  by (rule eqSubst[where Q="\<lambda>z. nth (S m) (asn_put z (S k) v) = nth (S m) z"])
              next
                assume ann: "\<not> Aa = Nil"
                have recN: "asn_put (list_tl Aa) k v N" by (rule asn_put_N[OF list_tl_nat[OF Aa] k v])
                have nmrec: "nth m (asn_put (list_tl Aa) k v) N" by (rule nth_N'[OF recN m])
                have e1: "asn_put Aa (S k) v = list_hd Aa \<triangleright> asn_put (list_tl Aa) k v"
                  by (rule asn_put_S_ne[OF Aa v k ann])
                have e2: "nth (S m) (list_hd Aa \<triangleright> asn_put (list_tl Aa) k v) = nth m (asn_put (list_tl Aa) k v)"
                  by (rule nth_suc_cons[OF m list_hd_nat[OF Aa] recN nmrec])
                have lhs1: "nth (S m) (asn_put Aa (S k) v) = nth m (asn_put (list_tl Aa) k v)"
                  using eqSym[OF e1] e2 by (rule eqSubst[where Q="\<lambda>z. nth (S m) z = nth m (asn_put (list_tl Aa) k v)"])
                have ihstep1: "\<forall>j. (\<not> j = k) \<longrightarrow> nth j (asn_put (list_tl Aa) k v) = nth j (list_tl Aa)"
                  by (rule forallE[OF IH list_tl_nat[OF Aa]])
                have ihstep2: "(\<not> m = k) \<longrightarrow> nth m (asn_put (list_tl Aa) k v) = nth m (list_tl Aa)"
                  by (rule forallE[OF ihstep1 m])
                have ihm: "nth m (asn_put (list_tl Aa) k v) = nth m (list_tl Aa)" by (rule implE[OF ihstep2 mk])
                have lhs2: "nth (S m) (asn_put Aa (S k) v) = nth m (list_tl Aa)" using lhs1 ihm by (rule eq_trans)
                have rhs: "nth (S m) Aa = nth m (list_tl Aa)" by (rule nth_suc_ne_nil[OF m Aa ann])
                show "nth (S m) (asn_put Aa (S k) v) = nth (S m) Aa"
                  using lhs2 eqSym[OF rhs] by (rule eq_trans)
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  have m1: "\<forall>j. (\<not> j = i) \<longrightarrow> nth j (asn_put A i v) = nth j A" by (rule forallE[OF main A])
  have m2: "(\<not> j = i) \<longrightarrow> nth j (asn_put A i v) = nth j A" by (rule forallE[OF m1 j])
  show ?thesis by (rule implE[OF m2 ne])
qed

lemma asn_put_overwrite:
  assumes A: "A N" and i: "i N" and v: "v N" and w: "w N"
  shows "asn_put (asn_put A i v) i w = asn_put A i w"
proof -
  have main: "\<forall>b. asn_put (asn_put b i v) i w = asn_put b i w"
  proof (rule ind[OF i])
    show "\<forall>b. asn_put (asn_put b 0 v) 0 w = asn_put b 0 w"
    proof (rule forallI)
      fix b assume B: "b N"
      show "asn_put (asn_put b 0 v) 0 w = asn_put b 0 w"
      proof (rule cases_bool[where q = "b = Nil"])
        show "(b = Nil) B" by (rule eqBool[OF B nil_nat])
      next
        assume c: "b = Nil"
        have vnil: "v \<triangleright> Nil N" by (rule cons_nat[OF v nil_nat])
        have r1: "asn_put b 0 v = v \<triangleright> Nil"
          using eqSym[OF c] asn_put_0_nil[OF v]
          by (rule eqSubst[where Q = "\<lambda>z. asn_put z 0 v = v \<triangleright> Nil"])
        have ne1: "\<not> v \<triangleright> Nil = Nil" using v by simp
        have r2: "asn_put (v \<triangleright> Nil) 0 w = w \<triangleright> list_tl (v \<triangleright> Nil)" by (rule asn_put_0_ne[OF vnil w ne1])
        have tl1: "list_tl (v \<triangleright> Nil) = Nil" by (rule list_tl_cons[OF v nil_nat])
        have r3: "asn_put b 0 w = w \<triangleright> Nil"
          using eqSym[OF c] asn_put_0_nil[OF w]
          by (rule eqSubst[where Q = "\<lambda>z. asn_put z 0 w = w \<triangleright> Nil"])
        have e2: "asn_put (v \<triangleright> Nil) 0 w = w \<triangleright> Nil"
          using tl1 r2 by (rule eqSubst[where Q = "\<lambda>z. asn_put (v \<triangleright> Nil) 0 w = w \<triangleright> z"])
        have eL: "asn_put (asn_put b 0 v) 0 w = w \<triangleright> Nil"
          using eqSym[OF r1] e2 by (rule eqSubst[where Q = "\<lambda>z. asn_put z 0 w = w \<triangleright> Nil"])
        show "asn_put (asn_put b 0 v) 0 w = asn_put b 0 w"
          using eL eqSym[OF r3] by (rule eq_trans)
      next
        assume c: "\<not> b = Nil"
        have tlB: "list_tl b N" using B by simp
        have vtl: "v \<triangleright> list_tl b N" by (rule cons_nat[OF v tlB])
        have r1: "asn_put b 0 v = v \<triangleright> list_tl b" by (rule asn_put_0_ne[OF B v c])
        have ne1: "\<not> v \<triangleright> list_tl b = Nil" using v tlB by simp
        have r2: "asn_put (v \<triangleright> list_tl b) 0 w = w \<triangleright> list_tl (v \<triangleright> list_tl b)" by (rule asn_put_0_ne[OF vtl w ne1])
        have tl1: "list_tl (v \<triangleright> list_tl b) = list_tl b" by (rule list_tl_cons[OF v tlB])
        have r3: "asn_put b 0 w = w \<triangleright> list_tl b" by (rule asn_put_0_ne[OF B w c])
        have e2: "asn_put (v \<triangleright> list_tl b) 0 w = w \<triangleright> list_tl b"
          using tl1 r2 by (rule eqSubst[where Q = "\<lambda>z. asn_put (v \<triangleright> list_tl b) 0 w = w \<triangleright> z"])
        have eL: "asn_put (asn_put b 0 v) 0 w = w \<triangleright> list_tl b"
          using eqSym[OF r1] e2 by (rule eqSubst[where Q = "\<lambda>z. asn_put z 0 w = w \<triangleright> list_tl b"])
        show "asn_put (asn_put b 0 v) 0 w = asn_put b 0 w"
          using eL eqSym[OF r3] by (rule eq_trans)
      qed
    qed
  next
    fix k assume k: "k N" and IH: "\<forall>b. asn_put (asn_put b k v) k w = asn_put b k w"
    show "\<forall>b. asn_put (asn_put b (S k) v) (S k) w = asn_put b (S k) w"
    proof (rule forallI)
      fix b assume B: "b N"
      show "asn_put (asn_put b (S k) v) (S k) w = asn_put b (S k) w"
      proof (rule cases_bool[where q = "b = Nil"])
        show "(b = Nil) B" by (rule eqBool[OF B nil_nat])
      next
        assume c: "b = Nil"
        have recvN: "asn_put Nil k v N" by (rule asn_put_N[OF nil_nat k v])
        have rv: "asn_put b (S k) v = 0 \<triangleright> asn_put Nil k v"
          using eqSym[OF c] asn_put_S_nil[OF v k]
          by (rule eqSubst[where Q = "\<lambda>z. asn_put z (S k) v = 0 \<triangleright> asn_put Nil k v"])
        have cne: "\<not> 0 \<triangleright> asn_put Nil k v = Nil" using recvN by simp
        have consN: "0 \<triangleright> asn_put Nil k v N" by (rule cons_nat[OF nat0 recvN])
        have r2: "asn_put (0 \<triangleright> asn_put Nil k v) (S k) w
                  = list_hd (0 \<triangleright> asn_put Nil k v) \<triangleright> asn_put (list_tl (0 \<triangleright> asn_put Nil k v)) k w"
          by (rule asn_put_S_ne[OF consN w k cne])
        have hd2: "list_hd (0 \<triangleright> asn_put Nil k v) = 0" by (rule list_hd_cons[OF nat0 recvN])
        have tl2: "list_tl (0 \<triangleright> asn_put Nil k v) = asn_put Nil k v" by (rule list_tl_cons[OF nat0 recvN])
        have ihNil: "asn_put (asn_put Nil k v) k w = asn_put Nil k w" by (rule forallE[OF IH nil_nat])
        have rw: "asn_put b (S k) w = 0 \<triangleright> asn_put Nil k w"
          using eqSym[OF c] asn_put_S_nil[OF w k]
          by (rule eqSubst[where Q = "\<lambda>z. asn_put z (S k) w = 0 \<triangleright> asn_put Nil k w"])
        have s1: "asn_put (0 \<triangleright> asn_put Nil k v) (S k) w
                  = 0 \<triangleright> asn_put (list_tl (0 \<triangleright> asn_put Nil k v)) k w"
          using hd2 r2 by (rule eqSubst[where Q = "\<lambda>z. asn_put (0 \<triangleright> asn_put Nil k v) (S k) w = z \<triangleright> asn_put (list_tl (0 \<triangleright> asn_put Nil k v)) k w"])
        have s2: "asn_put (0 \<triangleright> asn_put Nil k v) (S k) w = 0 \<triangleright> asn_put (asn_put Nil k v) k w"
          using tl2 s1 by (rule eqSubst[where Q = "\<lambda>z. asn_put (0 \<triangleright> asn_put Nil k v) (S k) w = 0 \<triangleright> asn_put z k w"])
        have s3: "asn_put (0 \<triangleright> asn_put Nil k v) (S k) w = 0 \<triangleright> asn_put Nil k w"
          using ihNil s2 by (rule eqSubst[where Q = "\<lambda>z. asn_put (0 \<triangleright> asn_put Nil k v) (S k) w = 0 \<triangleright> z"])
        have eL: "asn_put (asn_put b (S k) v) (S k) w = 0 \<triangleright> asn_put Nil k w"
          using eqSym[OF rv] s3 by (rule eqSubst[where Q = "\<lambda>z. asn_put z (S k) w = 0 \<triangleright> asn_put Nil k w"])
        show "asn_put (asn_put b (S k) v) (S k) w = asn_put b (S k) w"
          using eL eqSym[OF rw] by (rule eq_trans)
      next
        assume c: "\<not> b = Nil"
        have tlB: "list_tl b N" using B by simp
        have hdB: "list_hd b N" using B by simp
        have recvN: "asn_put (list_tl b) k v N" by (rule asn_put_N[OF tlB k v])
        have rv: "asn_put b (S k) v = list_hd b \<triangleright> asn_put (list_tl b) k v" by (rule asn_put_S_ne[OF B v k c])
        have cne: "\<not> list_hd b \<triangleright> asn_put (list_tl b) k v = Nil" using hdB recvN by simp
        have consN: "list_hd b \<triangleright> asn_put (list_tl b) k v N" by (rule cons_nat[OF hdB recvN])
        have r2: "asn_put (list_hd b \<triangleright> asn_put (list_tl b) k v) (S k) w
                  = list_hd (list_hd b \<triangleright> asn_put (list_tl b) k v)
                      \<triangleright> asn_put (list_tl (list_hd b \<triangleright> asn_put (list_tl b) k v)) k w"
          by (rule asn_put_S_ne[OF consN w k cne])
        have hd2: "list_hd (list_hd b \<triangleright> asn_put (list_tl b) k v) = list_hd b" by (rule list_hd_cons[OF hdB recvN])
        have tl2: "list_tl (list_hd b \<triangleright> asn_put (list_tl b) k v) = asn_put (list_tl b) k v" by (rule list_tl_cons[OF hdB recvN])
        have ihB: "asn_put (asn_put (list_tl b) k v) k w = asn_put (list_tl b) k w" by (rule forallE[OF IH tlB])
        have rw: "asn_put b (S k) w = list_hd b \<triangleright> asn_put (list_tl b) k w" by (rule asn_put_S_ne[OF B w k c])
        have s1: "asn_put (list_hd b \<triangleright> asn_put (list_tl b) k v) (S k) w
                  = list_hd b \<triangleright> asn_put (list_tl (list_hd b \<triangleright> asn_put (list_tl b) k v)) k w"
          using hd2 r2 by (rule eqSubst[where Q = "\<lambda>z. asn_put (list_hd b \<triangleright> asn_put (list_tl b) k v) (S k) w = z \<triangleright> asn_put (list_tl (list_hd b \<triangleright> asn_put (list_tl b) k v)) k w"])
        have s2: "asn_put (list_hd b \<triangleright> asn_put (list_tl b) k v) (S k) w
                  = list_hd b \<triangleright> asn_put (asn_put (list_tl b) k v) k w"
          using tl2 s1 by (rule eqSubst[where Q = "\<lambda>z. asn_put (list_hd b \<triangleright> asn_put (list_tl b) k v) (S k) w = list_hd b \<triangleright> asn_put z k w"])
        have s3: "asn_put (list_hd b \<triangleright> asn_put (list_tl b) k v) (S k) w
                  = list_hd b \<triangleright> asn_put (list_tl b) k w"
          using ihB s2 by (rule eqSubst[where Q = "\<lambda>z. asn_put (list_hd b \<triangleright> asn_put (list_tl b) k v) (S k) w = list_hd b \<triangleright> z"])
        have eL: "asn_put (asn_put b (S k) v) (S k) w = list_hd b \<triangleright> asn_put (list_tl b) k w"
          using eqSym[OF rv] s3 by (rule eqSubst[where Q = "\<lambda>z. asn_put z (S k) w = list_hd b \<triangleright> asn_put (list_tl b) k w"])
        show "asn_put (asn_put b (S k) v) (S k) w = asn_put b (S k) w"
          using eL eqSym[OF rw] by (rule eq_trans)
      qed
    qed
  qed
  show ?thesis by (rule forallE[OF main A])
qed

lemma subst_T_var_other:
  assumes t: "t N" and i: "i N" and s: "s N" and tg: "tag_T t = T_VAR" and ld: "\<not> load_T t = i"
  shows "subst_T t i s = t"
proof -
  have inner: "(if load_T t = i then s else t) = t"
    apply (rule condI2Eq[OF ld t])
    using t apply simp
    done
  show ?thesis
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI1Eq[OF tg t inner])
    done
qed

lemma subst_T_var_same:
  assumes t: "t N" and i: "i N" and s: "s N" and tg: "tag_T t = T_VAR" and ld: "load_T t = i"
  shows "subst_T t i s = s"
proof -
  have ss: "s = s"
    using s by simp
  have inner: "(if load_T t = i then s else t) = s"
    by (rule condI1Eq[OF ld s ss])
  show ?thesis
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI1Eq[OF tg s inner])
    done
qed

lemma eval_fuel_subst_T_varD:
  assumes k: "k N" and t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N" and evs: "evals s A v" and tg: "tag_T t = T_VAR" and run: "eval_fuel k (subst_T t i s) A = S r"
  shows "eval_fuel k t (asn_put A i v) = S r"
proof (rule cases_nat_2[where x=k])
  show "k N"
    by (rule k)
next
  assume kz: "k = 0"
  have run0: "eval_fuel 0 (subst_T t i s) A = S r"
    by (rule eqSubst[where a=k and b=0 and Q="\<lambda>z. eval_fuel z (subst_T t i s) A = S r", OF kz run])
  have timeout: "eval_fuel 0 (subst_T t i s) A = 0"
    by (rule eval_fuel_zero)
  show "eval_fuel F_EQ t (asn_put A i v) = S r"
    by (rule zero_successE[OF timeout run0])
next
  fix n
  assume n: "n N" and ks: "k = S n"
  have sn: "S n N"
    by (rule natS[OF n])
  have putN: "asn_put A i v N"
    by (rule asn_put_N[OF A i v])
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have runS: "eval_fuel (S n) (subst_T t i s) A = S r"
    by (rule eqSubst[where a=k and b="S n" and Q="\<lambda>z. eval_fuel z (subst_T t i s) A = S r", OF ks run])
  have loadEqB: "(load_T t = i) B"
    by (rule eqBool[OF loadN i])
  have resultS: "eval_fuel (S n) t (asn_put A i v) = S r"
  proof (rule cases_bool[where q="load_T t = i"])
    show "(load_T t = i) B"
      by (rule loadEqB)
  next
    assume li: "load_T t = i"
    have sub: "subst_T t i s = s"
      by (rule subst_T_var_same[OF t i s tg li])
    have runSub: "eval_fuel (S n) s A = S r"
      by (rule eqSubst[where a="subst_T t i s" and b=s and Q="\<lambda>z. eval_fuel (S n) z A = S r", OF sub runS])
    have rv: "r = v"
      by (rule evals_fuel_unique[OF sn s A evs runSub])
    have nthI: "nth i (asn_put A i v) = v"
      by (rule nth_put_eq[OF A i v])
    have nthLoad: "nth (load_T t) (asn_put A i v) = v"
      by (rule eqSubst[where a=i and b="load_T t" and Q="\<lambda>z. nth z (asn_put A i v) = v", OF eqSym[OF li] nthI])
    have nthLoadN: "nth (load_T t) (asn_put A i v) N"
      by (rule eq_impl_term[OF nthLoad])
    have evalV: "eval_fuel (S n) t (asn_put A i v) = S (nth (load_T t) (asn_put A i v))"
      by (rule eval_fuel_var[OF n tg nthLoadN])
    have nthLoadV: "S (nth (load_T t) (asn_put A i v)) = S v"
      by (rule sucCong[OF nthLoad])
    have evalV': "eval_fuel (S n) t (asn_put A i v) = S v"
      using evalV nthLoadV by (rule eq_trans)
    have vr: "S v = S r"
      by (rule sucCong[OF eqSym[OF rv]])
    show "eval_fuel (S n) t (asn_put A i v) = S r"
      using evalV' vr by (rule eq_trans)
  next
    assume li: "\<not> load_T t = i"
    have sub: "subst_T t i s = t"
      by (rule subst_T_var_other[OF t i s tg li])
    have runOld: "eval_fuel (S n) t A = S r"
      by (rule eqSubst[where a="subst_T t i s" and b=t and Q="\<lambda>z. eval_fuel (S n) z A = S r", OF sub runS])
    have nthA_N: "nth (load_T t) A N"
      by (rule nth_N'[OF A loadN])
    have oldEval: "eval_fuel (S n) t A = S (nth (load_T t) A)"
      by (rule eval_fuel_var[OF n tg nthA_N])
    have oldResult: "S (nth (load_T t) A) = S r"
      by (rule same_success[OF oldEval runOld])
    have nthSame: "nth (load_T t) (asn_put A i v) = nth (load_T t) A"
      by (rule nth_put_ne[OF A i v loadN li])
    have nthPutN: "nth (load_T t) (asn_put A i v) N"
      by (rule nth_N'[OF putN loadN])
    have newEval: "eval_fuel (S n) t (asn_put A i v) = S (nth (load_T t) (asn_put A i v))"
      by (rule eval_fuel_var[OF n tg nthPutN])
    have nthResult: "S (nth (load_T t) (asn_put A i v)) = S (nth (load_T t) A)"
      by (rule sucCong[OF nthSame])
    have newOld: "eval_fuel (S n) t (asn_put A i v) = S (nth (load_T t) A)"
      using newEval nthResult by (rule eq_trans)
    show "eval_fuel (S n) t (asn_put A i v) = S r"
      using newOld oldResult by (rule eq_trans)
  qed
  show "eval_fuel (S n) t (asn_put A i v) = S r"
    by (rule resultS)
qed

lemma eval_fuel_subst_T_zeroD:
  assumes k: "k N" and t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N" and evs: "evals s A v" and tg: "tag_T t = T_ZERO" and run: "eval_fuel k (subst_T t i s) A = S r"
  shows "eval_fuel k t (asn_put A i v) = S r"
proof (rule cases_nat_2[where x=k])
  show "k N"
    by (rule k)
next
  assume kz: "k = 0"
  have run0: "eval_fuel 0 (subst_T t i s) A = S r"
    by (rule eqSubst[where a=k and b=0 and Q="\<lambda>z. eval_fuel z (subst_T t i s) A = S r", OF kz run])
  have timeout: "eval_fuel 0 (subst_T t i s) A = 0"
    by (rule eval_fuel_zero)
  show "eval_fuel 0 t (asn_put A i v) = S r"
    by (rule zero_successE[OF timeout run0])
next
  fix n
  assume n: "n N" and ks: "k = S n"
  have runS: "eval_fuel (S n) (subst_T t i s) A = S r"
    by (rule eqSubst[where a=k and b="S n" and Q="\<lambda>z. eval_fuel z (subst_T t i s) A = S r", OF ks run])
  have packedN: "pack_T T_ZERO 0 N"
    by (rule pack_T_N[OF _ nat0], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have sub: "subst_T t i s = pack_T T_ZERO 0"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI1Eq[OF tg packedN])
    using packedN by simp
  have tagPacked: "tag_T (pack_T T_ZERO 0) = T_ZERO"
    by (rule tag_pack_T[OF _ nat0], simp)
  have runPacked: "eval_fuel (S n) (pack_T T_ZERO 0) A = S r"
    by (rule eqSubst[where a="subst_T t i s" and b="pack_T T_ZERO 0" and Q="\<lambda>z. eval_fuel (S n) z A = S r", OF sub runS])
  have packedValue: "eval_fuel (S n) (pack_T T_ZERO 0) A = S 0"
    by (rule eval_fuel_zero_step[OF n tagPacked])
  have resultZero: "S 0 = S r"
    by (rule same_success[OF packedValue runPacked])
  have newValue: "eval_fuel (S n) t (asn_put A i v) = S 0"
    by (rule eval_fuel_zero_step[OF n tg])
  show "eval_fuel (S n) t (asn_put A i v) = S r"
    using newValue resultZero by (rule eq_trans)
qed

lemma subst_T_N:
  assumes t: "t N" and j: "j N" and v: "v N"
  shows "subst_T t j v N"
proof (rule strong_induction[where a=t])
  show "t N" by (rule t)
next
  show "subst_T 0 j v N"
      proof -
    have zN: "pack_T T_ZERO 0 N"
      apply (rule pack_T_N) 
       apply simp 
      done
    have g1: "\<not> (tag_T 0 = T_VAR)" 
      by (simp add: tag_T_zero)
    have g2: "tag_T 0 = T_ZERO"     
      by (rule tag_T_zero)
    have red: "subst_T 0 j v = pack_T T_ZERO 0"
      apply (rule defE[OF subst_T_def[where t=0 and j=j and v=v]])
      apply (rule condI2Eq[OF g1 zN])
      apply (rule condI1Eq[OF g2 zN])
      using zN apply simp
      done
    show "subst_T 0 j v N" using red zN by simp
  qed
next
  fix x assume x: "x N" and IH: "\<And>y. y N \<Longrightarrow> y \<le> x = 1 \<Longrightarrow> subst_T y j v N"
  have sxN:  "S x N"          
    by (rule natS[OF x])
  have sxnz: "S x \<noteq> 0"        
    by (rule sucNonZero[OF x])
  have L:    "load_T (S x) N" 
    by (rule load_T_N[OF sxN])
  have Lx:   "load_T (S x) \<le> x = 1"
    by (rule le_suc_implies_leq[OF decrease_T[OF sxN sxnz] L x])
  have cxL:  "cpx (load_T (S x)) N" 
    by (rule cpx_terminates[OF L])
  have cyL:  "cpy (load_T (S x)) N" 
    by (rule cpy_terminates[OF L])
  have cxLx: "cpx (load_T (S x)) \<le> x = 1"
    by (rule leq_trans[OF cxL L x cpx_mono[OF L] Lx])
  have cyLx: "cpy (load_T (S x)) \<le> x = 1"
    by (rule leq_trans[OF cyL L x cpy_mono[OF L] Lx])
  have cxcyL: "cpx (cpy (load_T (S x))) N" 
    by (rule cpx_terminates[OF cyL])
  have cycyL: "cpy (cpy (load_T (S x))) N" 
    by (rule cpy_terminates[OF cyL])
  have cxcyLx: "cpx (cpy (load_T (S x))) \<le> x = 1"
    by (rule leq_trans[OF cxcyL cyL x cpx_mono[OF cyL] cyLx])
  have cycyLx: "cpy (cpy (load_T (S x))) \<le> x = 1"
    by (rule leq_trans[OF cycyL cyL x cpy_mono[OF cyL] cyLx])
  have r0: "subst_T (load_T (S x)) j v N"             
    by (rule IH[OF L Lx])
  have r1: "subst_T (cpx (load_T (S x))) j v N"       
    by (rule IH[OF cxL cxLx])
  have r2: "subst_T (cpx (cpy (load_T (S x)))) j v N" 
    by (rule IH[OF cxcyL cxcyLx])
  have r3: "subst_T (cpy (cpy (load_T (S x)))) j v N" 
    by (rule IH[OF cycyL cycyLx])  
    (* guards *)
  have tgN:   "tag_T (S x) N"             
    by (rule tag_T_N[OF sxN])
  have gVAR:  "(tag_T (S x) = T_VAR) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gZERO: "(tag_T (S x) = T_ZERO) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gSUC:  "(tag_T (S x) = T_SUC) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gPRED: "(tag_T (S x) = T_PRED) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gIFZ:  "(tag_T (S x) = T_IFZ) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  (* the six branches are all N *)
  have A1N: "(if load_T (S x) = j then v else S x) N"
    apply (rule condT[OF _ v sxN]) 
    apply (rule eqBool[OF L j]) 
    done
  have A2N: "pack_T T_ZERO 0 N"
    apply (rule pack_T_N) 
     apply simp 
    done
  have A3N: "pack_T T_SUC (subst_T (load_T (S x)) j v) N"
    apply (rule pack_T_N)
     apply simp
    apply (rule r0) 
    done
  have A4N: "pack_T T_PRED (subst_T (load_T (S x)) j v) N"
    apply (rule pack_T_N)
     apply simp
    apply (rule r0)
    done
  have iffN: "\<langle>subst_T (cpx (load_T (S x))) j v,
               \<langle>subst_T (cpx (cpy (load_T (S x)))) j v,
                subst_T (cpy (cpy (load_T (S x)))) j v\<rangle>\<rangle> N"
    using r1 r2 r3
    by simp
  have A5N: "pack_T T_IFZ \<langle>subst_T (cpx (load_T (S x))) j v,
               \<langle>subst_T (cpx (cpy (load_T (S x)))) j v,
                subst_T (cpy (cpy (load_T (S x)))) j v\<rangle>\<rangle> N"
    apply (rule pack_T_N)
    apply simp
    apply (rule r1)
    apply (rule r2)
    apply (rule r3)
    done

  have A6N: "pack_T T_APP \<langle>cpx (load_T (S x)),
               \<langle>subst_T (cpx (cpy (load_T (S x)))) j v,
                subst_T (cpy (cpy (load_T (S x)))) j v\<rangle>\<rangle> N"
    apply (rule pack_T_N)
     apply simp
    apply (rule L)
    apply (rule r2)
    apply (rule r3)
    done

  show "subst_T (S x) j v N"
    apply (rule defE[OF subst_T_def[where t="S x" and j=j and v=v]])
    apply (rule condT[OF gVAR A1N])
    apply (rule condT[OF gZERO A2N])
    apply (rule condT[OF gSUC A3N])
    apply (rule condT[OF gPRED A4N])
    apply (rule condT[OF gIFZ A5N])
    apply (rule A6N)
    done
qed

lemma subst_body_N:
  assumes b: "b N" and xa: "x N" and ya: "y N"
  shows "subst_body b x y N"
proof (rule strong_induction[where a=b])
  show "b N"
    by (rule b)
next
  show "subst_body 0 x y N"
    by (rule defE[OF subst_body_def[where b=0 and x=x and y=y]],
        simp add: tag_T_zero)
next
  fix w assume w: "w N" and IH: "\<And>z. z N \<Longrightarrow> z \<le> w = 1 \<Longrightarrow> subst_body z x y N"
  have swN:  "S w N"          using w
    by simp
  have swnz: "S w \<noteq> 0"       
    by (rule sucNonZero[OF w])
  have L:    "load_T (S w) N"
    by (rule load_T_N[OF swN])
  have Lw:   "load_T (S w) \<le> w = 1"
    by (rule le_suc_implies_leq[OF decrease_T[OF swN swnz] L w])
  have cxL: "cpx (load_T (S w)) N" using L
    by simp
  have cyL: "cpy (load_T (S w)) N" using L
    by simp
  have cxLw: "cpx (load_T (S w)) \<le> w = 1"
    by (rule leq_trans[OF cxL L w cpx_mono[OF L] Lw])
  have cyLw: "cpy (load_T (S w)) \<le> w = 1"
    by (rule leq_trans[OF cyL L w cpy_mono[OF L] Lw])
  have cxcyL: "cpx (cpy (load_T (S w))) N" using cyL
    by simp
  have cycyL: "cpy (cpy (load_T (S w))) N" using cyL
    by simp
  have cxcyLw: "cpx (cpy (load_T (S w))) \<le> w = 1"
    by (rule leq_trans[OF cxcyL cyL w cpx_mono[OF cyL] cyLw])
  have cycyLw: "cpy (cpy (load_T (S w))) \<le> w = 1"
    by (rule leq_trans[OF cycyL cyL w cpy_mono[OF cyL] cyLw])
  have r0: "subst_body (load_T (S w)) x y N"           
    by (rule IH[OF L Lw])
  have r1: "subst_body (cpx (load_T (S w))) x y N"     
    by (rule IH[OF cxL cxLw])
  have r2: "subst_body (cpx (cpy (load_T (S w)))) x y N"
    by (rule IH[OF cxcyL cxcyLw])
  have r3: "subst_body (cpy (cpy (load_T (S w)))) x y N"
    by (rule IH[OF cycyL cycyLw])
  have tgN:   "tag_T (S w) N"            
    by (rule tag_T_N[OF swN])
  have gVAR:  "(tag_T (S w) = T_VAR) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gZERO: "(tag_T (S w) = T_ZERO) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gSUC:  "(tag_T (S w) = T_SUC) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gPRED: "(tag_T (S w) = T_PRED) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gIFZ:  "(tag_T (S w) = T_IFZ) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  
  have ldN: "load_T (S w) N" by (rule L)
  have gL0: "(load_T (S w) = 0) B" 
    apply (rule eqBool[OF ldN]) 
    apply simp 
    done
  have gL1: "(load_T (S w) = 1) B" 
    apply (rule eqBool[OF ldN]) 
    apply simp 
    done
  
  have A1N: "(if load_T (S w) = 0 then x else if load_T (S w) = 1 then y else S w) N"
    apply (rule condT[OF gL0 xa])
    apply (rule condT[OF gL1 ya swN])
    done
  have A2N: "S w N" 
    by (rule swN)
  
  have A3N: "pack_T T_SUC (subst_body (load_T (S w)) x y) N"
    apply (rule pack_T_N) 
     apply simp 
    apply (rule r0) 
    done
    
  have A4N: "pack_T T_PRED (subst_body (load_T (S w)) x y) N"
    apply (rule pack_T_N) 
     apply simp 
    apply (rule r0) 
    done
    
  have iffN: "\<langle>subst_body (cpx (load_T (S w))) x y,
               \<langle>subst_body (cpx (cpy (load_T (S w)))) x y,
                subst_body (cpy (cpy (load_T (S w)))) x y\<rangle>\<rangle> N"
    using r1 r2 r3 by simp

  have A5N: "pack_T T_IFZ \<langle>subst_body (cpx (load_T (S w))) x y,
               \<langle>subst_body (cpx (cpy (load_T (S w)))) x y,
                subst_body (cpy (cpy (load_T (S w)))) x y\<rangle>\<rangle> N"
    apply (rule pack_T_N)
    apply simp
    apply (rule r1)
    apply (rule r2)
    apply (rule r3)
    done

  have A6N: "pack_T T_APP \<langle>cpx (load_T (S w)),
               \<langle>subst_body (cpx (cpy (load_T (S w)))) x y,
                subst_body (cpy (cpy (load_T (S w)))) x y\<rangle>\<rangle> N"
    apply (rule pack_T_N)
    apply simp
    apply (rule L)
    apply (rule r2)
    apply (rule r3)
    done

  show "subst_body (S w) x y N"
    apply (rule defE[OF subst_body_def[where b="S w" and x=x and y=y]])
    apply (rule condT[OF gVAR A1N])
    apply (rule condT[OF gZERO A2N])
    apply (rule condT[OF gSUC A3N])
    apply (rule condT[OF gPRED A4N])
    apply (rule condT[OF gIFZ A5N])
    apply (rule A6N)
    done
qed

lemma eval_fuel_subst_T_sucD:
  assumes n: "n N" and t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N" and tg: "tag_T t = T_SUC"
      and run: "eval_fuel (S n) (subst_T t i s) A = S r"
      and IH: "\<And>q. eval_fuel n (subst_T (load_T t) i s) A = S q \<Longrightarrow> eval_fuel n (load_T t) (asn_put A i v) = S q"
  shows "eval_fuel (S n) t (asn_put A i v) = S r"
proof -
  let ?child_orig = "load_T t"
  let ?child_sub = "subst_T ?child_orig i s"
  let ?packed = "pack_T T_SUC ?child_sub"
  let ?A_put = "asn_put A i v"
  have childOrigN: "?child_orig N"
    by (rule load_T_N[OF t])
  have childSubN: "?child_sub N"
    by (rule subst_T_N[OF childOrigN i s])
  have packedN: "?packed N"
    by (rule pack_T_N[OF _ childSubN], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have sub: "subst_T t i s = ?packed"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI2Eq[OF nzero packedN])
    apply (rule condI1Eq[OF tg packedN])
    using packedN by simp
  have tagPacked: "tag_T ?packed = T_SUC"
    by (rule tag_pack_T[OF _ childSubN], simp)
  have loadPacked: "load_T ?packed = ?child_sub"
    by (rule load_pack_T[OF _ childSubN], simp)
  have runPacked: "eval_fuel (S n) ?packed A = S r"
    by (rule eqSubst[where a="subst_T t i s" and b="?packed" and Q="\<lambda>z. eval_fuel (S n) z A = S r", OF sub run])
  have childEvalN: "eval_fuel n ?child_sub A N"
    by (rule eval_fuel_N[OF n childSubN A])
  show ?thesis
  proof (rule cases_nat_2[where x="eval_fuel n ?child_sub A"])
    show "eval_fuel n ?child_sub A N"
      by (rule childEvalN)
  next
    assume childZero: "eval_fuel n ?child_sub A = 0"
    have packedChildZero: "eval_fuel n (load_T ?packed) A = 0"
      by (rule eqSubst[where a="?child_sub" and b="load_T ?packed" and Q="\<lambda>z. eval_fuel n z A = 0", OF eqSym[OF loadPacked] childZero])
    have timeout: "eval_fuel (S n) ?packed A = 0"
      by (rule eval_fuel_suc_timeout[OF n tagPacked packedChildZero])
    show "eval_fuel (S n) t ?A_put = S r"
      by (rule zero_successE[OF timeout runPacked])
  next
    fix q
    assume q: "q N" and childSuccess: "eval_fuel n ?child_sub A = S q"
    have packedChildSuccess: "eval_fuel n (load_T ?packed) A = S q"
      by (rule eqSubst[where a="?child_sub" and b="load_T ?packed" and Q="\<lambda>z. eval_fuel n z A = S q", OF eqSym[OF loadPacked] childSuccess])
    have packedValue: "eval_fuel (S n) ?packed A = S (S q)"
      by (rule eval_fuel_suc_value[OF n tagPacked packedChildSuccess])
    have resultEq: "S (S q) = S r"
      by (rule same_success[OF packedValue runPacked])
    have childNew: "eval_fuel n ?child_orig ?A_put = S q"
      by (rule IH[OF childSuccess])
    have newValue: "eval_fuel (S n) t ?A_put = S (S q)"
      by (rule eval_fuel_suc_value[OF n tg childNew])
    show "eval_fuel (S n) t ?A_put = S r"
      using newValue resultEq by (rule eq_trans)
  qed
qed

lemma eval_fuel_subst_T_predD:
  assumes n: "n N" and t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N" and tg: "tag_T t = T_PRED"
      and run: "eval_fuel (S n) (subst_T t i s) A = S r"
      and IH: "\<And>q. eval_fuel n (subst_T (load_T t) i s) A = S q \<Longrightarrow> eval_fuel n (load_T t) (asn_put A i v) = S q"
  shows "eval_fuel (S n) t (asn_put A i v) = S r"
proof -
  let ?child_orig = "load_T t"
  let ?child_sub = "subst_T ?child_orig i s"
  let ?packed = "pack_T T_PRED ?child_sub"
  let ?A_put = "asn_put A i v"
  have childOrigN: "?child_orig N"
    by (rule load_T_N[OF t])
  have childSubN: "?child_sub N"
    by (rule subst_T_N[OF childOrigN i s])
  have packedN: "?packed N"
    by (rule pack_T_N[OF _ childSubN], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have sub: "subst_T t i s = ?packed"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI2Eq[OF nzero packedN])
    apply (rule condI2Eq[OF nsuc packedN])
    apply (rule condI1Eq[OF tg packedN])
    using packedN by simp
  have tagPacked: "tag_T ?packed = T_PRED"
    by (rule tag_pack_T[OF _ childSubN], simp)
  have loadPacked: "load_T ?packed = ?child_sub"
    by (rule load_pack_T[OF _ childSubN], simp)
  have runPacked: "eval_fuel (S n) ?packed A = S r"
    by (rule eqSubst[where a="subst_T t i s" and b="?packed" and Q="\<lambda>z. eval_fuel (S n) z A = S r", OF sub run])
  have childEvalN: "eval_fuel n ?child_sub A N"
    by (rule eval_fuel_N[OF n childSubN A])
  show ?thesis
  proof (rule cases_nat_2[where x="eval_fuel n ?child_sub A"])
    show "eval_fuel n ?child_sub A N"
      by (rule childEvalN)
  next
    assume childZero: "eval_fuel n ?child_sub A = 0"
    have packedChildZero: "eval_fuel n (load_T ?packed) A = 0"
      by (rule eqSubst[where a="?child_sub" and b="load_T ?packed" and Q="\<lambda>z. eval_fuel n z A = 0", OF eqSym[OF loadPacked] childZero])
    have timeout: "eval_fuel (S n) ?packed A = 0"
      by (rule eval_fuel_pred_timeout[OF n tagPacked packedChildZero])
    show "eval_fuel (S n) t ?A_put = S r"
      by (rule zero_successE[OF timeout runPacked])
  next
    fix q
    assume q: "q N" and childSuccess: "eval_fuel n ?child_sub A = S q"
    have packedChildSuccess: "eval_fuel n (load_T ?packed) A = S q"
      by (rule eqSubst[where a="?child_sub" and b="load_T ?packed" and Q="\<lambda>z. eval_fuel n z A = S q", OF eqSym[OF loadPacked] childSuccess])
    have packedValue: "eval_fuel (S n) ?packed A = S (P q)"
      by (rule eval_fuel_pred_value[OF n tagPacked packedChildSuccess])
    have resultEq: "S (P q) = S r"
      by (rule same_success[OF packedValue runPacked])
    have childNew: "eval_fuel n ?child_orig ?A_put = S q"
      by (rule IH[OF childSuccess])
    have newValue: "eval_fuel (S n) t ?A_put = S (P q)"
      by (rule eval_fuel_pred_value[OF n tg childNew])
    show "eval_fuel (S n) t ?A_put = S r"
      using newValue resultEq by (rule eq_trans)
  qed
qed

lemma eval_fuel_subst_T_ifzD:
  assumes n: "n N" and t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N" and tg: "tag_T t = T_IFZ" and run: "eval_fuel (S n) (subst_T t i s) A = S r"
      and IHcond: "\<And>q. eval_fuel n (subst_T (cpx (load_T t)) i s) A = S q \<Longrightarrow> eval_fuel n (cpx (load_T t)) (asn_put A i v) = S q"
      and IHthen: "\<And>q. eval_fuel n (subst_T (cpx (cpy (load_T t))) i s) A = S q \<Longrightarrow> eval_fuel n (cpx (cpy (load_T t))) (asn_put A i v) = S q"
      and IHelse: "\<And>q. eval_fuel n (subst_T (cpy (cpy (load_T t))) i s) A = S q \<Longrightarrow> eval_fuel n (cpy (cpy (load_T t))) (asn_put A i v) = S q"
  shows "eval_fuel (S n) t (asn_put A i v) = S r"
proof -
  let ?cond_orig = "cpx (load_T t)"
  let ?then_orig = "cpx (cpy (load_T t))"
  let ?else_orig = "cpy (cpy (load_T t))"
  let ?cond_sub = "subst_T ?cond_orig i s"
  let ?then_sub = "subst_T ?then_orig i s"
  let ?else_sub = "subst_T ?else_orig i s"
  let ?A_put = "asn_put A i v"
  let ?args = "\<langle>?then_sub, ?else_sub\<rangle>"
  let ?payload = "\<langle>?cond_sub, ?args\<rangle>"
  let ?packed = "pack_T T_IFZ ?payload"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have condOrigN: "?cond_orig N"
    by (rule cpx_terminates[OF loadN])
  have tailN: "cpy (load_T t) N"
    by (rule cpy_terminates[OF loadN])
  have thenOrigN: "?then_orig N"
    by (rule cpx_terminates[OF tailN])
  have elseOrigN: "?else_orig N"
    by (rule cpy_terminates[OF tailN])
  have condSubN: "?cond_sub N"
    by (rule subst_T_N[OF condOrigN i s])
  have thenSubN: "?then_sub N"
    by (rule subst_T_N[OF thenOrigN i s])
  have elseSubN: "?else_sub N"
    by (rule subst_T_N[OF elseOrigN i s])
  have argsN: "?args N"
    using thenSubN elseSubN by simp
  have payloadN: "?payload N"
    using condSubN argsN by simp
  have packedN: "?packed N"
    by (rule pack_T_N[OF _ payloadN], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have npred: "\<not> tag_T t = T_PRED"
    using tg by simp
  have sub: "subst_T t i s = ?packed"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI2Eq[OF nzero packedN])
    apply (rule condI2Eq[OF nsuc packedN])
    apply (rule condI2Eq[OF npred packedN])
    apply (rule condI1Eq[OF tg packedN])
    using packedN by simp
  have tagPacked: "tag_T ?packed = T_IFZ"
    by (rule tag_pack_T[OF _ payloadN], simp)
  have loadPacked: "load_T ?packed = ?payload"
    by (rule load_pack_T[OF _ payloadN], simp)
  have payloadCond: "cpx ?payload = ?cond_sub"
    by (rule cpx_proj[OF condSubN argsN])
  have payloadArgs: "cpy ?payload = ?args"
    by (rule cpy_proj[OF condSubN argsN])
  have argsThen: "cpx ?args = ?then_sub"
    by (rule cpx_proj[OF thenSubN elseSubN])
  have argsElse: "cpy ?args = ?else_sub"
    by (rule cpy_proj[OF thenSubN elseSubN])
  have selectCond: "cpx (load_T ?packed) = ?cond_sub"
    by (rule eqSubst[where a="?payload" and b="load_T ?packed" and Q="\<lambda>z. cpx z = ?cond_sub", OF eqSym[OF loadPacked] payloadCond])
  have selectArgs: "cpy (load_T ?packed) = ?args"
    by (rule eqSubst[where a="?payload" and b="load_T ?packed" and Q="\<lambda>z. cpy z = ?args", OF eqSym[OF loadPacked] payloadArgs])
  have selectThen: "cpx (cpy (load_T ?packed)) = ?then_sub"
    by (rule eqSubst[where a="?args" and b="cpy (load_T ?packed)" and Q="\<lambda>z. cpx z = ?then_sub", OF eqSym[OF selectArgs] argsThen])
  have selectElse: "cpy (cpy (load_T ?packed)) = ?else_sub"
    by (rule eqSubst[where a="?args" and b="cpy (load_T ?packed)" and Q="\<lambda>z. cpy z = ?else_sub", OF eqSym[OF selectArgs] argsElse])
  have runPacked: "eval_fuel (S n) ?packed A = S r"
    by (rule eqSubst[where a="subst_T t i s" and b="?packed" and Q="\<lambda>z. eval_fuel (S n) z A = S r", OF sub run])
  have condEvalN: "eval_fuel n ?cond_sub A N"
    by (rule eval_fuel_N[OF n condSubN A])
  show ?thesis
  proof (rule cases_nat_2[where x="eval_fuel n ?cond_sub A"])
    show "eval_fuel n ?cond_sub A N"
      by (rule condEvalN)
  next
    assume condTimeout: "eval_fuel n ?cond_sub A = 0"
    have condPackedTimeout: "eval_fuel n (cpx (load_T ?packed)) A = 0"
      by (rule eqSubst[where a="?cond_sub" and b="cpx (load_T ?packed)" and Q="\<lambda>z. eval_fuel n z A = 0", OF eqSym[OF selectCond] condTimeout])
    have timeout: "eval_fuel (S n) ?packed A = 0"
      by (rule eval_fuel_ifz_cond_timeout[OF n tagPacked condPackedTimeout])
    show "eval_fuel (S n) t ?A_put = S r"
      by (rule zero_successE[OF timeout runPacked])
  next
    fix c
    assume c: "c N" and condSuccess: "eval_fuel n ?cond_sub A = S c"
    show "eval_fuel (S n) t ?A_put = S r"
    proof (rule cases_nat_2[where x=c])
      show "c N"
        by (rule c)
    next
      assume cz: "c = 0"
      have scz: "S c = S 0"
        by (rule sucCong[OF cz])
      have condZero: "eval_fuel n ?cond_sub A = S 0"
        using condSuccess scz by (rule eq_trans)
      have condPackedZero: "eval_fuel n (cpx (load_T ?packed)) A = S 0"
        by (rule eqSubst[where a="?cond_sub" and b="cpx (load_T ?packed)" and Q="\<lambda>z. eval_fuel n z A = S 0", OF eqSym[OF selectCond] condZero])
      have thenEvalN: "eval_fuel n ?then_sub A N"
        by (rule eval_fuel_N[OF n thenSubN A])
      have thenPackedEvalN: "eval_fuel n (cpx (cpy (load_T ?packed))) A N"
        by (rule eqSubst[where a="?then_sub" and b="cpx (cpy (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A N", OF eqSym[OF selectThen] thenEvalN])
      show "eval_fuel (S n) t ?A_put = S r"
      proof (rule cases_nat_2[where x="eval_fuel n ?then_sub A"])
        show "eval_fuel n ?then_sub A N"
          by (rule thenEvalN)
      next
        assume thenTimeout: "eval_fuel n ?then_sub A = 0"
        have thenPackedTimeout: "eval_fuel n (cpx (cpy (load_T ?packed))) A = 0"
          by (rule eqSubst[where a="?then_sub" and b="cpx (cpy (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = 0", OF eqSym[OF selectThen] thenTimeout])
        have step: "eval_fuel (S n) ?packed A = eval_fuel n (cpx (cpy (load_T ?packed))) A"
          by (rule eval_fuel_ifz_zero[OF n tagPacked condPackedZero thenPackedEvalN])
        have timeout: "eval_fuel (S n) ?packed A = 0"
          using step thenPackedTimeout by (rule eq_trans)
        show "eval_fuel (S n) t ?A_put = S r"
          by (rule zero_successE[OF timeout runPacked])
      next
        fix q
        assume q: "q N" and thenSuccess: "eval_fuel n ?then_sub A = S q"
        have thenPackedSuccess: "eval_fuel n (cpx (cpy (load_T ?packed))) A = S q"
          by (rule eqSubst[where a="?then_sub" and b="cpx (cpy (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = S q", OF eqSym[OF selectThen] thenSuccess])
        have packedValue: "eval_fuel (S n) ?packed A = S q"
          by (rule eval_fuel_ifz_zero_value[OF n tagPacked condPackedZero thenPackedSuccess])
        have resultEq: "S q = S r"
          by (rule same_success[OF packedValue runPacked])
        have condNew: "eval_fuel n ?cond_orig ?A_put = S 0"
          by (rule IHcond[OF condZero])
        have thenNew: "eval_fuel n ?then_orig ?A_put = S q"
          by (rule IHthen[OF thenSuccess])
        have newValue: "eval_fuel (S n) t ?A_put = S q"
          by (rule eval_fuel_ifz_zero_value[OF n tg condNew thenNew])
        show "eval_fuel (S n) t ?A_put = S r"
          using newValue resultEq by (rule eq_trans)
      qed
    next
      fix d
      assume d: "d N" and cnz: "c = S d"
      have scnz: "S c = S (S d)"
        by (rule sucCong[OF cnz])
      have condNonzero: "eval_fuel n ?cond_sub A = S (S d)"
        using condSuccess scnz by (rule eq_trans)
      have condPackedNonzero: "eval_fuel n (cpx (load_T ?packed)) A = S (S d)"
        by (rule eqSubst[where a="?cond_sub" and b="cpx (load_T ?packed)" and Q="\<lambda>z. eval_fuel n z A = S (S d)", OF eqSym[OF selectCond] condNonzero])
      have elseEvalN: "eval_fuel n ?else_sub A N"
        by (rule eval_fuel_N[OF n elseSubN A])
      have elsePackedEvalN: "eval_fuel n (cpy (cpy (load_T ?packed))) A N"
        by (rule eqSubst[where a="?else_sub" and b="cpy (cpy (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A N", OF eqSym[OF selectElse] elseEvalN])
      show "eval_fuel (S n) t ?A_put = S r"
      proof (rule cases_nat_2[where x="eval_fuel n ?else_sub A"])
        show "eval_fuel n ?else_sub A N"
          by (rule elseEvalN)
      next
        assume elseTimeout: "eval_fuel n ?else_sub A = 0"
        have elsePackedTimeout: "eval_fuel n (cpy (cpy (load_T ?packed))) A = 0"
          by (rule eqSubst[where a="?else_sub" and b="cpy (cpy (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = 0", OF eqSym[OF selectElse] elseTimeout])
        have step: "eval_fuel (S n) ?packed A = eval_fuel n (cpy (cpy (load_T ?packed))) A"
          by (rule eval_fuel_ifz_nonzero[OF n tagPacked condPackedNonzero elsePackedEvalN])
        have timeout: "eval_fuel (S n) ?packed A = 0"
          using step elsePackedTimeout by (rule eq_trans)
        show "eval_fuel (S n) t ?A_put = S r"
          by (rule zero_successE[OF timeout runPacked])
      next
        fix q
        assume q: "q N" and elseSuccess: "eval_fuel n ?else_sub A = S q"
        have elsePackedSuccess: "eval_fuel n (cpy (cpy (load_T ?packed))) A = S q"
          by (rule eqSubst[where a="?else_sub" and b="cpy (cpy (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = S q", OF eqSym[OF selectElse] elseSuccess])
        have packedValue: "eval_fuel (S n) ?packed A = S q"
          by (rule eval_fuel_ifz_nonzero_value[OF n tagPacked condPackedNonzero elsePackedSuccess])
        have resultEq: "S q = S r"
          by (rule same_success[OF packedValue runPacked])
        have condNew: "eval_fuel n ?cond_orig ?A_put = S (S d)"
          by (rule IHcond[OF condNonzero])
        have elseNew: "eval_fuel n ?else_orig ?A_put = S q"
          by (rule IHelse[OF elseSuccess])
        have newValue: "eval_fuel (S n) t ?A_put = S q"
          by (rule eval_fuel_ifz_nonzero_value[OF n tg condNew elseNew])
        show "eval_fuel (S n) t ?A_put = S r"
          using newValue resultEq by (rule eq_trans)
      qed
    qed
  qed
qed

lemma eval_fuel_subst_T_appD:
  assumes n: "n N" and t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and nvar: "\<not> tag_T t = T_VAR" and nzero: "\<not> tag_T t = T_ZERO" and nsuc: "\<not> tag_T t = T_SUC" and npred: "\<not> tag_T t = T_PRED" and nifz: "\<not> tag_T t = T_IFZ"
      and run: "eval_fuel (S n) (subst_T t i s) A = S r"
      and IHarg1: "\<And>q. eval_fuel n (subst_T (cpx (cpy (load_T t))) i s) A = S q \<Longrightarrow> eval_fuel n (cpx (cpy (load_T t))) (asn_put A i v) = S q"
      and IHarg2: "\<And>q. eval_fuel n (subst_T (cpy (cpy (load_T t))) i s) A = S q \<Longrightarrow> eval_fuel n (cpy (cpy (load_T t))) (asn_put A i v) = S q"
  shows "eval_fuel (S n) t (asn_put A i v) = S r"
proof -
  let ?dfn = "cpx (load_T t)"
  let ?arg1_orig = "cpx (cpy (load_T t))"
  let ?arg2_orig = "cpy (cpy (load_T t))"
  let ?arg1_sub = "subst_T ?arg1_orig i s"
  let ?arg2_sub = "subst_T ?arg2_orig i s"
  let ?A_put = "asn_put A i v"
  let ?args = "\<langle>?arg1_sub, ?arg2_sub\<rangle>"
  let ?payload = "\<langle>?dfn, ?args\<rangle>"
  let ?packed = "pack_T T_APP ?payload"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have dfnN: "?dfn N"
    by (rule cpx_terminates[OF loadN])
  have tailN: "cpy (load_T t) N"
    by (rule cpy_terminates[OF loadN])
  have arg1OrigN: "?arg1_orig N"
    by (rule cpx_terminates[OF tailN])
  have arg2OrigN: "?arg2_orig N"
    by (rule cpy_terminates[OF tailN])
  have arg1SubN: "?arg1_sub N"
    by (rule subst_T_N[OF arg1OrigN i s])
  have arg2SubN: "?arg2_sub N"
    by (rule subst_T_N[OF arg2OrigN i s])
  have argsN: "?args N"
    using arg1SubN arg2SubN by simp
  have payloadN: "?payload N"
    using dfnN argsN by simp
  have packedN: "?packed N"
    by (rule pack_T_N[OF _ payloadN], simp)
  have sub: "subst_T t i s = ?packed"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI2Eq[OF nzero packedN])
    apply (rule condI2Eq[OF nsuc packedN])
    apply (rule condI2Eq[OF npred packedN])
    apply (rule condI2Eq[OF nifz packedN])
    using packedN by simp
  have tagPacked: "tag_T ?packed = T_APP"
    by (rule tag_pack_T[OF _ payloadN], simp)
  have packedNvar: "\<not> tag_T ?packed = T_VAR"
    using tagPacked by simp
  have packedNzero: "\<not> tag_T ?packed = T_ZERO"
    using tagPacked by simp
  have packedNsuc: "\<not> tag_T ?packed = T_SUC"
    using tagPacked by simp
  have packedNpred: "\<not> tag_T ?packed = T_PRED"
    using tagPacked by simp
  have packedNifz: "\<not> tag_T ?packed = T_IFZ"
    using tagPacked by simp
  have loadPacked: "load_T ?packed = ?payload"
    by (rule load_pack_T[OF _ payloadN], simp)
  have payloadDfn: "cpx ?payload = ?dfn"
    by (rule cpx_proj[OF dfnN argsN])
  have payloadArgs: "cpy ?payload = ?args"
    by (rule cpy_proj[OF dfnN argsN])
  have argsArg1: "cpx ?args = ?arg1_sub"
    by (rule cpx_proj[OF arg1SubN arg2SubN])
  have argsArg2: "cpy ?args = ?arg2_sub"
    by (rule cpy_proj[OF arg1SubN arg2SubN])
  have selectDfn: "cpx (load_T ?packed) = ?dfn"
    by (rule eqSubst[where a="?payload" and b="load_T ?packed" and Q="\<lambda>z. cpx z = ?dfn", OF eqSym[OF loadPacked] payloadDfn])
  have selectArgs: "cpy (load_T ?packed) = ?args"
    by (rule eqSubst[where a="?payload" and b="load_T ?packed" and Q="\<lambda>z. cpy z = ?args", OF eqSym[OF loadPacked] payloadArgs])
  have selectArg1: "cpx (cpy (load_T ?packed)) = ?arg1_sub"
    by (rule eqSubst[where a="?args" and b="cpy (load_T ?packed)" and Q="\<lambda>z. cpx z = ?arg1_sub", OF eqSym[OF selectArgs] argsArg1])
  have selectArg2: "cpy (cpy (load_T ?packed)) = ?arg2_sub"
    by (rule eqSubst[where a="?args" and b="cpy (load_T ?packed)" and Q="\<lambda>z. cpy z = ?arg2_sub", OF eqSym[OF selectArgs] argsArg2])
  have runPacked: "eval_fuel (S n) ?packed A = S r"
    by (rule eqSubst[where a="subst_T t i s" and b="?packed" and Q="\<lambda>z. eval_fuel (S n) z A = S r", OF sub run])
  have arg1EvalN: "eval_fuel n ?arg1_sub A N"
    by (rule eval_fuel_N[OF n arg1SubN A])
  show ?thesis
  proof (rule cases_nat_2[where x="eval_fuel n ?arg1_sub A"])
    show "eval_fuel n ?arg1_sub A N"
      by (rule arg1EvalN)
  next
    assume arg1Timeout: "eval_fuel n ?arg1_sub A = 0"
    have packedArg1Timeout: "eval_fuel n (cpx (cpy (load_T ?packed))) A = 0"
      by (rule eqSubst[where a="?arg1_sub" and b="cpx (cpy (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = 0", OF eqSym[OF selectArg1] arg1Timeout])
    have timeout: "eval_fuel (S n) ?packed A = 0"
      by (rule eval_fuel_app_arg1_timeout[OF n packedNvar packedNzero packedNsuc packedNpred packedNifz packedArg1Timeout])
    show "eval_fuel (S n) t ?A_put = S r"
      by (rule zero_successE[OF timeout runPacked])
  next
    fix x
    assume x: "x N" and arg1Success: "eval_fuel n ?arg1_sub A = S x"
    have packedArg1Success: "eval_fuel n (cpx (cpy (load_T ?packed))) A = S x"
      by (rule eqSubst[where a="?arg1_sub" and b="cpx (cpy (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = S x", OF eqSym[OF selectArg1] arg1Success])
    have arg2EvalN: "eval_fuel n ?arg2_sub A N"
      by (rule eval_fuel_N[OF n arg2SubN A])
    show "eval_fuel (S n) t ?A_put = S r"
    proof (rule cases_nat_2[where x="eval_fuel n ?arg2_sub A"])
      show "eval_fuel n ?arg2_sub A N"
        by (rule arg2EvalN)
    next
      assume arg2Timeout: "eval_fuel n ?arg2_sub A = 0"
      have packedArg2Timeout: "eval_fuel n (cpy (cpy (load_T ?packed))) A = 0"
        by (rule eqSubst[where a="?arg2_sub" and b="cpy (cpy (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = 0", OF eqSym[OF selectArg2] arg2Timeout])
      have timeout: "eval_fuel (S n) ?packed A = 0"
        by (rule eval_fuel_app_arg2_timeout[OF n packedNvar packedNzero packedNsuc packedNpred packedNifz packedArg1Success packedArg2Timeout])
      show "eval_fuel (S n) t ?A_put = S r"
        by (rule zero_successE[OF timeout runPacked])
    next
      fix y
      assume y: "y N" and arg2Success: "eval_fuel n ?arg2_sub A = S y"
      have packedArg2Success: "eval_fuel n (cpy (cpy (load_T ?packed))) A = S y"
        by (rule eqSubst[where a="?arg2_sub" and b="cpy (cpy (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = S y", OF eqSym[OF selectArg2] arg2Success])
      have appAsnN: "x \<triangleright> y \<triangleright> Nil N"
        using x y by simp
      have bodyEvalN: "eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) N"
        by (rule eval_fuel_N[OF n nth_N'[OF dfns_N dfnN] appAsnN])
      show "eval_fuel (S n) t ?A_put = S r"
      proof (rule cases_nat_2[where x="eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil)"])
        show "eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) N"
          by (rule bodyEvalN)
      next
        assume bodyTimeout: "eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) = 0"
        have packedBodyTimeout: "eval_fuel n (nth (cpx (load_T ?packed)) dfns) (x \<triangleright> y \<triangleright> Nil) = 0"
          by (rule eqSubst[where a="?dfn" and b="cpx (load_T ?packed)" and Q="\<lambda>z. eval_fuel n (nth z dfns) (x \<triangleright> y \<triangleright> Nil) = 0", OF eqSym[OF selectDfn] bodyTimeout])
        have timeout: "eval_fuel (S n) ?packed A = 0"
          by (rule eval_fuel_app_body_timeout[OF n packedNvar packedNzero packedNsuc packedNpred packedNifz packedArg1Success packedArg2Success packedBodyTimeout])
        show "eval_fuel (S n) t ?A_put = S r"
          by (rule zero_successE[OF timeout runPacked])
      next
        fix q
        assume q: "q N" and bodySuccess: "eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) = S q"
        have packedBodySuccess: "eval_fuel n (nth (cpx (load_T ?packed)) dfns) (x \<triangleright> y \<triangleright> Nil) = S q"
          by (rule eqSubst[where a="?dfn" and b="cpx (load_T ?packed)" and Q="\<lambda>z. eval_fuel n (nth z dfns) (x \<triangleright> y \<triangleright> Nil) = S q", OF eqSym[OF selectDfn] bodySuccess])
        have packedValue: "eval_fuel (S n) ?packed A = S q"
          by (rule eval_fuel_app_value[OF n packedNvar packedNzero packedNsuc packedNpred packedNifz packedArg1Success packedArg2Success packedBodySuccess])
        have resultEq: "S q = S r"
          by (rule same_success[OF packedValue runPacked])
        have arg1New: "eval_fuel n ?arg1_orig ?A_put = S x"
          by (rule IHarg1[OF arg1Success])
        have arg2New: "eval_fuel n ?arg2_orig ?A_put = S y"
          by (rule IHarg2[OF arg2Success])
        have newValue: "eval_fuel (S n) t ?A_put = S q"
          by (rule eval_fuel_app_value[OF n nvar nzero nsuc npred nifz arg1New arg2New bodySuccess])
        show "eval_fuel (S n) t ?A_put = S r"
          using newValue resultEq by (rule eq_trans)
      qed
    qed
  qed
qed

lemma eval_fuel_subst_TD:
  assumes k: "k N" and t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N" and evs: "evals s A v" and run: "eval_fuel k (subst_T t i s) A = S r"
  shows "eval_fuel k t (asn_put A i v) = S r"
proof -
  have main: "\<forall>u. \<forall>q. (eval_fuel k (subst_T u i s) A = S q) \<longrightarrow> eval_fuel k u (asn_put A i v) = S q"
  proof (rule ind[OF k])
    show "\<forall>u. \<forall>q. (eval_fuel 0 (subst_T u i s) A = S q) \<longrightarrow> eval_fuel 0 u (asn_put A i v) = S q"
    proof (rule forallI)
      fix u
      assume u: "u N"
      show "\<forall>q. (eval_fuel 0 (subst_T u i s) A = S q) \<longrightarrow> eval_fuel 0 u (asn_put A i v) = S q"
      proof (rule forallI)
        fix q
        assume q: "q N"
        show "(eval_fuel 0 (subst_T u i s) A = S q) \<longrightarrow> eval_fuel 0 u (asn_put A i v) = S q"
        proof (rule implI)
          have substN: "subst_T u i s N"
            by (rule subst_T_N[OF u i s])
          have evalN: "eval_fuel 0 (subst_T u i s) A N"
            by (rule eval_fuel_N[OF nat0 substN A])
          have sqN: "S q N"
            by (rule natS[OF q])
          show "(eval_fuel 0 (subst_T u i s) A = S q) B"
            by (rule eqBool[OF evalN sqN])
        next
          assume success: "eval_fuel 0 (subst_T u i s) A = S q"
          have timeout: "eval_fuel 0 (subst_T u i s) A = 0"
            by (rule eval_fuel_zero)
          show "eval_fuel 0 u (asn_put A i v) = S q"
            by (rule zero_successE[OF timeout success])
        qed
      qed
    qed
  next
    fix n
    assume n: "n N"
    assume IH: "\<forall>u. \<forall>q. (eval_fuel n (subst_T u i s) A = S q) \<longrightarrow> eval_fuel n u (asn_put A i v) = S q"
    show "\<forall>u. \<forall>q. (eval_fuel (S n) (subst_T u i s) A = S q) \<longrightarrow> eval_fuel (S n) u (asn_put A i v) = S q"
    proof (rule forallI)
      fix u
      assume u: "u N"
      show "\<forall>q. (eval_fuel (S n) (subst_T u i s) A = S q) \<longrightarrow> eval_fuel (S n) u (asn_put A i v) = S q"
      proof (rule forallI)
        fix q
        assume q: "q N"
        show "(eval_fuel (S n) (subst_T u i s) A = S q) \<longrightarrow> eval_fuel (S n) u (asn_put A i v) = S q"
        proof (rule implI)
          have sn: "S n N"
            by (rule natS[OF n])
          have substN: "subst_T u i s N"
            by (rule subst_T_N[OF u i s])
          have evalN: "eval_fuel (S n) (subst_T u i s) A N"
            by (rule eval_fuel_N[OF sn substN A])
          have sqN: "S q N"
            by (rule natS[OF q])
          show "(eval_fuel (S n) (subst_T u i s) A = S q) B"
            by (rule eqBool[OF evalN sqN])
        next
          assume result: "eval_fuel (S n) (subst_T u i s) A = S q"
          have sn: "S n N"
            by (rule natS[OF n])
          have IHmeta: "\<And>w z. w N \<Longrightarrow> eval_fuel n (subst_T w i s) A = S z \<Longrightarrow> eval_fuel n w (asn_put A i v) = S z"
          proof -
            fix w z
            assume w: "w N" and success: "eval_fuel n (subst_T w i s) A = S z"
            have substN: "subst_T w i s N"
              by (rule subst_T_N[OF w i s])
            have z: "z N"
              by (rule eval_fuel_result_N[OF n substN A success])
            have IHw: "\<forall>z. (eval_fuel n (subst_T w i s) A = S z) \<longrightarrow> eval_fuel n w (asn_put A i v) = S z"
              by (rule forallE[where a=w, OF IH w])
            have IHwz: "(eval_fuel n (subst_T w i s) A = S z) \<longrightarrow> eval_fuel n w (asn_put A i v) = S z"
              by (rule forallE[where a=z, OF IHw z])
            show "eval_fuel n w (asn_put A i v) = S z"
              using IHwz success by (rule implE)
          qed
          have loadN: "load_T u N"
            by (rule load_T_N[OF u])
          have condN: "cpx (load_T u) N"
            by (rule cpx_terminates[OF loadN])
          have tailN: "cpy (load_T u) N"
            by (rule cpy_terminates[OF loadN])
          have leftN: "cpx (cpy (load_T u)) N"
            by (rule cpx_terminates[OF tailN])
          have rightN: "cpy (cpy (load_T u)) N"
            by (rule cpy_terminates[OF tailN])
          have IHload: "\<And>z. eval_fuel n (subst_T (load_T u) i s) A = S z \<Longrightarrow> eval_fuel n (load_T u) (asn_put A i v) = S z"
          proof -
            fix z
            assume success: "eval_fuel n (subst_T (load_T u) i s) A = S z"
            show "eval_fuel n (load_T u) (asn_put A i v) = S z"
              by (rule IHmeta[OF loadN success])
          qed
          have IHcond: "\<And>z. eval_fuel n (subst_T (cpx (load_T u)) i s) A = S z \<Longrightarrow> eval_fuel n (cpx (load_T u)) (asn_put A i v) = S z"
          proof -
            fix z
            assume success: "eval_fuel n (subst_T (cpx (load_T u)) i s) A = S z"
            show "eval_fuel n (cpx (load_T u)) (asn_put A i v) = S z"
              by (rule IHmeta[OF condN success])
          qed
          have IHleft: "\<And>z. eval_fuel n (subst_T (cpx (cpy (load_T u))) i s) A = S z \<Longrightarrow> eval_fuel n (cpx (cpy (load_T u))) (asn_put A i v) = S z"
          proof -
            fix z
            assume success: "eval_fuel n (subst_T (cpx (cpy (load_T u))) i s) A = S z"
            show "eval_fuel n (cpx (cpy (load_T u))) (asn_put A i v) = S z"
              by (rule IHmeta[OF leftN success])
          qed
          have IHright: "\<And>z. eval_fuel n (subst_T (cpy (cpy (load_T u))) i s) A = S z \<Longrightarrow> eval_fuel n (cpy (cpy (load_T u))) (asn_put A i v) = S z"
          proof -
            fix z
            assume success: "eval_fuel n (subst_T (cpy (cpy (load_T u))) i s) A = S z"
            show "eval_fuel n (cpy (cpy (load_T u))) (asn_put A i v) = S z"
              by (rule IHmeta[OF rightN success])
          qed
          have tagN: "tag_T u N"
            by (rule tag_T_N[OF u])
          have varB: "(tag_T u = T_VAR) B"
            by (rule eqBool[OF tagN], simp)
          have zeroB: "(tag_T u = T_ZERO) B"
            by (rule eqBool[OF tagN], simp)
          have sucB: "(tag_T u = T_SUC) B"
            by (rule eqBool[OF tagN], simp)
          have predB: "(tag_T u = T_PRED) B"
            by (rule eqBool[OF tagN], simp)
          have ifzB: "(tag_T u = T_IFZ) B"
            by (rule eqBool[OF tagN], simp)
          show "eval_fuel (S n) u (asn_put A i v) = S q"
          proof (rule cases_bool[where q="tag_T u = T_VAR"])
            show "(tag_T u = T_VAR) B"
              by (rule varB)
          next
            assume tg: "tag_T u = T_VAR"
            show "eval_fuel (S n) u (asn_put A i v) = S q"
              by (rule eval_fuel_subst_T_varD[OF sn u i s A v evs tg result])
          next
            assume nvar: "\<not> tag_T u = T_VAR"
            show "eval_fuel (S n) u (asn_put A i v) = S q"
            proof (rule cases_bool[where q="tag_T u = T_ZERO"])
              show "(tag_T u = T_ZERO) B"
                by (rule zeroB)
            next
              assume tg: "tag_T u = T_ZERO"
              show "eval_fuel (S n) u (asn_put A i v) = S q"
                by (rule eval_fuel_subst_T_zeroD[OF sn u i s A v evs tg result])
            next
              assume nzero: "\<not> tag_T u = T_ZERO"
              show "eval_fuel (S n) u (asn_put A i v) = S q"
              proof (rule cases_bool[where q="tag_T u = T_SUC"])
                show "(tag_T u = T_SUC) B"
                  by (rule sucB)
              next
                assume tg: "tag_T u = T_SUC"
                show "eval_fuel (S n) u (asn_put A i v) = S q"
                  by (rule eval_fuel_subst_T_sucD[OF n u i s A v tg result IHload])
              next
                assume nsuc: "\<not> tag_T u = T_SUC"
                show "eval_fuel (S n) u (asn_put A i v) = S q"
                proof (rule cases_bool[where q="tag_T u = T_PRED"])
                  show "(tag_T u = T_PRED) B"
                    by (rule predB)
                next
                  assume tg: "tag_T u = T_PRED"
                  show "eval_fuel (S n) u (asn_put A i v) = S q"
                    by (rule eval_fuel_subst_T_predD[OF n u i s A v tg result IHload])
                next
                  assume npred: "\<not> tag_T u = T_PRED"
                  show "eval_fuel (S n) u (asn_put A i v) = S q"
                  proof (rule cases_bool[where q="tag_T u = T_IFZ"])
                    show "(tag_T u = T_IFZ) B"
                      by (rule ifzB)
                  next
                    assume tg: "tag_T u = T_IFZ"
                    show "eval_fuel (S n) u (asn_put A i v) = S q"
                      by (rule eval_fuel_subst_T_ifzD[OF n u i s A v tg result IHcond IHleft IHright])
                  next
                    assume nifz: "\<not> tag_T u = T_IFZ"
                    show "eval_fuel (S n) u (asn_put A i v) = S q"
                      by (rule eval_fuel_subst_T_appD[OF n u i s A v nvar nzero nsuc npred nifz result IHleft IHright])
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  have substN: "subst_T t i s N"
    by (rule subst_T_N[OF t i s])
  have r: "r N"
    by (rule eval_fuel_result_N[OF k substN A run])
  have mainT: "\<forall>q. (eval_fuel k (subst_T t i s) A = S q) \<longrightarrow> eval_fuel k t (asn_put A i v) = S q"
    by (rule forallE[where a=t, OF main t])
  have mainR: "(eval_fuel k (subst_T t i s) A = S r) \<longrightarrow> eval_fuel k t (asn_put A i v) = S r"
    by (rule forallE[where a=r, OF mainT r])
  show ?thesis
    using mainR run by (rule implE)
qed

lemma evals_subst_TD:
  assumes t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and evs: "evals s A v" and evsub: "evals (subst_T t i s) A r"
  shows "evals t (asn_put A i v) r"
proof -
  show ?thesis
    using evsub
  proof (rule evalsE)
    fix k
    assume k: "k N" and run: "eval_fuel k (subst_T t i s) A = S r"
    have transported: "eval_fuel k t (asn_put A i v) = S r"
      by (rule eval_fuel_subst_TD[OF k t i s A v evs run])
    show "evals t (asn_put A i v) r"
      by (rule evalsI[OF k transported])
  qed
qed

lemma evals_subst_T_result:
  assumes t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and evs: "evals s A v" and evsub: "evals (subst_T t i s) A r"
      and evt: "evals t (asn_put A i v) q"
  shows "r = q"
proof -
  have transported: "evals t (asn_put A i v) r"
    by (rule evals_subst_TD[OF t i s A v evs evsub])
  have putN: "asn_put A i v N"
    by (rule asn_put_N[OF A i v])
  show ?thesis
    by (rule evals_functional[OF t putN transported evt])
qed

lemma eval_fuel_subst_T_varI:
  assumes m: "m N" and n: "n N" and t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and srun: "eval_fuel m s A = S v" and tg: "tag_T t = T_VAR"
      and run: "eval_fuel (S n) t (asn_put A i v) = S r"
  shows "eval_fuel (m + S n) (subst_T t i s) A = S r"
proof -
  have sn: "S n N"
    by (rule natS[OF n])
  have putN: "asn_put A i v N"
    by (rule asn_put_N[OF A i v])
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have loadEqB: "(load_T t = i) B"
    by (rule eqBool[OF loadN i])
  show ?thesis
  proof (rule cases_bool[where q="load_T t = i"])
    show "(load_T t = i) B"
      by (rule loadEqB)
  next
    assume li: "load_T t = i"
    have sub: "subst_T t i s = s"
      by (rule subst_T_var_same[OF t i s tg li])
    have nthI: "nth i (asn_put A i v) = v"
      by (rule nth_put_eq[OF A i v])
    have nthLoad: "nth (load_T t) (asn_put A i v) = v"
      by (rule eqSubst[where a=i and b="load_T t" and Q="\<lambda>z. nth z (asn_put A i v) = v", OF eqSym[OF li] nthI])
    have nthLoadN: "nth (load_T t) (asn_put A i v) N"
      by (rule nth_N'[OF putN loadN])
    have originalValue0: "eval_fuel (S n) t (asn_put A i v) = S (nth (load_T t) (asn_put A i v))"
      by (rule eval_fuel_var[OF n tg nthLoadN])
    have nthValue: "S (nth (load_T t) (asn_put A i v)) = S v"
      by (rule sucCong[OF nthLoad])
    have originalValue: "eval_fuel (S n) t (asn_put A i v) = S v"
      using originalValue0 nthValue by (rule eq_trans)
    have resultEq: "S v = S r"
      by (rule same_success[OF originalValue run])
    have lifted: "eval_fuel (m + S n) s A = S v"
      by (rule eval_fuel_success_add[OF m sn s A srun])
    have liftedSub: "eval_fuel (m + S n) (subst_T t i s) A = S v"
      by (rule eqSubst[where a=s and b="subst_T t i s" and Q="\<lambda>z. eval_fuel (m + S n) z A = S v", OF eqSym[OF sub] lifted])
    show "eval_fuel (m + S n) (subst_T t i s) A = S r"
      using liftedSub resultEq by (rule eq_trans)
   next
    assume li: "\<not> load_T t = i"
    have sub: "subst_T t i s = t"
      by (rule subst_T_var_other[OF t i s tg li])
    have nthPutN: "nth (load_T t) (asn_put A i v) N"
      by (rule nth_N'[OF putN loadN])
    have nthAN: "nth (load_T t) A N"
      by (rule nth_N'[OF A loadN])
    have nthSame: "nth (load_T t) (asn_put A i v) = nth (load_T t) A"
      by (rule nth_put_ne[OF A i v loadN li])
    have putValue: "eval_fuel (S n) t (asn_put A i v) = S (nth (load_T t) (asn_put A i v))"
      by (rule eval_fuel_var[OF n tg nthPutN])
    have putResult: "S (nth (load_T t) (asn_put A i v)) = S r"
      by (rule same_success[OF putValue run])
    have oldValue: "eval_fuel (S n) t A = S (nth (load_T t) A)"
      by (rule eval_fuel_var[OF n tg nthAN])
    have valueEq: "S (nth (load_T t) A) = S (nth (load_T t) (asn_put A i v))"
      by (rule sucCong[OF eqSym[OF nthSame]])
    have oldPutValue: "eval_fuel (S n) t A = S (nth (load_T t) (asn_put A i v))"
      using oldValue valueEq by (rule eq_trans)
    have oldRun: "eval_fuel (S n) t A = S r"
      using oldPutValue putResult by (rule eq_trans)
    have lifted0: "eval_fuel (S n + m) t A = S r"
      by (rule eval_fuel_success_add[OF sn m t A oldRun])
    have fuelEq: "S n + m = m + S n"
      by (rule add_comm[OF sn m])
    have lifted: "eval_fuel (m + S n) t A = S r"
      by (rule eqSubst[where a="S n + m" and b="m + S n" and Q="\<lambda>z. eval_fuel z t A = S r", OF fuelEq lifted0])
    show "eval_fuel (m + S n) (subst_T t i s) A = S r"
      by (rule eqSubst[where a=t and b="subst_T t i s" and Q="\<lambda>z. eval_fuel (m + S n) z A = S r", OF eqSym[OF sub] lifted])
  qed
qed

lemma eval_fuel_subst_T_zeroI:
  assumes m: "m N" and n: "n N" and t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and srun: "eval_fuel m s A = S v" and tg: "tag_T t = T_ZERO"
      and run: "eval_fuel (S n) t (asn_put A i v) = S r"
  shows "eval_fuel (m + S n) (subst_T t i s) A = S r"
proof -
  let ?packed = "pack_T T_ZERO 0"
  have mnN: "m + n N"
    by (rule add_terminates[OF m n])
  have originalValue: "eval_fuel (S n) t (asn_put A i v) = S 0"
    by (rule eval_fuel_zero_step[OF n tg])
  have resultEq: "S 0 = S r"
    by (rule same_success[OF originalValue run])
  have packedN: "?packed N"
    by (rule pack_T_N[OF _ nat0], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have sub: "subst_T t i s = ?packed"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI1Eq[OF tg packedN])
    using packedN by simp
  have tagPacked: "tag_T ?packed = T_ZERO"
    by (rule tag_pack_T[OF _ nat0], simp)
  have packedValue: "eval_fuel (S (m + n)) ?packed A = S 0"
    by (rule eval_fuel_zero_step[OF mnN tagPacked])
  have fuelEq: "m + S n = S (m + n)"
    by (rule add_succ[OF m n])
  have lifted: "eval_fuel (m + S n) ?packed A = S 0"
    by (rule eqSubst[where a="S (m + n)" and b="m + S n" and Q="\<lambda>z. eval_fuel z ?packed A = S 0", OF eqSym[OF fuelEq] packedValue])
  have liftedSub: "eval_fuel (m + S n) (subst_T t i s) A = S 0"
    by (rule eqSubst[where a="?packed" and b="subst_T t i s" and Q="\<lambda>z. eval_fuel (m + S n) z A = S 0", OF eqSym[OF sub] lifted])
  show "eval_fuel (m + S n) (subst_T t i s) A = S r"
    using liftedSub resultEq by (rule eq_trans)
qed

lemma eval_fuel_subst_T_sucI:
  assumes m: "m N" and n: "n N" and t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and srun: "eval_fuel m s A = S v" and tg: "tag_T t = T_SUC"
      and run: "eval_fuel (S n) t (asn_put A i v) = S r"
      and IH: "\<And>q. eval_fuel n (load_T t) (asn_put A i v) = S q \<Longrightarrow> eval_fuel (m + n) (subst_T (load_T t) i s) A = S q"
  shows "eval_fuel (m + S n) (subst_T t i s) A = S r"
proof -
  let ?child_orig = "load_T t"
  let ?child_sub = "subst_T ?child_orig i s"
  let ?packed = "pack_T T_SUC ?child_sub"
  let ?A_put = "asn_put A i v"
  have childOrigN: "?child_orig N"
    by (rule load_T_N[OF t])
  have childSubN: "?child_sub N"
    by (rule subst_T_N[OF childOrigN i s])
  have mnN: "m + n N"
    by (rule add_terminates[OF m n])
  have packedN: "?packed N"
    by (rule pack_T_N[OF _ childSubN], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have sub: "subst_T t i s = ?packed"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI2Eq[OF nzero packedN])
    apply (rule condI1Eq[OF tg packedN])
    using packedN by simp
  have tagPacked: "tag_T ?packed = T_SUC"
    by (rule tag_pack_T[OF _ childSubN], simp)
  have loadPacked: "load_T ?packed = ?child_sub"
    by (rule load_pack_T[OF _ childSubN], simp)
  have childEvalN: "eval_fuel n ?child_orig ?A_put N"
    by (rule eval_fuel_N[OF n childOrigN asn_put_N[OF A i v]])
  show ?thesis
  proof (rule cases_nat_2[where x="eval_fuel n ?child_orig ?A_put"])
    show "eval_fuel n ?child_orig ?A_put N"
      by (rule childEvalN)
  next
    assume childTimeout: "eval_fuel n ?child_orig ?A_put = 0"
    have timeout: "eval_fuel (S n) t ?A_put = 0"
      by (rule eval_fuel_suc_timeout[OF n tg childTimeout])
    show "eval_fuel (m + S n) (subst_T t i s) A = S r"
      by (rule zero_successE[OF timeout run])
  next
    fix q
    assume q: "q N" and childSuccess: "eval_fuel n ?child_orig ?A_put = S q"
    have originalValue: "eval_fuel (S n) t ?A_put = S (S q)"
      by (rule eval_fuel_suc_value[OF n tg childSuccess])
    have resultEq: "S (S q) = S r"
      by (rule same_success[OF originalValue run])
    have childSubSuccess: "eval_fuel (m + n) ?child_sub A = S q"
      by (rule IH[OF childSuccess])
    have packedChildSuccess: "eval_fuel (m + n) (load_T ?packed) A = S q"
      by (rule eqSubst[where a="?child_sub" and b="load_T ?packed" and Q="\<lambda>z. eval_fuel (m + n) z A = S q", OF eqSym[OF loadPacked] childSubSuccess])
    have packedValue: "eval_fuel (S (m + n)) ?packed A = S (S q)"
      by (rule eval_fuel_suc_value[OF mnN tagPacked packedChildSuccess])
    have fuelEq: "m + S n = S (m + n)"
      by (rule add_succ[OF m n])
    have lifted: "eval_fuel (m + S n) ?packed A = S (S q)"
      by (rule eqSubst[where a="S (m + n)" and b="m + S n" and Q="\<lambda>z. eval_fuel z ?packed A = S (S q)", OF eqSym[OF fuelEq] packedValue])
    have liftedSub: "eval_fuel (m + S n) (subst_T t i s) A = S (S q)"
      by (rule eqSubst[where a="?packed" and b="subst_T t i s" and Q="\<lambda>z. eval_fuel (m + S n) z A = S (S q)", OF eqSym[OF sub] lifted])
    show "eval_fuel (m + S n) (subst_T t i s) A = S r"
      using liftedSub resultEq by (rule eq_trans)
  qed
qed

lemma eval_fuel_subst_T_predI:
  assumes m: "m N" and n: "n N" and t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and srun: "eval_fuel m s A = S v" and tg: "tag_T t = T_PRED"
      and run: "eval_fuel (S n) t (asn_put A i v) = S r"
      and IH: "\<And>q. eval_fuel n (load_T t) (asn_put A i v) = S q \<Longrightarrow> eval_fuel (m + n) (subst_T (load_T t) i s) A = S q"
  shows "eval_fuel (m + S n) (subst_T t i s) A = S r"
proof -
  let ?child_orig = "load_T t"
  let ?child_sub = "subst_T ?child_orig i s"
  let ?packed = "pack_T T_PRED ?child_sub"
  let ?A_put = "asn_put A i v"
  have childOrigN: "?child_orig N"
    by (rule load_T_N[OF t])
  have childSubN: "?child_sub N"
    by (rule subst_T_N[OF childOrigN i s])
  have mnN: "m + n N"
    by (rule add_terminates[OF m n])
  have packedN: "?packed N"
    by (rule pack_T_N[OF _ childSubN], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have sub: "subst_T t i s = ?packed"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI2Eq[OF nzero packedN])
    apply (rule condI2Eq[OF nsuc packedN])
    apply (rule condI1Eq[OF tg packedN])
    using packedN by simp
  have tagPacked: "tag_T ?packed = T_PRED"
    by (rule tag_pack_T[OF _ childSubN], simp)
  have loadPacked: "load_T ?packed = ?child_sub"
    by (rule load_pack_T[OF _ childSubN], simp)
  have childEvalN: "eval_fuel n ?child_orig ?A_put N"
    by (rule eval_fuel_N[OF n childOrigN asn_put_N[OF A i v]])
  show ?thesis
  proof (rule cases_nat_2[where x="eval_fuel n ?child_orig ?A_put"])
    show "eval_fuel n ?child_orig ?A_put N"
      by (rule childEvalN)
  next
    assume childTimeout: "eval_fuel n ?child_orig ?A_put = 0"
    have timeout: "eval_fuel (S n) t ?A_put = 0"
      by (rule eval_fuel_pred_timeout[OF n tg childTimeout])
    show "eval_fuel (m + S n) (subst_T t i s) A = S r"
      by (rule zero_successE[OF timeout run])
  next
    fix q
    assume q: "q N" and childSuccess: "eval_fuel n ?child_orig ?A_put = S q"
    have originalValue: "eval_fuel (S n) t ?A_put = S (P q)"
      by (rule eval_fuel_pred_value[OF n tg childSuccess])
    have resultEq: "S (P q) = S r"
      by (rule same_success[OF originalValue run])
    have childSubSuccess: "eval_fuel (m + n) ?child_sub A = S q"
      by (rule IH[OF childSuccess])
    have packedChildSuccess: "eval_fuel (m + n) (load_T ?packed) A = S q"
      by (rule eqSubst[where a="?child_sub" and b="load_T ?packed" and Q="\<lambda>z. eval_fuel (m + n) z A = S q", OF eqSym[OF loadPacked] childSubSuccess])
    have packedValue: "eval_fuel (S (m + n)) ?packed A = S (P q)"
      by (rule eval_fuel_pred_value[OF mnN tagPacked packedChildSuccess])
    have fuelEq: "m + S n = S (m + n)"
      by (rule add_succ[OF m n])
    have lifted: "eval_fuel (m + S n) ?packed A = S (P q)"
      by (rule eqSubst[where a="S (m + n)" and b="m + S n" and Q="\<lambda>z. eval_fuel z ?packed A = S (P q)", OF eqSym[OF fuelEq] packedValue])
    have liftedSub: "eval_fuel (m + S n) (subst_T t i s) A = S (P q)"
      by (rule eqSubst[where a="?packed" and b="subst_T t i s" and Q="\<lambda>z. eval_fuel (m + S n) z A = S (P q)", OF eqSym[OF sub] lifted])
    show "eval_fuel (m + S n) (subst_T t i s) A = S r"
      using liftedSub resultEq by (rule eq_trans)
  qed
qed

lemma eval_fuel_subst_T_ifzI:
  assumes m: "m N" and n: "n N" and t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and srun: "eval_fuel m s A = S v" and tg: "tag_T t = T_IFZ"
      and run: "eval_fuel (S n) t (asn_put A i v) = S r"
      and IHcond: "\<And>q. eval_fuel n (cpx (load_T t)) (asn_put A i v) = S q \<Longrightarrow> eval_fuel (m + n) (subst_T (cpx (load_T t)) i s) A = S q"
      and IHthen: "\<And>q. eval_fuel n (cpx (cpy (load_T t))) (asn_put A i v) = S q \<Longrightarrow> eval_fuel (m + n) (subst_T (cpx (cpy (load_T t))) i s) A = S q"
      and IHelse: "\<And>q. eval_fuel n (cpy (cpy (load_T t))) (asn_put A i v) = S q \<Longrightarrow> eval_fuel (m + n) (subst_T (cpy (cpy (load_T t))) i s) A = S q"
  shows "eval_fuel (m + S n) (subst_T t i s) A = S r"
proof -
  let ?cond_orig = "cpx (load_T t)"
  let ?then_orig = "cpx (cpy (load_T t))"
  let ?else_orig = "cpy (cpy (load_T t))"
  let ?cond_sub = "subst_T ?cond_orig i s"
  let ?then_sub = "subst_T ?then_orig i s"
  let ?else_sub = "subst_T ?else_orig i s"
  let ?A_put = "asn_put A i v"
  let ?args = "\<langle>?then_sub, ?else_sub\<rangle>"
  let ?payload = "\<langle>?cond_sub, ?args\<rangle>"
  let ?packed = "pack_T T_IFZ ?payload"
  have putN: "?A_put N"
    by (rule asn_put_N[OF A i v])
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have condOrigN: "?cond_orig N"
    by (rule cpx_terminates[OF loadN])
  have tailN: "cpy (load_T t) N"
    by (rule cpy_terminates[OF loadN])
  have thenOrigN: "?then_orig N"
    by (rule cpx_terminates[OF tailN])
  have elseOrigN: "?else_orig N"
    by (rule cpy_terminates[OF tailN])
  have condSubN: "?cond_sub N"
    by (rule subst_T_N[OF condOrigN i s])
  have thenSubN: "?then_sub N"
    by (rule subst_T_N[OF thenOrigN i s])
  have elseSubN: "?else_sub N"
    by (rule subst_T_N[OF elseOrigN i s])
  have mnN: "m + n N"
    by (rule add_terminates[OF m n])
  have argsN: "?args N"
    using thenSubN elseSubN by simp
  have payloadN: "?payload N"
    using condSubN argsN by simp
  have packedN: "?packed N"
    by (rule pack_T_N[OF _ payloadN], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have npred: "\<not> tag_T t = T_PRED"
    using tg by simp
  have sub: "subst_T t i s = ?packed"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI2Eq[OF nzero packedN])
    apply (rule condI2Eq[OF nsuc packedN])
    apply (rule condI2Eq[OF npred packedN])
    apply (rule condI1Eq[OF tg packedN])
    using packedN by simp
  have tagPacked: "tag_T ?packed = T_IFZ"
    by (rule tag_pack_T[OF _ payloadN], simp)
  have loadPacked: "load_T ?packed = ?payload"
    by (rule load_pack_T[OF _ payloadN], simp)
  have payloadCond: "cpx ?payload = ?cond_sub"
    by (rule cpx_proj[OF condSubN argsN])
  have payloadArgs: "cpy ?payload = ?args"
    by (rule cpy_proj[OF condSubN argsN])
  have argsThen: "cpx ?args = ?then_sub"
    by (rule cpx_proj[OF thenSubN elseSubN])
  have argsElse: "cpy ?args = ?else_sub"
    by (rule cpy_proj[OF thenSubN elseSubN])
  have selectCond: "cpx (load_T ?packed) = ?cond_sub"
    by (rule eqSubst[where a="?payload" and b="load_T ?packed" and Q="\<lambda>z. cpx z = ?cond_sub", OF eqSym[OF loadPacked] payloadCond])
  have selectCond: "hyp_of (load_T ?packed) = ?cond_sub"
    by (rule eqSubst[where a="?payload" and b="load_T ?packed" and Q="\<lambda>z. hyp_of z = ?cond_sub", OF eqSym[OF loadPacked] payloadCond])
  have selectArgs: "conc_of (load_T ?packed) = ?args"
    by (rule eqSubst[where a="?payload" and b="load_T ?packed" and Q="\<lambda>z. conc_of z = ?args", OF eqSym[OF loadPacked] payloadArgs])
  have selectThen: "cpx (cpy (load_T ?packed)) = ?then_sub"
    by (rule eqSubst[where a="?args" and b="cpy (load_T ?packed)" and Q="\<lambda>z. cpx z = ?then_sub", OF eqSym[OF selectArgs] argsThen])
  have selectElse: "cpy (cpy (load_T ?packed)) = ?else_sub"
    by (rule eqSubst[where a="?args" and b="cpy (load_T ?packed)" and Q="\<lambda>z. cpy z = ?else_sub", OF eqSym[OF selectArgs] argsElse])
  have condEvalN: "eval_fuel n ?cond_orig ?A_put N"
    by (rule eval_fuel_N[OF n condOrigN putN])
  show ?thesis
  proof (rule cases_nat_2[where x="eval_fuel n ?cond_orig ?A_put"])
    show "eval_fuel n ?cond_orig ?A_put N"
      by (rule condEvalN)
  next
    assume condTimeout: "eval_fuel n ?cond_orig ?A_put = 0"
    have timeout: "eval_fuel (S n) t ?A_put = 0"
      by (rule eval_fuel_ifz_cond_timeout[OF n tg condTimeout])
    show "eval_fuel (m + S n) (subst_T t i s) A = S r"
      by (rule zero_successE[OF timeout run])
  next
    fix c
    assume c: "c N" and condSuccess: "eval_fuel n ?cond_orig ?A_put = S c"
    show "eval_fuel (m + S n) (subst_T t i s) A = S r"
    proof (rule cases_nat_2[where x=c])
      show "c N"
        by (rule c)
    next
      assume cz: "c = 0"
      have condZero: "eval_fuel n ?cond_orig ?A_put = S 0"
        using condSuccess sucCong[OF cz] by (rule eq_trans)
      have thenEvalN: "eval_fuel n ?then_orig ?A_put N"
        by (rule eval_fuel_N[OF n thenOrigN putN])
      show "eval_fuel (m + S n) (subst_T t i s) A = S r"
      proof (rule cases_nat_2[where x="eval_fuel n ?then_orig ?A_put"])
        show "eval_fuel n ?then_orig ?A_put N"
          by (rule thenEvalN)
      next
        assume thenTimeout: "eval_fuel n ?then_orig ?A_put = 0"
        have step: "eval_fuel (S n) t ?A_put = eval_fuel n ?then_orig ?A_put"
          by (rule eval_fuel_ifz_zero[OF n tg condZero thenEvalN])
        have timeout: "eval_fuel (S n) t ?A_put = 0"
          using step thenTimeout by (rule eq_trans)
        show "eval_fuel (m + S n) (subst_T t i s) A = S r"
          by (rule zero_successE[OF timeout run])
      next
        fix q
        assume q: "q N" and thenSuccess: "eval_fuel n ?then_orig ?A_put = S q"
        have originalValue: "eval_fuel (S n) t ?A_put = S q"
          by (rule eval_fuel_ifz_zero_value[OF n tg condZero thenSuccess])
        have resultEq: "S q = S r"
          by (rule same_success[OF originalValue run])
        have condSubSuccess: "eval_fuel (m + n) ?cond_sub A = S 0"
          by (rule IHcond[OF condZero])
        have thenSubSuccess: "eval_fuel (m + n) ?then_sub A = S q"
          by (rule IHthen[OF thenSuccess])
        have packedCond: "eval_fuel (m + n) (cpx (load_T ?packed)) A = S 0"
          by (rule eqSubst[where a="?cond_sub" and b="cpx (load_T ?packed)" and Q="\<lambda>z. eval_fuel (m + n) z A = S 0", OF eqSym[OF selectCond] condSubSuccess])
        have packedThen: "eval_fuel (m + n) (cpx (cpy (load_T ?packed))) A = S q"
          by (rule eqSubst[where a="?then_sub" and b="cpx (cpy (load_T ?packed))" and Q="\<lambda>z. eval_fuel (m + n) z A = S q", OF eqSym[OF selectThen] thenSubSuccess])
        have packedValue: "eval_fuel (S (m + n)) ?packed A = S q"
          by (rule eval_fuel_ifz_zero_value[OF mnN tagPacked packedCond packedThen])
        have fuelEq: "m + S n = S (m + n)"
          by (rule add_succ[OF m n])
        have lifted: "eval_fuel (m + S n) ?packed A = S q"
          by (rule eqSubst[where a="S (m + n)" and b="m + S n" and Q="\<lambda>z. eval_fuel z ?packed A = S q", OF eqSym[OF fuelEq] packedValue])
        have liftedSub: "eval_fuel (m + S n) (subst_T t i s) A = S q"
          by (rule eqSubst[where a="?packed" and b="subst_T t i s" and Q="\<lambda>z. eval_fuel (m + S n) z A = S q", OF eqSym[OF sub] lifted])
        show "eval_fuel (m + S n) (subst_T t i s) A = S r"
          using liftedSub resultEq by (rule eq_trans)
      qed
    next
      fix d
      assume d: "d N" and cnz: "c = S d"
      have condNonzero: "eval_fuel n ?cond_orig ?A_put = S (S d)"
        using condSuccess sucCong[OF cnz] by (rule eq_trans)
      have elseEvalN: "eval_fuel n ?else_orig ?A_put N"
        by (rule eval_fuel_N[OF n elseOrigN putN])
      show "eval_fuel (m + S n) (subst_T t i s) A = S r"
      proof (rule cases_nat_2[where x="eval_fuel n ?else_orig ?A_put"])
        show "eval_fuel n ?else_orig ?A_put N"
          by (rule elseEvalN)
      next
        assume elseTimeout: "eval_fuel n ?else_orig ?A_put = 0"
        have step: "eval_fuel (S n) t ?A_put = eval_fuel n ?else_orig ?A_put"
          by (rule eval_fuel_ifz_nonzero[OF n tg condNonzero elseEvalN])
        have timeout: "eval_fuel (S n) t ?A_put = 0"
          using step elseTimeout by (rule eq_trans)
        show "eval_fuel (m + S n) (subst_T t i s) A = S r"
          by (rule zero_successE[OF timeout run])
      next
        fix q
        assume q: "q N" and elseSuccess: "eval_fuel n ?else_orig ?A_put = S q"
        have originalValue: "eval_fuel (S n) t ?A_put = S q"
          by (rule eval_fuel_ifz_nonzero_value[OF n tg condNonzero elseSuccess])
        have resultEq: "S q = S r"
          by (rule same_success[OF originalValue run])
        have condSubSuccess: "eval_fuel (m + n) ?cond_sub A = S (S d)"
          by (rule IHcond[OF condNonzero])
        have elseSubSuccess: "eval_fuel (m + n) ?else_sub A = S q"
          by (rule IHelse[OF elseSuccess])
        have packedCond: "eval_fuel (m + n) (cpx (load_T ?packed)) A = S (S d)"
          by (rule eqSubst[where a="?cond_sub" and b="cpx (load_T ?packed)" and Q="\<lambda>z. eval_fuel (m + n) z A = S (S d)", OF eqSym[OF selectCond] condSubSuccess])
        have packedElse: "eval_fuel (m + n) (cpy (cpy (load_T ?packed))) A = S q"
          by (rule eqSubst[where a="?else_sub" and b="cpy (cpy (load_T ?packed))" and Q="\<lambda>z. eval_fuel (m + n) z A = S q", OF eqSym[OF selectElse] elseSubSuccess])
        have packedValue: "eval_fuel (S (m + n)) ?packed A = S q"
          by (rule eval_fuel_ifz_nonzero_value[OF mnN tagPacked packedCond packedElse])
        have fuelEq: "m + S n = S (m + n)"
          by (rule add_succ[OF m n])
        have lifted: "eval_fuel (m + S n) ?packed A = S q"
          by (rule eqSubst[where a="S (m + n)" and b="m + S n" and Q="\<lambda>z. eval_fuel z ?packed A = S q", OF eqSym[OF fuelEq] packedValue])
        have liftedSub: "eval_fuel (m + S n) (subst_T t i s) A = S q"
          by (rule eqSubst[where a="?packed" and b="subst_T t i s" and Q="\<lambda>z. eval_fuel (m + S n) z A = S q", OF eqSym[OF sub] lifted])
        show "eval_fuel (m + S n) (subst_T t i s) A = S r"
          using liftedSub resultEq by (rule eq_trans)
      qed
    qed
  qed
qed

lemma eval_fuel_subst_T_appI:
  assumes m: "m N" and n: "n N" and t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and srun: "eval_fuel m s A = S v"
      and nvar: "\<not> tag_T t = T_VAR" and nzero: "\<not> tag_T t = T_ZERO" and nsuc: "\<not> tag_T t = T_SUC"
      and npred: "\<not> tag_T t = T_PRED" and nifz: "\<not> tag_T t = T_IFZ"
      and run: "eval_fuel (S n) t (asn_put A i v) = S r"
      and IHarg1: "\<And>q. eval_fuel n (hyp_of (conc_of (load_T t))) (asn_put A i v) = S q \<Longrightarrow> eval_fuel (m + n) (subst_T (hyp_of (conc_of (load_T t))) i s) A = S q"
      and IHarg2: "\<And>q. eval_fuel n (conc_of (conc_of (load_T t))) (asn_put A i v) = S q \<Longrightarrow> eval_fuel (m + n) (subst_T (conc_of (conc_of (load_T t))) i s) A = S q"
  shows "eval_fuel (m + S n) (subst_T t i s) A = S r"
proof -
  let ?dfn = "hyp_of (load_T t)"
  let ?arg1_orig = "hyp_of (conc_of (load_T t))"
  let ?arg2_orig = "conc_of (conc_of (load_T t))"
  let ?arg1_sub = "subst_T ?arg1_orig i s"
  let ?arg2_sub = "subst_T ?arg2_orig i s"
  let ?A_put = "asn_put A i v"
  let ?args = "\<langle>?arg1_sub, ?arg2_sub\<rangle>"
  let ?payload = "\<langle>?dfn, ?args\<rangle>"
  let ?packed = "pack_T T_APP ?payload"
  have putN: "?A_put N"
    by (rule asn_put_N[OF A i v])
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have dfnN: "?dfn N"
    by (rule cpx_terminates[OF loadN])
  have tailN: "conc_of (load_T t) N"
    by (rule cpy_terminates[OF loadN])
  have arg1OrigN: "?arg1_orig N"
    by (rule cpx_terminates[OF tailN])
  have arg2OrigN: "?arg2_orig N"
    by (rule cpy_terminates[OF tailN])
  have arg1SubN: "?arg1_sub N"
    by (rule subst_T_N[OF arg1OrigN i s])
  have arg2SubN: "?arg2_sub N"
    by (rule subst_T_N[OF arg2OrigN i s])
  have mnN: "m + n N"
    by (rule add_terminates[OF m n])
  have argsN: "?args N"
    using arg1SubN arg2SubN by simp
  have payloadN: "?payload N"
    using dfnN argsN by simp
  have packedN: "?packed N"
    by (rule pack_T_N[OF _ payloadN], simp)
  have sub: "subst_T t i s = ?packed"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI2Eq[OF nzero packedN])
    apply (rule condI2Eq[OF nsuc packedN])
    apply (rule condI2Eq[OF npred packedN])
    apply (rule condI2Eq[OF nifz packedN])
    using packedN by simp
  have tagPacked: "tag_T ?packed = T_APP"
    by (rule tag_pack_T[OF _ payloadN], simp)
  have packedNvar: "\<not> tag_T ?packed = T_VAR"
    using tagPacked by simp
  have packedNzero: "\<not> tag_T ?packed = T_ZERO"
    using tagPacked by simp
  have packedNsuc: "\<not> tag_T ?packed = T_SUC"
    using tagPacked by simp
  have packedNpred: "\<not> tag_T ?packed = T_PRED"
    using tagPacked by simp
  have packedNifz: "\<not> tag_T ?packed = T_IFZ"
    using tagPacked by simp
  have loadPacked: "load_T ?packed = ?payload"
    by (rule load_pack_T[OF _ payloadN], simp)
  have payloadDfn: "hyp_of ?payload = ?dfn"
    by (rule cpx_proj[OF dfnN argsN])
  have payloadArgs: "conc_of ?payload = ?args"
    by (rule cpy_proj[OF dfnN argsN])
  have argsArg1: "hyp_of ?args = ?arg1_sub"
    by (rule cpx_proj[OF arg1SubN arg2SubN])
  have argsArg2: "conc_of ?args = ?arg2_sub"
    by (rule cpy_proj[OF arg1SubN arg2SubN])
  have selectDfn: "hyp_of (load_T ?packed) = ?dfn"
    by (rule eqSubst[where a="?payload" and b="load_T ?packed" and Q="\<lambda>z. hyp_of z = ?dfn", OF eqSym[OF loadPacked] payloadDfn])
  have selectArgs: "conc_of (load_T ?packed) = ?args"
    by (rule eqSubst[where a="?payload" and b="load_T ?packed" and Q="\<lambda>z. conc_of z = ?args", OF eqSym[OF loadPacked] payloadArgs])
  have selectArg1: "hyp_of (conc_of (load_T ?packed)) = ?arg1_sub"
    by (rule eqSubst[where a="?args" and b="conc_of (load_T ?packed)" and Q="\<lambda>z. hyp_of z = ?arg1_sub", OF eqSym[OF selectArgs] argsArg1])
  have selectArg2: "conc_of (conc_of (load_T ?packed)) = ?arg2_sub"
    by (rule eqSubst[where a="?args" and b="conc_of (load_T ?packed)" and Q="\<lambda>z. conc_of z = ?arg2_sub", OF eqSym[OF selectArgs] argsArg2])
  have arg1EvalN: "eval_fuel n ?arg1_orig ?A_put N"
    by (rule eval_fuel_N[OF n arg1OrigN putN])
  show ?thesis
  proof (rule cases_nat_2[where x="eval_fuel n ?arg1_orig ?A_put"])
    show "eval_fuel n ?arg1_orig ?A_put N"
      by (rule arg1EvalN)
  next
    assume arg1Timeout: "eval_fuel n ?arg1_orig ?A_put = 0"
    have timeout: "eval_fuel (S n) t ?A_put = 0"
      by (rule eval_fuel_app_arg1_timeout[OF n nvar nzero nsuc npred nifz arg1Timeout])
    show "eval_fuel (m + S n) (subst_T t i s) A = S r"
      by (rule zero_successE[OF timeout run])
  next
    fix x
    assume x: "x N" and arg1Success: "eval_fuel n ?arg1_orig ?A_put = S x"
    have arg2EvalN: "eval_fuel n ?arg2_orig ?A_put N"
      by (rule eval_fuel_N[OF n arg2OrigN putN])
    show "eval_fuel (m + S n) (subst_T t i s) A = S r"
    proof (rule cases_nat_2[where x="eval_fuel n ?arg2_orig ?A_put"])
      show "eval_fuel n ?arg2_orig ?A_put N"
        by (rule arg2EvalN)
    next
      assume arg2Timeout: "eval_fuel n ?arg2_orig ?A_put = 0"
      have timeout: "eval_fuel (S n) t ?A_put = 0"
        by (rule eval_fuel_app_arg2_timeout[OF n nvar nzero nsuc npred nifz arg1Success arg2Timeout])
      show "eval_fuel (m + S n) (subst_T t i s) A = S r"
        by (rule zero_successE[OF timeout run])
    next
      fix y
      assume y: "y N" and arg2Success: "eval_fuel n ?arg2_orig ?A_put = S y"
      have appAsnN: "x \<triangleright> y \<triangleright> Nil N"
        using x y by simp
      have bodyTermN: "nth ?dfn dfns N"
        by (rule nth_N'[OF dfns_N dfnN])
      have bodyEvalN: "eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) N"
        by (rule eval_fuel_N[OF n bodyTermN appAsnN])
      show "eval_fuel (m + S n) (subst_T t i s) A = S r"
      proof (rule cases_nat_2[where x="eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil)"])
        show "eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) N"
          by (rule bodyEvalN)
      next
        assume bodyTimeout: "eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) = 0"
        have timeout: "eval_fuel (S n) t ?A_put = 0"
          by (rule eval_fuel_app_body_timeout[OF n nvar nzero nsuc npred nifz arg1Success arg2Success bodyTimeout])
        show "eval_fuel (m + S n) (subst_T t i s) A = S r"
          by (rule zero_successE[OF timeout run])
      next
        fix q
        assume q: "q N" and bodySuccess: "eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) = S q"
        have originalValue: "eval_fuel (S n) t ?A_put = S q"
          by (rule eval_fuel_app_value[OF n nvar nzero nsuc npred nifz arg1Success arg2Success bodySuccess])
        have resultEq: "S q = S r"
          by (rule same_success[OF originalValue run])
        have arg1SubSuccess: "eval_fuel (m + n) ?arg1_sub A = S x"
          by (rule IHarg1[OF arg1Success])
        have arg2SubSuccess: "eval_fuel (m + n) ?arg2_sub A = S y"
          by (rule IHarg2[OF arg2Success])
        have packedArg1: "eval_fuel (m + n) (hyp_of (conc_of (load_T ?packed))) A = S x"
          by (rule eqSubst[where a="?arg1_sub" and b="hyp_of (conc_of (load_T ?packed))" and Q="\<lambda>z. eval_fuel (m + n) z A = S x", OF eqSym[OF selectArg1] arg1SubSuccess])
        have packedArg2: "eval_fuel (m + n) (conc_of (conc_of (load_T ?packed))) A = S y"
          by (rule eqSubst[where a="?arg2_sub" and b="conc_of (conc_of (load_T ?packed))" and Q="\<lambda>z. eval_fuel (m + n) z A = S y", OF eqSym[OF selectArg2] arg2SubSuccess])
        have bodyLift0: "eval_fuel (n + m) (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) = S q"
          by (rule eval_fuel_success_add[OF n m bodyTermN appAsnN bodySuccess])
        have bodyFuelEq: "n + m = m + n"
          by (rule add_comm[OF n m])
        have bodyLift: "eval_fuel (m + n) (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) = S q"
          by (rule eqSubst[where a="n + m" and b="m + n" and Q="\<lambda>z. eval_fuel z (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) = S q", OF bodyFuelEq bodyLift0])
        have packedBody: "eval_fuel (m + n) (nth (hyp_of (load_T ?packed)) dfns) (x \<triangleright> y \<triangleright> Nil) = S q"
          by (rule eqSubst[where a="?dfn" and b="hyp_of (load_T ?packed)" and Q="\<lambda>z. eval_fuel (m + n) (nth z dfns) (x \<triangleright> y \<triangleright> Nil) = S q", OF eqSym[OF selectDfn] bodyLift])
        have packedValue: "eval_fuel (S (m + n)) ?packed A = S q"
          by (rule eval_fuel_app_value[OF mnN packedNvar packedNzero packedNsuc packedNpred packedNifz packedArg1 packedArg2 packedBody])
        have fuelEq: "m + S n = S (m + n)"
          by (rule add_succ[OF m n])
        have lifted: "eval_fuel (m + S n) ?packed A = S q"
          by (rule eqSubst[where a="S (m + n)" and b="m + S n" and Q="\<lambda>z. eval_fuel z ?packed A = S q", OF eqSym[OF fuelEq] packedValue])
        have liftedSub: "eval_fuel (m + S n) (subst_T t i s) A = S q"
          by (rule eqSubst[where a="?packed" and b="subst_T t i s" and Q="\<lambda>z. eval_fuel (m + S n) z A = S q", OF eqSym[OF sub] lifted])
        show "eval_fuel (m + S n) (subst_T t i s) A = S r"
          using liftedSub resultEq by (rule eq_trans)
      qed
    qed
  qed
qed

lemma eval_fuel_subst_TI:
  assumes m: "m N" and k: "k N" and t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and srun: "eval_fuel m s A = S v" and run: "eval_fuel k t (asn_put A i v) = S r"
  shows "eval_fuel (m + k) (subst_T t i s) A = S r"
proof -
  have putN: "asn_put A i v N"
    by (rule asn_put_N[OF A i v])
  have main: "\<forall>u. \<forall>q. (eval_fuel k u (asn_put A i v) = S q) \<longrightarrow> eval_fuel (m + k) (subst_T u i s) A = S q"
  proof (rule ind[OF k])
    show "\<forall>u. \<forall>q. (eval_fuel 0 u (asn_put A i v) = S q) \<longrightarrow> eval_fuel (m + 0) (subst_T u i s) A = S q"
    proof (rule forallI)
      fix u
      assume u: "u N"
      show "\<forall>q. (eval_fuel 0 u (asn_put A i v) = S q) \<longrightarrow> eval_fuel (m + 0) (subst_T u i s) A = S q"
      proof (rule forallI)
        fix q
        assume q: "q N"
        show "(eval_fuel 0 u (asn_put A i v) = S q) \<longrightarrow> eval_fuel (m + 0) (subst_T u i s) A = S q"
        proof (rule implI)
          have evalN: "eval_fuel 0 u (asn_put A i v) N"
            by (rule eval_fuel_N[OF nat0 u putN])
          have sqN: "S q N"
            by (rule natS[OF q])
          show "(eval_fuel 0 u (asn_put A i v) = S q) B"
            by (rule eqBool[OF evalN sqN])
        next
          assume success: "eval_fuel 0 u (asn_put A i v) = S q"
          have timeout: "eval_fuel 0 u (asn_put A i v) = 0"
            by (rule eval_fuel_zero)
          show "eval_fuel (m + 0) (subst_T u i s) A = S q"
            by (rule zero_successE[OF timeout success])
        qed
      qed
    qed
  next
    fix n
    assume n: "n N"
    assume IH: "\<forall>u. \<forall>q. (eval_fuel n u (asn_put A i v) = S q) \<longrightarrow> eval_fuel (m + n) (subst_T u i s) A = S q"
    show "\<forall>u. \<forall>q. (eval_fuel (S n) u (asn_put A i v) = S q) \<longrightarrow> eval_fuel (m + S n) (subst_T u i s) A = S q"
    proof (rule forallI)
      fix u
      assume u: "u N"
      show "\<forall>q. (eval_fuel (S n) u (asn_put A i v) = S q) \<longrightarrow> eval_fuel (m + S n) (subst_T u i s) A = S q"
      proof (rule forallI)
        fix q
        assume q: "q N"
        show "(eval_fuel (S n) u (asn_put A i v) = S q) \<longrightarrow> eval_fuel (m + S n) (subst_T u i s) A = S q"
        proof (rule implI)
          have sn: "S n N"
            by (rule natS[OF n])
          have evalN: "eval_fuel (S n) u (asn_put A i v) N"
            by (rule eval_fuel_N[OF sn u putN])
          have sqN: "S q N"
            by (rule natS[OF q])
          show "(eval_fuel (S n) u (asn_put A i v) = S q) B"
            by (rule eqBool[OF evalN sqN])
        next
          assume result: "eval_fuel (S n) u (asn_put A i v) = S q"
          have IHmeta: "\<And>w z. w N \<Longrightarrow> eval_fuel n w (asn_put A i v) = S z \<Longrightarrow> eval_fuel (m + n) (subst_T w i s) A = S z"
          proof -
            fix w z
            assume w: "w N" and success: "eval_fuel n w (asn_put A i v) = S z"
            have z: "z N"
              by (rule eval_fuel_result_N[OF n w putN success])
            have IHw: "\<forall>z. (eval_fuel n w (asn_put A i v) = S z) \<longrightarrow> eval_fuel (m + n) (subst_T w i s) A = S z"
              by (rule forallE[where a=w, OF IH w])
            have IHwz: "(eval_fuel n w (asn_put A i v) = S z) \<longrightarrow> eval_fuel (m + n) (subst_T w i s) A = S z"
              by (rule forallE[where a=z, OF IHw z])
            show "eval_fuel (m + n) (subst_T w i s) A = S z"
              using IHwz success by (rule implE)
          qed
          have loadN: "load_T u N"
            by (rule load_T_N[OF u])
          have condN: "hyp_of (load_T u) N"
            by (rule cpx_terminates[OF loadN])
          have tailN: "conc_of (load_T u) N"
            by (rule cpy_terminates[OF loadN])
          have leftN: "hyp_of (conc_of (load_T u)) N"
            by (rule cpx_terminates[OF tailN])
          have rightN: "conc_of (conc_of (load_T u)) N"
            by (rule cpy_terminates[OF tailN])
          have IHload: "\<And>z. eval_fuel n (load_T u) (asn_put A i v) = S z \<Longrightarrow> eval_fuel (m + n) (subst_T (load_T u) i s) A = S z"
          proof -
            fix z
            assume success: "eval_fuel n (load_T u) (asn_put A i v) = S z"
            show "eval_fuel (m + n) (subst_T (load_T u) i s) A = S z"
              by (rule IHmeta[OF loadN success])
          qed
          have IHcond: "\<And>z. eval_fuel n (hyp_of (load_T u)) (asn_put A i v) = S z \<Longrightarrow> eval_fuel (m + n) (subst_T (hyp_of (load_T u)) i s) A = S z"
          proof -
            fix z
            assume success: "eval_fuel n (hyp_of (load_T u)) (asn_put A i v) = S z"
            show "eval_fuel (m + n) (subst_T (hyp_of (load_T u)) i s) A = S z"
              by (rule IHmeta[OF condN success])
          qed
          have IHleft: "\<And>z. eval_fuel n (hyp_of (conc_of (load_T u))) (asn_put A i v) = S z \<Longrightarrow> eval_fuel (m + n) (subst_T (hyp_of (conc_of (load_T u))) i s) A = S z"
          proof -
            fix z
            assume success: "eval_fuel n (hyp_of (conc_of (load_T u))) (asn_put A i v) = S z"
            show "eval_fuel (m + n) (subst_T (hyp_of (conc_of (load_T u))) i s) A = S z"
              by (rule IHmeta[OF leftN success])
          qed
          have IHright: "\<And>z. eval_fuel n (conc_of (conc_of (load_T u))) (asn_put A i v) = S z \<Longrightarrow> eval_fuel (m + n) (subst_T (conc_of (conc_of (load_T u))) i s) A = S z"
          proof -
            fix z
            assume success: "eval_fuel n (conc_of (conc_of (load_T u))) (asn_put A i v) = S z"
            show "eval_fuel (m + n) (subst_T (conc_of (conc_of (load_T u))) i s) A = S z"
              by (rule IHmeta[OF rightN success])
          qed
          have tagN: "tag_T u N"
            by (rule tag_T_N[OF u])
          have varB: "(tag_T u = T_VAR) B"
            by (rule eqBool[OF tagN], simp)
          have zeroB: "(tag_T u = T_ZERO) B"
            by (rule eqBool[OF tagN], simp)
          have sucB: "(tag_T u = T_SUC) B"
            by (rule eqBool[OF tagN], simp)
          have predB: "(tag_T u = T_PRED) B"
            by (rule eqBool[OF tagN], simp)
          have ifzB: "(tag_T u = T_IFZ) B"
            by (rule eqBool[OF tagN], simp)
          show "eval_fuel (m + S n) (subst_T u i s) A = S q"
          proof (rule cases_bool[where q="tag_T u = T_VAR"])
            show "(tag_T u = T_VAR) B"
              by (rule varB)
          next
            assume tg: "tag_T u = T_VAR"
            show "eval_fuel (m + S n) (subst_T u i s) A = S q"
              by (rule eval_fuel_subst_T_varI[OF m n u i s A v srun tg result])
          next
            assume nvar: "\<not> tag_T u = T_VAR"
            show "eval_fuel (m + S n) (subst_T u i s) A = S q"
            proof (rule cases_bool[where q="tag_T u = T_ZERO"])
              show "(tag_T u = T_ZERO) B"
                by (rule zeroB)
            next
              assume tg: "tag_T u = T_ZERO"
              show "eval_fuel (m + S n) (subst_T u i s) A = S q"
                by (rule eval_fuel_subst_T_zeroI[OF m n u i s A v srun tg result])
            next
              assume nzero: "\<not> tag_T u = T_ZERO"
              show "eval_fuel (m + S n) (subst_T u i s) A = S q"
              proof (rule cases_bool[where q="tag_T u = T_SUC"])
                show "(tag_T u = T_SUC) B"
                  by (rule sucB)
              next
                assume tg: "tag_T u = T_SUC"
                show "eval_fuel (m + S n) (subst_T u i s) A = S q"
                  by (rule eval_fuel_subst_T_sucI[OF m n u i s A v srun tg result IHload])
              next
                assume nsuc: "\<not> tag_T u = T_SUC"
                show "eval_fuel (m + S n) (subst_T u i s) A = S q"
                proof (rule cases_bool[where q="tag_T u = T_PRED"])
                  show "(tag_T u = T_PRED) B"
                    by (rule predB)
                next
                  assume tg: "tag_T u = T_PRED"
                  show "eval_fuel (m + S n) (subst_T u i s) A = S q"
                    by (rule eval_fuel_subst_T_predI[OF m n u i s A v srun tg result IHload])
                next
                  assume npred: "\<not> tag_T u = T_PRED"
                  show "eval_fuel (m + S n) (subst_T u i s) A = S q"
                  proof (rule cases_bool[where q="tag_T u = T_IFZ"])
                    show "(tag_T u = T_IFZ) B"
                      by (rule ifzB)
                  next
                    assume tg: "tag_T u = T_IFZ"
                    show "eval_fuel (m + S n) (subst_T u i s) A = S q"
                      by (rule eval_fuel_subst_T_ifzI[OF m n u i s A v srun tg result IHcond IHleft IHright])
                  next
                    assume nifz: "\<not> tag_T u = T_IFZ"
                    show "eval_fuel (m + S n) (subst_T u i s) A = S q"
                      by (rule eval_fuel_subst_T_appI[OF m n u i s A v srun nvar nzero nsuc npred nifz result IHleft IHright])
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  have r: "r N"
    by (rule eval_fuel_result_N[OF k t putN run])
  have mainT: "\<forall>q. (eval_fuel k t (asn_put A i v) = S q) \<longrightarrow> eval_fuel (m + k) (subst_T t i s) A = S q"
    by (rule forallE[where a=t, OF main t])
  have mainR: "(eval_fuel k t (asn_put A i v) = S r) \<longrightarrow> eval_fuel (m + k) (subst_T t i s) A = S r"
    by (rule forallE[where a=r, OF mainT r])
  show ?thesis
    using mainR run by (rule implE)
qed

lemma evals_subst_TI:
  assumes t: "t N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and evs: "evals s A v" and evt: "evals t (asn_put A i v) r"
  shows "evals (subst_T t i s) A r"
proof -
  show ?thesis
    using evs
  proof (rule evalsE)
    fix m
    assume m: "m N" and srun: "eval_fuel m s A = S v"
    show "evals (subst_T t i s) A r"
      using evt
    proof (rule evalsE)
      fix k
      assume k: "k N" and run: "eval_fuel k t (asn_put A i v) = S r"
      have mkN: "m + k N"
        by (rule add_terminates[OF m k])
      have transported: "eval_fuel (m + k) (subst_T t i s) A = S r"
        by (rule eval_fuel_subst_TI[OF m k t i s A v srun run])
      show "evals (subst_T t i s) A r"
        by (rule evalsI[OF mkN transported])
    qed
  qed
qed

lemmas evals_subst_T = evals_subst_TD evals_subst_TI

lemma subst_F_N:
  assumes f: "f N" and i: "i N" and s: "s N"
  shows "subst_F f i s N"
proof -
  let ?left = "subst_T (hyp_of (load_F f)) i s"
  let ?right = "subst_T (conc_of (load_F f)) i s"
  let ?payload = "\<langle>?left, ?right\<rangle>"
  have loadN: "load_F f N"
    by (rule load_F_N[OF f])
  have leftOrigN: "hyp_of (load_F f) N"
    by (rule cpx_terminates[OF loadN])
  have rightOrigN: "conc_of (load_F f) N"
    by (rule cpy_terminates[OF loadN])
  have leftN: "?left N"
    by (rule subst_T_N[OF leftOrigN i s])
  have rightN: "?right N"
    by (rule subst_T_N[OF rightOrigN i s])
  have payloadN: "?payload N"
    using leftN rightN by simp
  have eqPackN: "pack_F F_EQ ?payload N"
    by (rule pack_F_N[OF _ payloadN], simp)
  have neqPackN: "pack_F F_NEQ ?payload N"
    by (rule pack_F_N[OF _ payloadN], simp)
  have tagN: "tag_F f N"
    by (rule tag_F_N[OF f])
  have tagB: "(tag_F f = F_EQ) B"
    by (rule eqBool[OF tagN], simp)
  show ?thesis
    apply (rule defE[OF subst_F_def[where f=f and j=i and v=s]])
    apply (rule condT[OF tagB eqPackN])
    apply (rule neqPackN)
    done
qed

lemma load_F_subst_F:
  assumes f: "f N" and i: "i N" and s: "s N"
  shows "load_F (subst_F f i s) =
    \<langle>subst_T (hyp_of (load_F f)) i s, subst_T (conc_of (load_F f)) i s\<rangle>"
proof -
  let ?left = "subst_T (hyp_of (load_F f)) i s"
  let ?right = "subst_T (conc_of (load_F f)) i s"
  let ?payload = "\<langle>?left, ?right\<rangle>"
  have loadN: "load_F f N"
    by (rule load_F_N[OF f])
  have leftOrigN: "hyp_of (load_F f) N"
    by (rule cpx_terminates[OF loadN])
  have rightOrigN: "conc_of (load_F f) N"
    by (rule cpy_terminates[OF loadN])
  have leftN: "?left N"
    by (rule subst_T_N[OF leftOrigN i s])
  have rightN: "?right N"
    by (rule subst_T_N[OF rightOrigN i s])
  have payloadN: "?payload N"
    using leftN rightN by simp
  have eqPackN: "pack_F F_EQ ?payload N"
    by (rule pack_F_N[OF _ payloadN], simp)
  have neqPackN: "pack_F F_NEQ ?payload N"
    by (rule pack_F_N[OF _ payloadN], simp)
  have tagN: "tag_F f N"
    by (rule tag_F_N[OF f])
  have tagB: "(tag_F f = F_EQ) B"
    by (rule eqBool[OF tagN], simp)
  show ?thesis
  proof (rule cases_bool[where q="tag_F f = F_EQ"])
    show "(tag_F f = F_EQ) B"
      by (rule tagB)
  next
    assume tg: "tag_F f = F_EQ"
    have feqN: "F_EQ N"
      by simp
    have eqPackN: "pack_F F_EQ ?payload N"
      by (rule pack_F_N[OF feqN payloadN])
    have sub: "subst_F f i s = pack_F F_EQ ?payload"
      apply (rule defE[OF subst_F_def[where f=f and j=i and v=s]])
      apply (rule condI1Eq[OF tg eqPackN])
      using eqPackN apply simp
      done
    have load: "load_F (pack_F F_EQ ?payload) = ?payload"
      by (rule load_pack_F[OF _ payloadN], simp)
    show "load_F (subst_F f i s) = ?payload"
      by (rule eqSubst[where a="pack_F F_EQ ?payload" and b="subst_F f i s" and Q="\<lambda>z. load_F z = ?payload", OF eqSym[OF sub] load])
  next
    assume tg: "\<not> tag_F f = F_EQ"
    have feqN: "F_NEQ N"
      by simp
    have neqPackN: "pack_F F_NEQ ?payload N"
      by (rule pack_F_N[OF feqN payloadN])
    have sub: "subst_F f i s = pack_F F_NEQ ?payload"
      apply (rule defE[OF subst_F_def[where f=f and j=i and v=s]])
      apply (rule condI2Eq[OF tg neqPackN])
      using neqPackN apply simp
      done
    have load: "load_F (pack_F F_NEQ ?payload) = ?payload"
      by (rule load_pack_F[OF _ payloadN], simp)
    show "load_F (subst_F f i s) = ?payload"
      by (rule eqSubst[where a="pack_F F_NEQ ?payload" and b="subst_F f i s" and Q="\<lambda>z. load_F z = ?payload", OF eqSym[OF sub] load])
  qed
qed

lemma hyp_of_load_F_subst_F:
  assumes f: "f N" and i: "i N" and s: "s N"
  shows "hyp_of (load_F (subst_F f i s)) = subst_T (hyp_of (load_F f)) i s"
proof -
  let ?left = "subst_T (hyp_of (load_F f)) i s"
  let ?right = "subst_T (conc_of (load_F f)) i s"
  let ?payload = "\<langle>?left, ?right\<rangle>"
  have loadN: "load_F f N"
    by (rule load_F_N[OF f])
  have leftN: "?left N"
    by (rule subst_T_N[OF cpx_terminates[OF loadN] i s])
  have rightN: "?right N"
    by (rule subst_T_N[OF cpy_terminates[OF loadN] i s])
  have load: "load_F (subst_F f i s) = ?payload"
    by (rule load_F_subst_F[OF f i s])
  have projection: "hyp_of ?payload = ?left"
    by (rule cpx_proj[OF leftN rightN])
  show ?thesis
    by (rule eqSubst[where a="?payload" and b="load_F (subst_F f i s)" and Q="\<lambda>z. hyp_of z = ?left", OF eqSym[OF load] projection])
qed

lemma conc_of_load_F_subst_F:
  assumes f: "f N" and i: "i N" and s: "s N"
  shows "conc_of (load_F (subst_F f i s)) = subst_T (conc_of (load_F f)) i s"
proof -
  let ?left = "subst_T (hyp_of (load_F f)) i s"
  let ?right = "subst_T (conc_of (load_F f)) i s"
  let ?payload = "\<langle>?left, ?right\<rangle>"
  have loadN: "load_F f N"
    by (rule load_F_N[OF f])
  have leftN: "?left N"
    by (rule subst_T_N[OF cpx_terminates[OF loadN] i s])
  have rightN: "?right N"
    by (rule subst_T_N[OF cpy_terminates[OF loadN] i s])
  have load: "load_F (subst_F f i s) = ?payload"
    by (rule load_F_subst_F[OF f i s])
  have projection: "conc_of ?payload = ?right"
    by (rule cpy_proj[OF leftN rightN])
  show ?thesis
    by (rule eqSubst[where a="?payload" and b="load_F (subst_F f i s)" and Q="\<lambda>z. conc_of z = ?right", OF eqSym[OF load] projection])
qed

definition sat_fuel :: "fm \<Rightarrow> asn \<Rightarrow> o" where
  "sat_fuel f A \<equiv> \<exists>x. \<exists>y. evals (hyp_of (load_F f)) A x \<and> (evals (conc_of (load_F f)) A y \<and> (if tag_F f = F_EQ then x = y else x \<noteq> y))"

lemma sat_fuelE:
  assumes sat: "sat_fuel f A"
      and step: "\<And>x y. x N \<Longrightarrow> y N \<Longrightarrow>
        evals (hyp_of (load_F f)) A x \<Longrightarrow>
        evals (conc_of (load_F f)) A y \<Longrightarrow>
        (if tag_F f = F_EQ then x = y else x \<noteq> y) \<Longrightarrow> R"
  shows R
proof -
  have ex: "\<exists>x. \<exists>y. evals (hyp_of (load_F f)) A x \<and> (evals (conc_of (load_F f)) A y \<and> (if tag_F f = F_EQ then x = y else x \<noteq> y))"
    using sat unfolding sat_fuel_def .
  show R
    using ex
  proof (rule existsE)
    fix x
    assume x: "x N"
    assume exY: "\<exists>y.  evals (hyp_of (load_F f)) A x \<and> (evals (conc_of (load_F f)) A y \<and> (if tag_F f = F_EQ then x = y else x \<noteq> y))"
    show R
      using exY
    proof (rule existsE)
      fix y
      assume y: "y N"
      assume facts: "evals (hyp_of (load_F f)) A x \<and>
        (evals (conc_of (load_F f)) A y \<and>
         (if tag_F f = F_EQ then x = y else x \<noteq> y))"
      have left: "evals (hyp_of (load_F f)) A x"
        by (rule conjE1[OF facts])
      have rest: "evals (conc_of (load_F f)) A y \<and>
        (if tag_F f = F_EQ then x = y else x \<noteq> y)"
        by (rule conjE2[OF facts])
      have right: "evals (conc_of (load_F f)) A y"
        by (rule conjE1[OF rest])
      have relation: "if tag_F f = F_EQ then x = y else x \<noteq> y"
        by (rule conjE2[OF rest])
      show R
        by (rule step[OF x y left right relation])
    qed
  qed
qed

lemma tag_F_subst_F_eq:
  assumes f: "f N" and i: "i N" and s: "s N" and tg: "tag_F f = F_EQ"
  shows "tag_F (subst_F f i s) = F_EQ"
proof -
  let ?left = "subst_T (hyp_of (load_F f)) i s"
  let ?right = "subst_T (conc_of (load_F f)) i s"
  let ?payload = "\<langle>?left, ?right\<rangle>"
  have loadN: "load_F f N"
    by (rule load_F_N[OF f])
  have leftN: "?left N"
    by (rule subst_T_N[OF cpx_terminates[OF loadN] i s])
  have rightN: "?right N"
    by (rule subst_T_N[OF cpy_terminates[OF loadN] i s])
  have payloadN: "?payload N"
    using leftN rightN by simp
  have feqN: "F_EQ N"
    by simp
  have packedN: "pack_F F_EQ ?payload N"
    by (rule pack_F_N[OF feqN payloadN])
  have sub: "subst_F f i s = pack_F F_EQ ?payload"
    apply (rule defE[OF subst_F_def[where f=f and j=i and v=s]])
    apply (rule condI1Eq[OF tg packedN])
    using packedN apply simp
    done
  have packedTag: "tag_F (pack_F F_EQ ?payload) = F_EQ"
    by (rule tag_pack_F[OF feqN payloadN])
  show ?thesis
    by (rule eqSubst[where a="pack_F F_EQ ?payload" and b="subst_F f i s" and Q="\<lambda>z. tag_F z = F_EQ", OF eqSym[OF sub] packedTag])
qed

lemma tag_F_subst_F_neq:
  assumes f: "f N" and i: "i N" and s: "s N" and tg: "\<not> tag_F f = F_EQ"
  shows "\<not> tag_F (subst_F f i s) = F_EQ"
proof -
  let ?left = "subst_T (hyp_of (load_F f)) i s"
  let ?right = "subst_T (conc_of (load_F f)) i s"
  let ?payload = "\<langle>?left, ?right\<rangle>"
  have loadN: "load_F f N"
    by (rule load_F_N[OF f])
  have leftN: "?left N"
    by (rule subst_T_N[OF cpx_terminates[OF loadN] i s])
  have rightN: "?right N"
    by (rule subst_T_N[OF cpy_terminates[OF loadN] i s])
  have payloadN: "?payload N"
    using leftN rightN by simp
  have fneqN: "F_NEQ N"
    by simp
  have packedN: "pack_F F_NEQ ?payload N"
    by (rule pack_F_N[OF fneqN payloadN])
  have sub: "subst_F f i s = pack_F F_NEQ ?payload"
    apply (rule defE[OF subst_F_def[where f=f and j=i and v=s]])
    apply (rule condI2Eq[OF tg packedN])
    using packedN apply simp
    done
  have packedTag: "tag_F (pack_F F_NEQ ?payload) = F_NEQ"
    by (rule tag_pack_F[OF fneqN payloadN])
  have result: "tag_F (subst_F f i s) = F_NEQ"
    by (rule eqSubst[where a="pack_F F_NEQ ?payload" and b="subst_F f i s" and Q="\<lambda>z. tag_F z = F_NEQ", OF eqSym[OF sub] packedTag])
  show ?thesis
    using result by simp
qed

lemma sat_fuelI:
  assumes x: "x N" and y: "y N"
      and left: "evals (hyp_of (load_F f)) A x"
      and right: "evals (conc_of (load_F f)) A y"
      and relation: "if tag_F f = F_EQ then x = y else x \<noteq> y"
  shows "sat_fuel f A"
  unfolding sat_fuel_def
proof (rule existsI[OF x], rule existsI[OF y])
  show "evals (hyp_of (load_F f)) A x \<and>
    (evals (conc_of (load_F f)) A y \<and>
     (if tag_F f = F_EQ then x = y else x \<noteq> y))"
  proof (rule conjI)
    show "evals (hyp_of (load_F f)) A x"
      by (rule left)
    show "evals (conc_of (load_F f)) A y \<and>
      (if tag_F f = F_EQ then x = y else x \<noteq> y)"
      by (rule conjI[OF right relation])
  qed
qed

lemma sat_fuel_subst_FD:
  assumes f: "f N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and evs: "evals s A v" and sat: "sat_fuel (subst_F f i s) A"
  shows "sat_fuel f (asn_put A i v)"
proof -
  let ?left_orig = "hyp_of (load_F f)"
  let ?right_orig = "conc_of (load_F f)"
  let ?left_sub = "subst_T ?left_orig i s"
  let ?right_sub = "subst_T ?right_orig i s"
  let ?A_put = "asn_put A i v"
  have loadN: "load_F f N"
    by (rule load_F_N[OF f])
  have leftOrigN: "?left_orig N"
    by (rule cpx_terminates[OF loadN])
  have rightOrigN: "?right_orig N"
    by (rule cpy_terminates[OF loadN])
  have leftProj: "hyp_of (load_F (subst_F f i s)) = ?left_sub"
    by (rule hyp_of_load_F_subst_F[OF f i s])
  have rightProj: "conc_of (load_F (subst_F f i s)) = ?right_sub"
    by (rule conc_of_load_F_subst_F[OF f i s])
  have tagN: "tag_F f N"
    by (rule tag_F_N[OF f])
  have feqN: "F_EQ N"
    by simp
  have tagB: "(tag_F f = F_EQ) B"
    by (rule eqBool[OF tagN feqN])
  show ?thesis
    using sat
  proof (rule sat_fuelE)
    fix x y
    assume x: "x N" and y: "y N"
        and left: "evals (hyp_of (load_F (subst_F f i s))) A x"
        and right: "evals (conc_of (load_F (subst_F f i s))) A y"
        and relation: "if tag_F (subst_F f i s) = F_EQ then x = y else x \<noteq> y"
    have leftSub: "evals ?left_sub A x"
      by (rule eqSubst[where a="hyp_of (load_F (subst_F f i s))" and b="?left_sub" and Q="\<lambda>z. evals z A x", OF leftProj left])
    have rightSub: "evals ?right_sub A y"
      by (rule eqSubst[where a="conc_of (load_F (subst_F f i s))" and b="?right_sub" and Q="\<lambda>z. evals z A y", OF rightProj right])
    have leftNew: "evals ?left_orig ?A_put x"
      by (rule evals_subst_TD[OF leftOrigN i s A v evs leftSub])
    have rightNew: "evals ?right_orig ?A_put y"
      by (rule evals_subst_TD[OF rightOrigN i s A v evs rightSub])  
    have originalRelation: "if tag_F f = F_EQ then x = y else x \<noteq> y"
    proof (rule cases_bool[where q="tag_F f = F_EQ"])
      show "(tag_F f = F_EQ) B"
        by (rule tagB)
    next
      assume tg: "tag_F f = F_EQ"
      have subTag: "tag_F (subst_F f i s) = F_EQ"
        by (rule tag_F_subst_F_eq[OF f i s tg])
      have xy: "x = y"
        by (rule cond_thenE[OF subTag relation])
      have xyB: "(x = y) B"
        by (rule eqBool[OF x y])
      have relIff: "(if tag_F f = F_EQ then x = y else x \<noteq> y) \<longleftrightarrow> x = y"
        by (rule condI1B[OF tg xyB])
      have bck: "(x = y) \<longrightarrow> (if tag_F f = F_EQ then x = y else x \<noteq> y)"
        by (rule iffE2[OF relIff])
      show "if tag_F f = F_EQ then x = y else x \<noteq> y"
        using bck xy by (rule implE)
    next
      assume tg: "\<not> tag_F f = F_EQ"
      have subTag: "\<not> tag_F (subst_F f i s) = F_EQ"
        by (rule tag_F_subst_F_neq[OF f i s tg])
      have xy: "x \<noteq> y"
        by (rule notcond_thenE[OF subTag relation])
      have xyB: "(x \<noteq> y) B"
        by (rule neq_bool[OF x y])
      have relIff: "(if tag_F f = F_EQ then x = y else x \<noteq> y) \<longleftrightarrow> x \<noteq> y"
        by (rule condI2B[OF tg xyB])
      have bck: "(x \<noteq> y) \<longrightarrow> (if tag_F f = F_EQ then x = y else x \<noteq> y)"
        by (rule iffE2[OF relIff])
      show "if tag_F f = F_EQ then x = y else x \<noteq> y"
        using bck xy by (rule implE)
    qed
    show "sat_fuel f ?A_put"
      by (rule sat_fuelI[OF x y leftNew rightNew originalRelation])
  qed
qed

lemma sat_fuel_subst_FI:
  assumes f: "f N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and evs: "evals s A v" and sat: "sat_fuel f (asn_put A i v)"
  shows "sat_fuel (subst_F f i s) A"
proof -
  let ?left_orig = "hyp_of (load_F f)"
  let ?right_orig = "conc_of (load_F f)"
  let ?left_sub = "subst_T ?left_orig i s"
  let ?right_sub = "subst_T ?right_orig i s"
  let ?A_put = "asn_put A i v"
  have loadN: "load_F f N"
    by (rule load_F_N[OF f])
  have leftOrigN: "?left_orig N"
    by (rule cpx_terminates[OF loadN])
  have rightOrigN: "?right_orig N"
    by (rule cpy_terminates[OF loadN])
  have leftProj: "hyp_of (load_F (subst_F f i s)) = ?left_sub"
    by (rule hyp_of_load_F_subst_F[OF f i s])
  have rightProj: "conc_of (load_F (subst_F f i s)) = ?right_sub"
    by (rule conc_of_load_F_subst_F[OF f i s])
  have tagN: "tag_F f N"
    by (rule tag_F_N[OF f])
  have feqN: "F_EQ N"
    by simp
  have tagB: "(tag_F f = F_EQ) B"
    by (rule eqBool[OF tagN feqN])
  show ?thesis
    using sat
  proof (rule sat_fuelE)
    fix x y
    assume x: "x N" and y: "y N"
        and left: "evals ?left_orig ?A_put x"
        and right: "evals ?right_orig ?A_put y"
        and relation: "if tag_F f = F_EQ then x = y else x \<noteq> y"
    have leftSub: "evals ?left_sub A x"
      by (rule evals_subst_TI[OF leftOrigN i s A v evs left])
    have rightSub: "evals ?right_sub A y"
      by (rule evals_subst_TI[OF rightOrigN i s A v evs right])
    have leftNew: "evals (hyp_of (load_F (subst_F f i s))) A x"
      by (rule eqSubst[where a="?left_sub" and b="hyp_of (load_F (subst_F f i s))" and Q="\<lambda>z. evals z A x", OF eqSym[OF leftProj] leftSub])
    have rightNew: "evals (conc_of (load_F (subst_F f i s))) A y"
      by (rule eqSubst[where a="?right_sub" and b="conc_of (load_F (subst_F f i s))" and Q="\<lambda>z. evals z A y", OF eqSym[OF rightProj] rightSub])
    have subRelation: "if tag_F (subst_F f i s) = F_EQ then x = y else x \<noteq> y"
    proof (rule cases_bool[where q="tag_F f = F_EQ"])
      show "(tag_F f = F_EQ) B"
        by (rule tagB)
    next
      assume tg: "tag_F f = F_EQ"
      have subTag: "tag_F (subst_F f i s) = F_EQ"
        by (rule tag_F_subst_F_eq[OF f i s tg])
      have xy: "x = y"
        by (rule cond_thenE[OF tg relation])
      have xyB: "(x = y) B"
        by (rule eqBool[OF x y])
      have relIff: "(if tag_F (subst_F f i s) = F_EQ then x = y else x \<noteq> y) \<longleftrightarrow> x = y"
        by (rule condI1B[OF subTag xyB])
      have bck: "(x = y) \<longrightarrow> (if tag_F (subst_F f i s) = F_EQ then x = y else x \<noteq> y)"
        by (rule iffE2[OF relIff])
      show "if tag_F (subst_F f i s) = F_EQ then x = y else x \<noteq> y"
        using bck xy by (rule implE)
    next
      assume tg: "\<not> tag_F f = F_EQ"
      have subTag: "\<not> tag_F (subst_F f i s) = F_EQ"
        by (rule tag_F_subst_F_neq[OF f i s tg])
      have xy: "x \<noteq> y"
        by (rule notcond_thenE[OF tg relation])
      have xyB: "(x \<noteq> y) B"
        by (rule neq_bool[OF x y])
      have relIff: "(if tag_F (subst_F f i s) = F_EQ then x = y else x \<noteq> y) \<longleftrightarrow> x \<noteq> y"
        by (rule condI2B[OF subTag xyB])
      have bck: "(x \<noteq> y) \<longrightarrow> (if tag_F (subst_F f i s) = F_EQ then x = y else x \<noteq> y)"
        by (rule iffE2[OF relIff])
      show "if tag_F (subst_F f i s) = F_EQ then x = y else x \<noteq> y"
        using bck xy by (rule implE)
    qed
    show "sat_fuel (subst_F f i s) A"
      by (rule sat_fuelI[OF x y leftNew rightNew subRelation])
  qed
qed

lemmas sat_fuel_subst_F = sat_fuel_subst_FD sat_fuel_subst_FI

definition sat_hyp_fuel :: "hyp \<Rightarrow> asn \<Rightarrow> o" where
  "sat_hyp_fuel G A \<equiv> \<forall>f. f \<in> G \<longrightarrow> sat_fuel f A"

lemma sat_hyp_fuel_mem:
  assumes f: "f N" and mem: "f \<in> G" and satG: "sat_hyp_fuel G A"
  shows "sat_fuel f A"
proof -
  have all: "\<forall>g. g \<in> G \<longrightarrow> sat_fuel g A"
    using satG unfolding sat_hyp_fuel_def .
  have step: "f \<in> G \<longrightarrow> sat_fuel f A"
    by (rule forallE[where a=f, OF all f])
  show ?thesis
    using step mem by (rule implE)
qed

lemma sat_hyp_fuel_nil:
  shows "sat_hyp_fuel Nil A"
  unfolding sat_hyp_fuel_def
proof (rule forallI)
  fix f
  assume f: "f N"
  show "f \<in> Nil \<longrightarrow> sat_fuel f A"
  proof (rule implI)
    show "(f \<in> Nil) B"
      by (rule mem_bool[OF f nil_nat])
  next
    assume mem: "f \<in> Nil"
    show "sat_fuel f A"
      by (rule exF[OF mem mem_nil])
  qed
qed

lemma sat_hyp_fuel_consI:
  assumes f: "f N" and G: "G N" and sf: "sat_fuel f A" and sG: "sat_hyp_fuel G A"
  shows "sat_hyp_fuel (f \<triangleright> G) A"
proof -
  show ?thesis
    unfolding sat_hyp_fuel_def
  proof (rule forallI)
    fix g
    assume g: "g N"
    show "g \<in> (f \<triangleright> G) \<longrightarrow> sat_fuel g A"
    proof (rule implI)
      show "g \<in> (f \<triangleright> G) B"
        by (rule mem_bool[OF g], use f G in simp)
    next
      assume mem: "g \<in> (f \<triangleright> G)"
      have split: "g \<in> (f \<triangleright> G) \<longleftrightarrow> (if f = g then True else g \<in> G)"
        by (rule mem_cons[OF f G g])
      have cond: "if f = g then True else g \<in> G"
        by (rule implE[OF iffE1[OF split] mem])
      show "sat_fuel g A"
      proof (rule cases_bool[where q="f = g"])
        show "(f = g) B"
          by (rule eqBool[OF f g])
      next
        assume fg: "f = g"
        show "sat_fuel g A"
          using fg sf by (rule eqSubst[where Q="\<lambda>z. sat_fuel z A"])
      next
        assume fg: "\<not> f = g"
        have gG: "g \<in> G"
          by (rule notcond_thenE[OF fg cond])
        show "sat_fuel g A"
          by (rule sat_hyp_fuel_mem[OF g gG sG])
      qed
    qed
  qed
qed

lemma fresh_T_var_ne:
  assumes i: "i N" and t: "t N" and fresh: "fresh_T i t" and tg: "tag_T t = T_VAR"
  shows "\<not> load_T t = i"
proof -
  have unfolded:
    "if tag_T t = T_VAR then load_T t < i = 1
     else if tag_T t = T_ZERO then True
     else if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    using fresh by (rule defI[OF fresh_T_def[where k=i and t=t]])
  have less: "load_T t < i = 1"
    by (rule cond_thenE[OF tg unfolded])
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  show ?thesis
    using less loadN i by simp
qed

lemma fresh_T_sucD:
  assumes i: "i N" and t: "t N" and fresh: "fresh_T i t" and tg: "tag_T t = T_SUC"
  shows "fresh_T i (load_T t)"
proof -
  have unfolded:
    "if tag_T t = T_VAR then load_T t < i = 1
     else if tag_T t = T_ZERO then True
     else if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    using fresh by (rule defI[OF fresh_T_def[where k=i and t=t]])
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have step1:
    "if tag_T t = T_ZERO then True
     else if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nvar unfolded])
  have step2:
    "if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nzero step1])
  show ?thesis
    by (rule cond_thenE[OF tg step2])
qed

lemma fresh_T_predD:
  assumes i: "i N" and t: "t N" and fresh: "fresh_T i t" and tg: "tag_T t = T_PRED"
  shows "fresh_T i (load_T t)"
proof -
  have unfolded:
    "if tag_T t = T_VAR then load_T t < i = 1
     else if tag_T t = T_ZERO then True
     else if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    using fresh by (rule defI[OF fresh_T_def[where k=i and t=t]])
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have step1:
    "if tag_T t = T_ZERO then True
     else if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nvar unfolded])
  have step2:
    "if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nzero step1])
  have step3:
    "if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nsuc step2])
  show ?thesis
    by (rule cond_thenE[OF tg step3])
qed

lemma fresh_T_ifzD:
  assumes i: "i N" and t: "t N" and fresh: "fresh_T i t" and tg: "tag_T t = T_IFZ"
  shows "fresh_T i (hyp_of (load_T t)) \<and>
    fresh_T i (hyp_of (conc_of (load_T t))) \<and>
    fresh_T i (conc_of (conc_of (load_T t)))"
proof -
  have unfolded:
    "if tag_T t = T_VAR then load_T t < i = 1
     else if tag_T t = T_ZERO then True
     else if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    using fresh by (rule defI[OF fresh_T_def[where k=i and t=t]])
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have npred: "\<not> tag_T t = T_PRED"
    using tg by simp
  have step1:
    "if tag_T t = T_ZERO then True
     else if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nvar unfolded])
  have step2:
    "if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nzero step1])
  have step3:
    "if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nsuc step2])
  have step4:
    "if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF npred step3])
  show ?thesis
    by (rule cond_thenE[OF tg step4])
qed

lemma fresh_T_appD:
  assumes i: "i N" and t: "t N" and fresh: "fresh_T i t"
      and nvar: "\<not> tag_T t = T_VAR" and nzero: "\<not> tag_T t = T_ZERO"
      and nsuc: "\<not> tag_T t = T_SUC" and npred: "\<not> tag_T t = T_PRED"
      and nifz: "\<not> tag_T t = T_IFZ"
  shows "fresh_T i (hyp_of (conc_of (load_T t))) \<and>
    fresh_T i (conc_of (conc_of (load_T t)))"
proof -
  have unfolded:
    "if tag_T t = T_VAR then load_T t < i = 1
     else if tag_T t = T_ZERO then True
     else if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    using fresh by (rule defI[OF fresh_T_def[where k=i and t=t]])
  have step1:
    "if tag_T t = T_ZERO then True
     else if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nvar unfolded])
  have step2:
    "if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nzero step1])
  have step3:
    "if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nsuc step2])
  have step4:
    "if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF npred step3])
  have step5:
    "if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nifz step4])
  have tagN: "tag_T t N"
    by (rule tag_T_N[OF t])
  have appB: "(tag_T t = T_APP) B"
    by (rule eqBool[OF tagN], simp)
  show ?thesis
  proof (rule cases_bool[where q="tag_T t = T_APP"])
    show "(tag_T t = T_APP) B"
      by (rule appB)
  next
    assume tg: "tag_T t = T_APP"
    show ?thesis
      by (rule cond_thenE[OF tg step5])
  next
    assume ntg: "\<not> tag_T t = T_APP"
    have bot: "False"
      by (rule notcond_thenE[OF ntg step5])
    show ?thesis
      by (rule exF[OF bot], simp)
  qed
qed

lemma fresh_FD:
  assumes i: "i N" and f: "f N" and fresh: "fresh_F i f"
  shows "fresh_T i (hyp_of (load_F f)) \<and> fresh_T i (conc_of (load_F f))"
proof -
  show ?thesis
    using fresh by (rule defI[OF fresh_F_def[where k=i and f=f]])
qed

lemma eval_fuel_fresh_put:
  assumes k: "k N" and t: "t N" and i: "i N" and A: "A N" and v: "v N"
      and fresh: "fresh_T i t" and run: "eval_fuel k t A = S r"
  shows "eval_fuel k t (asn_put A i v) = S r"
proof -
  have putN: "asn_put A i v N"
    by (rule asn_put_N[OF A i v])
  have main: "\<forall>u. \<forall>q. fresh_T i u \<longrightarrow> (eval_fuel k u A = S q) \<longrightarrow> eval_fuel k u (asn_put A i v) = S q"
  proof (rule ind[OF k])
    show "\<forall>u. \<forall>q. fresh_T i u \<longrightarrow> (eval_fuel 0 u A = S q) \<longrightarrow> eval_fuel 0 u (asn_put A i v) = S q"
    proof (rule forallI)
      fix u
      assume u: "u N"
      show "\<forall>q. fresh_T i u \<longrightarrow> (eval_fuel 0 u A = S q) \<longrightarrow> eval_fuel 0 u (asn_put A i v) = S q"
      proof (rule forallI)
        fix q
        assume q: "q N"
        show "fresh_T i u \<longrightarrow> (eval_fuel 0 u A = S q) \<longrightarrow> eval_fuel 0 u (asn_put A i v) = S q"
        proof (rule implI)
          show "fresh_T i u B"
            by (rule fresh_T_bool[OF i u])
        next
          assume freshU: "fresh_T i u"
          show "(eval_fuel 0 u A = S q) \<longrightarrow> eval_fuel 0 u (asn_put A i v) = S q"
          proof (rule implI)
            have evalN: "eval_fuel 0 u A N"
              by (rule eval_fuel_N[OF nat0 u A])
            have sqN: "S q N"
              by (rule natS[OF q])
            show "(eval_fuel 0 u A = S q) B"
              by (rule eqBool[OF evalN sqN])
          next
            assume success: "eval_fuel 0 u A = S q"
            have timeout: "eval_fuel 0 u A = 0"
              by (rule eval_fuel_zero)
            show "eval_fuel 0 u (asn_put A i v) = S q"
              by (rule zero_successE[OF timeout success])
          qed
        qed
      qed
    qed
  next
    fix n
    assume n: "n N"
    assume IH: "\<forall>u. \<forall>q. fresh_T i u \<longrightarrow> (eval_fuel n u A = S q) \<longrightarrow> eval_fuel n u (asn_put A i v) = S q"
    show "\<forall>u. \<forall>q. fresh_T i u \<longrightarrow> (eval_fuel (S n) u A = S q) \<longrightarrow> eval_fuel (S n) u (asn_put A i v) = S q"
    proof (rule forallI)
      fix u
      assume u: "u N"
      show "\<forall>q. fresh_T i u \<longrightarrow> (eval_fuel (S n) u A = S q) \<longrightarrow> eval_fuel (S n) u (asn_put A i v) = S q"
      proof (rule forallI)
        fix q
        assume q: "q N"
        show "fresh_T i u \<longrightarrow> (eval_fuel (S n) u A = S q) \<longrightarrow> eval_fuel (S n) u (asn_put A i v) = S q"
        proof (rule implI)
          show "fresh_T i u B"
            by (rule fresh_T_bool[OF i u])
        next
          assume freshU: "fresh_T i u"
          show "(eval_fuel (S n) u A = S q) \<longrightarrow> eval_fuel (S n) u (asn_put A i v) = S q"
          proof (rule implI)
            have sn: "S n N"
              by (rule natS[OF n])
            have evalN: "eval_fuel (S n) u A N"
              by (rule eval_fuel_N[OF sn u A])
            have sqN: "S q N"
              by (rule natS[OF q])
            show "(eval_fuel (S n) u A = S q) B"
              by (rule eqBool[OF evalN sqN])
          next
            assume result: "eval_fuel (S n) u A = S q"
            have IHmeta: "\<And>w z. w N \<Longrightarrow> fresh_T i w \<Longrightarrow> eval_fuel n w A = S z \<Longrightarrow> eval_fuel n w (asn_put A i v) = S z"
            proof -
              fix w z
              assume w: "w N" and freshW: "fresh_T i w" and success: "eval_fuel n w A = S z"
              have z: "z N"
                by (rule eval_fuel_result_N[OF n w A success])
              have IHw: "\<forall>z. fresh_T i w \<longrightarrow> (eval_fuel n w A = S z) \<longrightarrow> eval_fuel n w (asn_put A i v) = S z"
                by (rule forallE[where a=w, OF IH w])
              have IHwz: "fresh_T i w \<longrightarrow> (eval_fuel n w A = S z) \<longrightarrow> eval_fuel n w (asn_put A i v) = S z"
                by (rule forallE[where a=z, OF IHw z])
              have successImp: "(eval_fuel n w A = S z) \<longrightarrow> eval_fuel n w (asn_put A i v) = S z"
                using IHwz freshW by (rule implE)
              show "eval_fuel n w (asn_put A i v) = S z"
                using successImp success by (rule implE)
            qed
            have loadN: "load_T u N"
              by (rule load_T_N[OF u])
            have condN: "hyp_of (load_T u) N"
              by (rule cpx_terminates[OF loadN])
            have tailN: "conc_of (load_T u) N"
              by (rule cpy_terminates[OF loadN])
            have leftN: "hyp_of (conc_of (load_T u)) N"
              by (rule cpx_terminates[OF tailN])
            have rightN: "conc_of (conc_of (load_T u)) N"
              by (rule cpy_terminates[OF tailN])
            have tagN: "tag_T u N"
              by (rule tag_T_N[OF u])
            have varB: "(tag_T u = T_VAR) B"
              by (rule eqBool[OF tagN], simp)
            have zeroB: "(tag_T u = T_ZERO) B"
              by (rule eqBool[OF tagN], simp)
            have sucB: "(tag_T u = T_SUC) B"
              by (rule eqBool[OF tagN], simp)
            have predB: "(tag_T u = T_PRED) B"
              by (rule eqBool[OF tagN], simp)
            have ifzB: "(tag_T u = T_IFZ) B"
              by (rule eqBool[OF tagN], simp)
            show "eval_fuel (S n) u (asn_put A i v) = S q"
            proof (rule cases_bool[where q="tag_T u = T_VAR"])
              show "(tag_T u = T_VAR) B"
                by (rule varB)
            next
              assume tg: "tag_T u = T_VAR"
              have ne: "\<not> load_T u = i"
                by (rule fresh_T_var_ne[OF i u freshU tg])
              have nthAN: "nth (load_T u) A N"
                by (rule nth_N'[OF A loadN])
              have nthPutN: "nth (load_T u) (asn_put A i v) N"
                by (rule nth_N'[OF putN loadN])
              have nthSame: "nth (load_T u) (asn_put A i v) = nth (load_T u) A"
                by (rule nth_put_ne[OF A i v loadN ne])
              have oldValue: "eval_fuel (S n) u A = S (nth (load_T u) A)"
                by (rule eval_fuel_var[OF n tg nthAN])
              have resultEq: "S (nth (load_T u) A) = S q"
                by (rule same_success[OF oldValue result])
              have newValue: "eval_fuel (S n) u (asn_put A i v) = S (nth (load_T u) (asn_put A i v))"
                by (rule eval_fuel_var[OF n tg nthPutN])
              have newOld: "eval_fuel (S n) u (asn_put A i v) = S (nth (load_T u) A)"
                using newValue sucCong[OF nthSame] by (rule eq_trans)
              show "eval_fuel (S n) u (asn_put A i v) = S q"
                using newOld resultEq by (rule eq_trans)
            next
              assume nvar: "\<not> tag_T u = T_VAR"
              show "eval_fuel (S n) u (asn_put A i v) = S q"
              proof (rule cases_bool[where q="tag_T u = T_ZERO"])
                show "(tag_T u = T_ZERO) B"
                  by (rule zeroB)
              next
                assume tg: "tag_T u = T_ZERO"
                have oldValue: "eval_fuel (S n) u A = S 0"
                  by (rule eval_fuel_zero_step[OF n tg])
                have resultEq: "S 0 = S q"
                  by (rule same_success[OF oldValue result])
                have newValue: "eval_fuel (S n) u (asn_put A i v) = S 0"
                  by (rule eval_fuel_zero_step[OF n tg])
                show "eval_fuel (S n) u (asn_put A i v) = S q"
                  using newValue resultEq by (rule eq_trans)
              next
                assume nzero: "\<not> tag_T u = T_ZERO"
                show "eval_fuel (S n) u (asn_put A i v) = S q"
                proof (rule cases_bool[where q="tag_T u = T_SUC"])
                  show "(tag_T u = T_SUC) B"
                    by (rule sucB)
                next
                  assume tg: "tag_T u = T_SUC"
                  have freshChild: "fresh_T i (load_T u)"
                    by (rule fresh_T_sucD[OF i u freshU tg])
                  have childEvalN: "eval_fuel n (load_T u) A N"
                    by (rule eval_fuel_N[OF n loadN A])
                  show "eval_fuel (S n) u (asn_put A i v) = S q"
                  proof (rule cases_nat_2[where x="eval_fuel n (load_T u) A"])
                    show "eval_fuel n (load_T u) A N"
                      by (rule childEvalN)
                  next
                    assume childTimeout: "eval_fuel n (load_T u) A = 0"
                    have timeout: "eval_fuel (S n) u A = 0"
                      by (rule eval_fuel_suc_timeout[OF n tg childTimeout])
                    show "eval_fuel (S n) u (asn_put A i v) = S q"
                      by (rule zero_successE[OF timeout result])
                  next
                    fix z
                    assume z: "z N" and childSuccess: "eval_fuel n (load_T u) A = S z"
                    have childNew: "eval_fuel n (load_T u) (asn_put A i v) = S z"
                      by (rule IHmeta[OF loadN freshChild childSuccess])
                    have oldValue: "eval_fuel (S n) u A = S (S z)"
                      by (rule eval_fuel_suc_value[OF n tg childSuccess])
                    have resultEq: "S (S z) = S q"
                      by (rule same_success[OF oldValue result])
                    have newValue: "eval_fuel (S n) u (asn_put A i v) = S (S z)"
                      by (rule eval_fuel_suc_value[OF n tg childNew])
                    show "eval_fuel (S n) u (asn_put A i v) = S q"
                      using newValue resultEq by (rule eq_trans)
                  qed
                next
                  assume nsuc: "\<not> tag_T u = T_SUC"
                  show "eval_fuel (S n) u (asn_put A i v) = S q"
                  proof (rule cases_bool[where q="tag_T u = T_PRED"])
                    show "(tag_T u = T_PRED) B"
                      by (rule predB)
                  next
                    assume tg: "tag_T u = T_PRED"
                    have freshChild: "fresh_T i (load_T u)"
                      by (rule fresh_T_predD[OF i u freshU tg])
                    have childEvalN: "eval_fuel n (load_T u) A N"
                      by (rule eval_fuel_N[OF n loadN A])
                    show "eval_fuel (S n) u (asn_put A i v) = S q"
                    proof (rule cases_nat_2[where x="eval_fuel n (load_T u) A"])
                      show "eval_fuel n (load_T u) A N"
                        by (rule childEvalN)
                    next
                      assume childTimeout: "eval_fuel n (load_T u) A = 0"
                      have timeout: "eval_fuel (S n) u A = 0"
                        by (rule eval_fuel_pred_timeout[OF n tg childTimeout])
                      show "eval_fuel (S n) u (asn_put A i v) = S q"
                        by (rule zero_successE[OF timeout result])
                    next
                      fix z
                      assume z: "z N" and childSuccess: "eval_fuel n (load_T u) A = S z"
                      have childNew: "eval_fuel n (load_T u) (asn_put A i v) = S z"
                        by (rule IHmeta[OF loadN freshChild childSuccess])
                      have oldValue: "eval_fuel (S n) u A = S (P z)"
                        by (rule eval_fuel_pred_value[OF n tg childSuccess])
                      have resultEq: "S (P z) = S q"
                        by (rule same_success[OF oldValue result])
                      have newValue: "eval_fuel (S n) u (asn_put A i v) = S (P z)"
                        by (rule eval_fuel_pred_value[OF n tg childNew])
                      show "eval_fuel (S n) u (asn_put A i v) = S q"
                        using newValue resultEq by (rule eq_trans)
                    qed
                  next
                    assume npred: "\<not> tag_T u = T_PRED"
                    show "eval_fuel (S n) u (asn_put A i v) = S q"
                    proof (rule cases_bool[where q="tag_T u = T_IFZ"])
                      show "(tag_T u = T_IFZ) B"
                        by (rule ifzB)
                    next
                      assume tg: "tag_T u = T_IFZ"
                      have freshParts: "fresh_T i (hyp_of (load_T u)) \<and> fresh_T i (hyp_of (conc_of (load_T u))) \<and> fresh_T i (conc_of (conc_of (load_T u)))"
                        by (rule fresh_T_ifzD[OF i u freshU tg])
                      have freshCondThen:
                        "fresh_T i (hyp_of (load_T u)) \<and>
                         fresh_T i (hyp_of (conc_of (load_T u)))"
                        by (rule conjE1[OF freshParts])
                      have freshCond: "fresh_T i (hyp_of (load_T u))"
                        by (rule conjE1[OF freshCondThen])
                      have freshThen: "fresh_T i (hyp_of (conc_of (load_T u)))"
                        by (rule conjE2[OF freshCondThen])
                      have freshElse: "fresh_T i (conc_of (conc_of (load_T u)))"
                        by (rule conjE2[OF freshParts])
                      have condEvalN: "eval_fuel n (hyp_of (load_T u)) A N"
                        by (rule eval_fuel_N[OF n condN A])
                      show "eval_fuel (S n) u (asn_put A i v) = S q"
                      proof (rule cases_nat_2[where x="eval_fuel n (hyp_of (load_T u)) A"])
                        show "eval_fuel n (hyp_of (load_T u)) A N"
                          by (rule condEvalN)
                      next
                        assume condTimeout: "eval_fuel n (hyp_of (load_T u)) A = 0"
                        have timeout: "eval_fuel (S n) u A = 0"
                          by (rule eval_fuel_ifz_cond_timeout[OF n tg condTimeout])
                        show "eval_fuel (S n) u (asn_put A i v) = S q"
                          by (rule zero_successE[OF timeout result])
                      next
                        fix c
                        assume c: "c N" and condSuccess: "eval_fuel n (hyp_of (load_T u)) A = S c"
                        show "eval_fuel (S n) u (asn_put A i v) = S q"
                        proof (rule cases_nat_2[where x=c])
                          show "c N"
                            by (rule c)
                        next
                          assume cz: "c = 0"
                          have condZero: "eval_fuel n (hyp_of (load_T u)) A = S 0"
                            using condSuccess sucCong[OF cz] by (rule eq_trans)
                          have thenEvalN: "eval_fuel n (hyp_of (conc_of (load_T u))) A N"
                            by (rule eval_fuel_N[OF n leftN A])
                          show "eval_fuel (S n) u (asn_put A i v) = S q"
                          proof (rule cases_nat_2[where x="eval_fuel n (hyp_of (conc_of (load_T u))) A"])
                            show "eval_fuel n (hyp_of (conc_of (load_T u))) A N"
                              by (rule thenEvalN)
                          next
                            assume thenTimeout: "eval_fuel n (hyp_of (conc_of (load_T u))) A = 0"
                            have step: "eval_fuel (S n) u A = eval_fuel n (hyp_of (conc_of (load_T u))) A"
                              by (rule eval_fuel_ifz_zero[OF n tg condZero thenEvalN])
                            have timeout: "eval_fuel (S n) u A = 0"
                              using step thenTimeout by (rule eq_trans)
                            show "eval_fuel (S n) u (asn_put A i v) = S q"
                              by (rule zero_successE[OF timeout result])
                          next
                            fix z
                            assume z: "z N" and thenSuccess: "eval_fuel n (hyp_of (conc_of (load_T u))) A = S z"
                            have condNew: "eval_fuel n (hyp_of (load_T u)) (asn_put A i v) = S 0"
                              by (rule IHmeta[OF condN freshCond condZero])
                            have thenNew: "eval_fuel n (hyp_of (conc_of (load_T u))) (asn_put A i v) = S z"
                              by (rule IHmeta[OF leftN freshThen thenSuccess])
                            have oldValue: "eval_fuel (S n) u A = S z"
                              by (rule eval_fuel_ifz_zero_value[OF n tg condZero thenSuccess])
                            have resultEq: "S z = S q"
                              by (rule same_success[OF oldValue result])
                            have newValue: "eval_fuel (S n) u (asn_put A i v) = S z"
                              by (rule eval_fuel_ifz_zero_value[OF n tg condNew thenNew])
                            show "eval_fuel (S n) u (asn_put A i v) = S q"
                              using newValue resultEq by (rule eq_trans)
                          qed
                        next
                          fix d
                          assume d: "d N" and cnz: "c = S d"
                          have condNonzero: "eval_fuel n (hyp_of (load_T u)) A = S (S d)"
                            using condSuccess sucCong[OF cnz] by (rule eq_trans)
                          have elseEvalN: "eval_fuel n (conc_of (conc_of (load_T u))) A N"
                            by (rule eval_fuel_N[OF n rightN A])
                          show "eval_fuel (S n) u (asn_put A i v) = S q"
                          proof (rule cases_nat_2[where x="eval_fuel n (conc_of (conc_of (load_T u))) A"])
                            show "eval_fuel n (conc_of (conc_of (load_T u))) A N"
                              by (rule elseEvalN)
                          next
                            assume elseTimeout: "eval_fuel n (conc_of (conc_of (load_T u))) A = 0"
                            have step: "eval_fuel (S n) u A = eval_fuel n (conc_of (conc_of (load_T u))) A"
                              by (rule eval_fuel_ifz_nonzero[OF n tg condNonzero elseEvalN])
                            have timeout: "eval_fuel (S n) u A = 0"
                              using step elseTimeout by (rule eq_trans)
                            show "eval_fuel (S n) u (asn_put A i v) = S q"
                              by (rule zero_successE[OF timeout result])
                          next
                            fix z
                            assume z: "z N" and elseSuccess: "eval_fuel n (conc_of (conc_of (load_T u))) A = S z"
                            have condNew: "eval_fuel n (hyp_of (load_T u)) (asn_put A i v) = S (S d)"
                              by (rule IHmeta[OF condN freshCond condNonzero])
                            have elseNew: "eval_fuel n (conc_of (conc_of (load_T u))) (asn_put A i v) = S z"
                              by (rule IHmeta[OF rightN freshElse elseSuccess])
                            have oldValue: "eval_fuel (S n) u A = S z"
                              by (rule eval_fuel_ifz_nonzero_value[OF n tg condNonzero elseSuccess])
                            have resultEq: "S z = S q"
                              by (rule same_success[OF oldValue result])
                            have newValue: "eval_fuel (S n) u (asn_put A i v) = S z"
                              by (rule eval_fuel_ifz_nonzero_value[OF n tg condNew elseNew])
                            show "eval_fuel (S n) u (asn_put A i v) = S q"
                              using newValue resultEq by (rule eq_trans)
                          qed
                        qed
                      qed
                    next
                      assume nifz: "\<not> tag_T u = T_IFZ"
                      have freshArgs: "fresh_T i (hyp_of (conc_of (load_T u))) \<and> fresh_T i (conc_of (conc_of (load_T u)))"
                        by (rule fresh_T_appD[OF i u freshU nvar nzero nsuc npred nifz])
                      have freshArg1: "fresh_T i (hyp_of (conc_of (load_T u)))"
                        by (rule conjE1[OF freshArgs])
                      have freshArg2: "fresh_T i (conc_of (conc_of (load_T u)))"
                        by (rule conjE2[OF freshArgs])
                      have arg1EvalN: "eval_fuel n (hyp_of (conc_of (load_T u))) A N"
                        by (rule eval_fuel_N[OF n leftN A])
                      show "eval_fuel (S n) u (asn_put A i v) = S q"
                      proof (rule cases_nat_2[where x="eval_fuel n (hyp_of (conc_of (load_T u))) A"])
                        show "eval_fuel n (hyp_of (conc_of (load_T u))) A N"
                          by (rule arg1EvalN)
                      next
                        assume arg1Timeout: "eval_fuel n (hyp_of (conc_of (load_T u))) A = 0"
                        have timeout: "eval_fuel (S n) u A = 0"
                          by (rule eval_fuel_app_arg1_timeout[OF n nvar nzero nsuc npred nifz arg1Timeout])
                        show "eval_fuel (S n) u (asn_put A i v) = S q"
                          by (rule zero_successE[OF timeout result])
                      next
                        fix x
                        assume x: "x N" and arg1Success: "eval_fuel n (hyp_of (conc_of (load_T u))) A = S x"
                        have arg2EvalN: "eval_fuel n (conc_of (conc_of (load_T u))) A N"
                          by (rule eval_fuel_N[OF n rightN A])
                        show "eval_fuel (S n) u (asn_put A i v) = S q"
                        proof (rule cases_nat_2[where x="eval_fuel n (conc_of (conc_of (load_T u))) A"])
                          show "eval_fuel n (conc_of (conc_of (load_T u))) A N"
                            by (rule arg2EvalN)
                        next
                          assume arg2Timeout: "eval_fuel n (conc_of (conc_of (load_T u))) A = 0"
                          have timeout: "eval_fuel (S n) u A = 0"
                            by (rule eval_fuel_app_arg2_timeout[OF n nvar nzero nsuc npred nifz arg1Success arg2Timeout])
                          show "eval_fuel (S n) u (asn_put A i v) = S q"
                            by (rule zero_successE[OF timeout result])
                        next
                          fix y
                          assume y: "y N" and arg2Success: "eval_fuel n (conc_of (conc_of (load_T u))) A = S y"
                          let ?dfn = "hyp_of (load_T u)"
                          have dfnN: "?dfn N"
                            by (rule cpx_terminates[OF loadN])
                          have appAsnN: "x \<triangleright> y \<triangleright> Nil N"
                            using x y by simp
                          have bodyTermN: "nth ?dfn dfns N"
                            by (rule nth_N'[OF dfns_N dfnN])
                          have bodyEvalN: "eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) N"
                            by (rule eval_fuel_N[OF n bodyTermN appAsnN])
                          show "eval_fuel (S n) u (asn_put A i v) = S q"
                          proof (rule cases_nat_2[where x="eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil)"])
                            show "eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) N"
                              by (rule bodyEvalN)
                          next
                            assume bodyTimeout: "eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) = 0"
                            have timeout: "eval_fuel (S n) u A = 0"
                              by (rule eval_fuel_app_body_timeout[OF n nvar nzero nsuc npred nifz arg1Success arg2Success bodyTimeout])
                            show "eval_fuel (S n) u (asn_put A i v) = S q"
                              by (rule zero_successE[OF timeout result])
                          next
                            fix z
                            assume z: "z N" and bodySuccess: "eval_fuel n (nth ?dfn dfns) (x \<triangleright> y \<triangleright> Nil) = S z"
                            have arg1New: "eval_fuel n (hyp_of (conc_of (load_T u))) (asn_put A i v) = S x"
                              by (rule IHmeta[OF leftN freshArg1 arg1Success])
                            have arg2New: "eval_fuel n (conc_of (conc_of (load_T u))) (asn_put A i v) = S y"
                              by (rule IHmeta[OF rightN freshArg2 arg2Success])
                            have oldValue: "eval_fuel (S n) u A = S z"
                              by (rule eval_fuel_app_value[OF n nvar nzero nsuc npred nifz arg1Success arg2Success bodySuccess])
                            have resultEq: "S z = S q"
                              by (rule same_success[OF oldValue result])
                            have newValue: "eval_fuel (S n) u (asn_put A i v) = S z"
                              by (rule eval_fuel_app_value[OF n nvar nzero nsuc npred nifz arg1New arg2New bodySuccess])
                            show "eval_fuel (S n) u (asn_put A i v) = S q"
                              using newValue resultEq by (rule eq_trans)
                          qed
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  have r: "r N"
    by (rule eval_fuel_result_N[OF k t A run])
  have mainT: "\<forall>q. fresh_T i t \<longrightarrow> (eval_fuel k t A = S q) \<longrightarrow> eval_fuel k t (asn_put A i v) = S q"
    by (rule forallE[where a=t, OF main t])
  have mainR: "fresh_T i t \<longrightarrow> (eval_fuel k t A = S r) \<longrightarrow> eval_fuel k t (asn_put A i v) = S r"
    by (rule forallE[where a=r, OF mainT r])
  have runImp: "(eval_fuel k t A = S r) \<longrightarrow> eval_fuel k t (asn_put A i v) = S r"
    using mainR fresh by (rule implE)
  show ?thesis
    using runImp run by (rule implE)
qed

lemma evals_fresh_put:
  assumes t: "t N" and i: "i N" and A: "A N" and v: "v N"
      and fresh: "fresh_T i t" and ev: "evals t A r"
  shows "evals t (asn_put A i v) r"
proof -
  show ?thesis
    using ev
  proof (rule evalsE)
    fix k
    assume k: "k N" and run: "eval_fuel k t A = S r"
    have transported: "eval_fuel k t (asn_put A i v) = S r"
      by (rule eval_fuel_fresh_put[OF k t i A v fresh run])
    show "evals t (asn_put A i v) r"
      by (rule evalsI[OF k transported])
  qed
qed

lemma sat_fuel_fresh_put:
  assumes f: "f N" and i: "i N" and A: "A N" and v: "v N"
      and fresh: "fresh_F i f" and sat: "sat_fuel f A"
  shows "sat_fuel f (asn_put A i v)"
proof -
  let ?left = "hyp_of (load_F f)"
  let ?right = "conc_of (load_F f)"
  have loadN: "load_F f N"
    by (rule load_F_N[OF f])
  have leftN: "?left N"
    by (rule cpx_terminates[OF loadN])
  have rightN: "?right N"
    by (rule cpy_terminates[OF loadN])
  have freshParts: "fresh_T i ?left \<and> fresh_T i ?right"
    by (rule fresh_FD[OF i f fresh])
  have freshLeft: "fresh_T i ?left"
    by (rule conjE1[OF freshParts])
  have freshRight: "fresh_T i ?right"
    by (rule conjE2[OF freshParts])
  show ?thesis
    using sat
  proof (rule sat_fuelE)
    fix x y
    assume x: "x N" and y: "y N"
        and left: "evals ?left A x"
        and right: "evals ?right A y"
        and relation: "if tag_F f = F_EQ then x = y else x \<noteq> y"
    have leftNew: "evals ?left (asn_put A i v) x"
      by (rule evals_fresh_put[OF leftN i A v freshLeft left])
    have rightNew: "evals ?right (asn_put A i v) y"
      by (rule evals_fresh_put[OF rightN i A v freshRight right])
    show "sat_fuel f (asn_put A i v)"
      by (rule sat_fuelI[OF x y leftNew rightNew relation])
  qed
qed

lemma sat_hyp_fuel_put:
  assumes G: "G N" and i: "i N" and A: "A N" and v: "v N"
      and fresh: "fresh_H i G" and satG: "sat_hyp_fuel G A"
  shows "sat_hyp_fuel G (asn_put A i v)"
  unfolding sat_hyp_fuel_def
proof (rule forallI)
  fix f
  assume f: "f N"
  show "f \<in> G \<longrightarrow> sat_fuel f (asn_put A i v)"
  proof (rule implI)
    show "(f \<in> G) B"
      by (rule mem_bool[OF f G])
  next
    assume mem: "f \<in> G"
    have freshF: "fresh_F i f"
      by (rule fresh_H_mem[OF i G f fresh mem])
    have satF: "sat_fuel f A"
      by (rule sat_hyp_fuel_mem[OF f mem satG])
    show "sat_fuel f (asn_put A i v)"
      by (rule sat_fuel_fresh_put[OF f i A v freshF satF])
  qed
qed

lemma evals_appI:
  assumes d: "d N" and a: "a N" and b: "b N" and A: "A N"
      and eva: "evals a A x" and evb: "evals b A y"
      and body: "evals (nth d dfns) (x \<triangleright> y \<triangleright> Nil) r"
  shows "evals (pack_T T_APP \<langle>d, \<langle>a, b\<rangle>\<rangle>) A r"
proof -
  let ?args = "\<langle>a, b\<rangle>"
  let ?payload = "\<langle>d, ?args\<rangle>"
  let ?app = "pack_T T_APP ?payload"
  have x: "x N"
    by (rule evals_result_N[OF a A eva])
  have y: "y N"
    by (rule evals_result_N[OF b A evb])
  have argsN: "?args N"
    using a b by simp
  have payloadN: "?payload N"
    using d argsN by simp
  have tappN: "T_APP N"
    by simp
  have appN: "?app N"
    by (rule pack_T_N[OF tappN payloadN])
  have tagApp: "tag_T ?app = T_APP"
    by (rule tag_pack_T[OF tappN payloadN])
  have nvar: "\<not> tag_T ?app = T_VAR"
    using tagApp by simp
  have nzero: "\<not> tag_T ?app = T_ZERO"
    using tagApp by simp
  have nsuc: "\<not> tag_T ?app = T_SUC"
    using tagApp by simp
  have npred: "\<not> tag_T ?app = T_PRED"
    using tagApp by simp
  have nifz: "\<not> tag_T ?app = T_IFZ"
    using tagApp by simp
  have loadApp: "load_T ?app = ?payload"
    by (rule load_pack_T[OF tappN payloadN])
  have payloadDfn: "hyp_of ?payload = d"
    by (rule cpx_proj[OF d argsN])
  have payloadArgs: "conc_of ?payload = ?args"
    by (rule cpy_proj[OF d argsN])
  have argsLeft: "hyp_of ?args = a"
    by (rule cpx_proj[OF a b])
  have argsRight: "conc_of ?args = b"
    by (rule cpy_proj[OF a b])
  have selectDfn: "hyp_of (load_T ?app) = d"
    by (rule eqSubst[where a="?payload" and b="load_T ?app" and Q="\<lambda>z. hyp_of z = d", OF eqSym[OF loadApp] payloadDfn])
  have selectArgs: "conc_of (load_T ?app) = ?args"
    by (rule eqSubst[where a="?payload" and b="load_T ?app" and Q="\<lambda>z. conc_of z = ?args", OF eqSym[OF loadApp] payloadArgs])
  have selectLeft: "hyp_of (conc_of (load_T ?app)) = a"
    by (rule eqSubst[where a="?args" and b="conc_of (load_T ?app)" and Q="\<lambda>z. hyp_of z = a", OF eqSym[OF selectArgs] argsLeft])
  have selectRight: "conc_of (conc_of (load_T ?app)) = b"
    by (rule eqSubst[where a="?args" and b="conc_of (load_T ?app)" and Q="\<lambda>z. conc_of z = b", OF eqSym[OF selectArgs] argsRight])
  show ?thesis
    using eva
  proof (rule evalsE)
    fix ka
    assume ka: "ka N" and runA: "eval_fuel ka a A = S x"
    show "evals ?app A r"
      using evb
    proof (rule evalsE)
      fix kb
      assume kb: "kb N" and runB: "eval_fuel kb b A = S y"
      show "evals ?app A r"
        using body
      proof (rule evalsE)
        fix kc
        assume kc: "kc N" and runBody: "eval_fuel kc (nth d dfns) (x \<triangleright> y \<triangleright> Nil) = S r"
        let ?K = "(ka + kb) + kc"
        have kabN: "ka + kb N"
          by (rule add_terminates[OF ka kb])
        have KN: "?K N"
          by (rule add_terminates[OF kabN kc])
        have kbkcN: "kb + kc N"
          by (rule add_terminates[OF kb kc])
        have kakcN: "ka + kc N"
          by (rule add_terminates[OF ka kc])
        have appAsnN: "x \<triangleright> y \<triangleright> Nil N"
          using x y by simp
        have runA0: "eval_fuel (ka + (kb + kc)) a A = S x"
          by (rule eval_fuel_success_add[OF ka kbkcN a A runA])
        have assocA: "(ka + kb) + kc = ka + (kb + kc)"
          by (rule add_assoc[OF ka kb kc])
        have runAK: "eval_fuel ?K a A = S x"
          by (rule eqSubst[where a="ka + (kb + kc)" and b="?K" and Q="\<lambda>z. eval_fuel z a A = S x", OF eqSym[OF assocA] runA0])
        have runB0: "eval_fuel (kb + (ka + kc)) b A = S y"
          by (rule eval_fuel_success_add[OF kb kakcN b A runB])
        have assocB: "(kb + ka) + kc = kb + (ka + kc)"
          by (rule add_assoc[OF kb ka kc])
        have commBA: "kb + ka = ka + kb"
          by (rule add_comm[OF kb ka])
        have leftEq: "(kb + ka) + kc = (ka + kb) + kc"
          using commBA ka kb kc by simp
        have fuelB: "kb + (ka + kc) = ?K"
          using eqSym[OF assocB] leftEq by (rule eq_trans)
        have runBK: "eval_fuel ?K b A = S y"
          by (rule eqSubst[where a="kb + (ka + kc)" and b="?K" and Q="\<lambda>z. eval_fuel z b A = S y", OF fuelB runB0])
        have runBody0: "eval_fuel (kc + (ka + kb)) (nth d dfns) (x \<triangleright> y \<triangleright> Nil) = S r"
          by (rule eval_fuel_success_add[OF kc kabN nth_N'[OF dfns_N d] appAsnN runBody])
        have fuelBody: "kc + (ka + kb) = ?K"
          by (rule add_comm[OF kc kabN])
        have runBodyK: "eval_fuel ?K (nth d dfns) (x \<triangleright> y \<triangleright> Nil) = S r"
          by (rule eqSubst[where a="kc + (ka + kb)" and b="?K" and Q="\<lambda>z. eval_fuel z (nth d dfns) (x \<triangleright> y \<triangleright> Nil) = S r", OF fuelBody runBody0])
        have packedLeft: "eval_fuel ?K (hyp_of (conc_of (load_T ?app))) A = S x"
          by (rule eqSubst[where a=a and b="hyp_of (conc_of (load_T ?app))" and Q="\<lambda>z. eval_fuel ?K z A = S x", OF eqSym[OF selectLeft] runAK])
        have packedRight: "eval_fuel ?K (conc_of (conc_of (load_T ?app))) A = S y"
          by (rule eqSubst[where a=b and b="conc_of (conc_of (load_T ?app))" and Q="\<lambda>z. eval_fuel ?K z A = S y", OF eqSym[OF selectRight] runBK])
        have packedBody: "eval_fuel ?K (nth (hyp_of (load_T ?app)) dfns) (x \<triangleright> y \<triangleright> Nil) = S r"
          by (rule eqSubst[where a=d and b="hyp_of (load_T ?app)" and Q="\<lambda>z. eval_fuel ?K (nth z dfns) (x \<triangleright> y \<triangleright> Nil) = S r", OF eqSym[OF selectDfn] runBodyK])
        have appRun: "eval_fuel (S ?K) ?app A = S r"
          by (rule eval_fuel_app_value[OF KN nvar nzero nsuc npred nifz packedLeft packedRight packedBody])
        show "evals ?app A r"
          by (rule evalsI[OF natS[OF KN] appRun])
      qed
    qed
  qed
qed

lemma sat_fuel_formula_eqE:
  assumes f: "f N" and tg: "tag_F f = F_EQ" and sat: "sat_fuel f A"
      and H: "\<And>x y. x N \<Longrightarrow> y N \<Longrightarrow>
        evals (hyp_of (load_F f)) A x \<Longrightarrow>
        evals (conc_of (load_F f)) A y \<Longrightarrow> x = y \<Longrightarrow> R"
  shows R
proof -
  show R
    using sat
  proof (rule sat_fuelE)
    fix x y
    assume x: "x N" and y: "y N"
        and left: "evals (hyp_of (load_F f)) A x"
        and right: "evals (conc_of (load_F f)) A y"
        and relation: "if tag_F f = F_EQ then x = y else x \<noteq> y"
    have xy: "x = y"
      by (rule cond_thenE[OF tg relation])
    show R
      by (rule H[OF x y left right xy])
  qed
qed

lemma sat_fuel_reflE:
  assumes a: "a N" and sat: "sat_fuel (pack_F F_EQ \<langle>a, a\<rangle>) A"
      and H: "\<And>x. x N \<Longrightarrow> evals a A x \<Longrightarrow> R"
  shows R
proof -
  let ?args = "\<langle>a, a\<rangle>"
  let ?f = "pack_F F_EQ ?args"
  have argsN: "?args N"
    using a by simp
  have feqN: "F_EQ N"
    by simp
  have fN: "?f N"
    by (rule pack_F_N[OF feqN argsN])
  have tg: "tag_F ?f = F_EQ"
    by (rule tag_pack_F[OF feqN argsN])
  have load: "load_F ?f = ?args"
    by (rule load_pack_F[OF feqN argsN])
  have leftPair: "hyp_of ?args = a"
    by (rule cpx_proj[OF a a])
  have leftProj: "hyp_of (load_F ?f) = a"
    by (rule eqSubst[where a="?args" and b="load_F ?f" and Q="\<lambda>z. hyp_of z = a", OF eqSym[OF load] leftPair])
  show R
  proof (rule sat_fuel_formula_eqE[OF fN tg sat])
    fix x y
    assume x: "x N" and y: "y N"
        and left: "evals (hyp_of (load_F ?f)) A x"
        and right: "evals (conc_of (load_F ?f)) A y"
        and xy: "x = y"
    have evalA: "evals a A x"
      by (rule eqSubst[where a="hyp_of (load_F ?f)" and b=a and Q="\<lambda>z. evals z A x", OF leftProj left])
    show R
      by (rule H[OF x evalA])
  qed
qed

lemma fresh_T_var_lt:
  assumes k: "k N" and t: "t N" and fresh: "fresh_T k t" and tg: "tag_T t = T_VAR"
  shows "load_T t < k = 1"
proof -
  have unfolded:
    "if tag_T t = T_VAR then load_T t < k = 1
     else if tag_T t = T_ZERO then True
     else if tag_T t = T_SUC then fresh_T k (load_T t)
     else if tag_T t = T_PRED then fresh_T k (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T k (hyp_of (load_T t)) \<and>
       fresh_T k (hyp_of (conc_of (load_T t))) \<and>
       fresh_T k (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T k (hyp_of (conc_of (load_T t))) \<and>
       fresh_T k (conc_of (conc_of (load_T t)))
     else False"
    using fresh by (rule defI[OF fresh_T_def[where k=k and t=t]])
  show ?thesis
    by (rule cond_thenE[OF tg unfolded])
qed

lemma eval_fuel_subst_body_varD:
  assumes k: "k N" and b: "b N" and x: "x N" and y: "y N" and A: "A N"
      and vx: "vx N" and vy: "vy N" and evx: "evals x A vx" and evy: "evals y A vy"
      and fresh: "fresh_T 2 b" and tg: "tag_T b = T_VAR"
      and run: "eval_fuel k (subst_body b x y) A = S r"
  shows "eval_fuel k b (vx \<triangleright> vy \<triangleright> Nil) = S r"
proof (rule cases_nat_2[where x=k])
  show "k N"
    by (rule k)
next
  assume kz: "k = 0"
  have run0: "eval_fuel 0 (subst_body b x y) A = S r"
    by (rule eqSubst[where a=k and b=0 and Q="\<lambda>z. eval_fuel z (subst_body b x y) A = S r", OF kz run])
  have timeout: "eval_fuel 0 (subst_body b x y) A = 0"
    by (rule eval_fuel_zero)
  show "eval_fuel 0 b (vx \<triangleright> vy \<triangleright> Nil) = S r"
    by (rule zero_successE[OF timeout run0])
next
  fix n
  assume n: "n N" and ks: "k = S n"
  have sn: "S n N"
    by (rule natS[OF n])
  have twoN: "2 N"
    by simp
  have loadN: "load_T b N"
    by (rule load_T_N[OF b])
  have less: "load_T b < 2 = 1"
    by (rule fresh_T_var_lt[OF twoN b fresh tg])
  have A2N: "vy \<triangleright> Nil N"
    using vy by simp
  have A3N: "vx \<triangleright> vy \<triangleright> Nil N"
    using vx vy by simp
  have runS: "eval_fuel (S n) (subst_body b x y) A = S r"
    by (rule eqSubst[where a=k and b="S n" and Q="\<lambda>z. eval_fuel z (subst_body b x y) A = S r", OF ks run])
  show "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S r"
  proof (rule cases_nat_2[where x="load_T b"])
    show "load_T b N"
      by (rule loadN)
  next
    assume ld0: "load_T b = 0"
    have sub0: "subst_body b x y = x"
      apply (rule defE[OF subst_body_def[where b=b and x=x and y=y]])
      apply (rule condI1Eq[OF tg x])
      apply (rule condI1Eq[OF ld0 x])
      using x by simp
    have runX: "eval_fuel (S n) x A = S r"
      by (rule eqSubst[where a="subst_body b x y" and b=x and Q="\<lambda>z. eval_fuel (S n) z A = S r", OF sub0 runS])
    have rvx: "r = vx"
      by (rule evals_fuel_unique[OF sn x A evx runX])
    have nth0: "nth 0 (vx \<triangleright> vy \<triangleright> Nil) = vx"
      by (rule nth_zero_cons[OF vx A2N])
    have nthLoad: "nth (load_T b) (vx \<triangleright> vy \<triangleright> Nil) = vx"
      by (rule eqSubst[where a=0 and b="load_T b" and Q="\<lambda>z. nth z (vx \<triangleright> vy \<triangleright> Nil) = vx", OF eqSym[OF ld0] nth0])
    have nthLoadN: "nth (load_T b) (vx \<triangleright> vy \<triangleright> Nil) N"
      by (rule nth_N'[OF A3N loadN])
    have value0: "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S (nth (load_T b) (vx \<triangleright> vy \<triangleright> Nil))"
      by (rule eval_fuel_var[OF n tg nthLoadN])
    have value: "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S vx"
      using value0 sucCong[OF nthLoad] by (rule eq_trans)
    have vxr: "S vx = S r"
      by (rule sucCong[OF eqSym[OF rvx]])
    show "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S r"
      using value vxr by (rule eq_trans)
  next
    fix j
    assume j: "j N" and ldS: "load_T b = S j"
    show "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S r"
    proof (rule cases_nat_2[where x=j])
      show "j N"
        by (rule j)
    next
      assume j0: "j = 0"
      have ld1: "load_T b = 1"
        using ldS j0 by simp
      have ld0ne: "\<not> load_T b = 0"
        using ld1 by simp
      have sub1: "subst_body b x y = y"
        apply (rule defE[OF subst_body_def[where b=b and x=x and y=y]])
        apply (rule condI1Eq[OF tg y])
        apply (rule condI2Eq[OF ld0ne y])
        apply (rule condI1Eq[OF ld1 y])
        using y by simp
      have runY: "eval_fuel (S n) y A = S r"
        by (rule eqSubst[where a="subst_body b x y" and b=y and Q="\<lambda>z. eval_fuel (S n) z A = S r", OF sub1 runS])
      have rvy: "r = vy"
        by (rule evals_fuel_unique[OF sn y A evy runY])
      have nthTailN: "nth 0 (vy \<triangleright> Nil) N"
        by (rule nth_N'[OF A2N nat0])
      have nthSuc: "nth (S 0) (vx \<triangleright> vy \<triangleright> Nil) = nth 0 (vy \<triangleright> Nil)"
        by (rule nth_suc_cons[OF nat0 vx A2N nthTailN])
      have nthTail: "nth 0 (vy \<triangleright> Nil) = vy"
        by (rule nth_zero_cons[OF vy nil_nat])
      have nth1: "nth 1 (vx \<triangleright> vy \<triangleright> Nil) = vy"
        using nthSuc nthTail nthTailN apply simp
        done
      have nthLoad: "nth (load_T b) (vx \<triangleright> vy \<triangleright> Nil) = vy"
        by (rule eqSubst[where a=1 and b="load_T b" and Q="\<lambda>z. nth z (vx \<triangleright> vy \<triangleright> Nil) = vy", OF eqSym[OF ld1] nth1])
      have nthLoadN: "nth (load_T b) (vx \<triangleright> vy \<triangleright> Nil) N"
        by (rule nth_N'[OF A3N loadN])
      have value0: "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S (nth (load_T b) (vx \<triangleright> vy \<triangleright> Nil))"
        by (rule eval_fuel_var[OF n tg nthLoadN])
      have value: "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S vy"
        using value0 sucCong[OF nthLoad] by (rule eq_trans)
      have vyr: "S vy = S r"
        by (rule sucCong[OF eqSym[OF rvy]])
      show "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S r"
        using value vyr by (rule eq_trans)
    next
      fix z
      assume z: "z N" and jS: "j = S z"
      have ldLarge: "load_T b = S (S z)"
        using ldS jS z apply simp
        done
      have lessLarge: "S (S z) < 2 = 1"
        by (rule eqSubst[where a="load_T b" and b="S (S z)" and Q="\<lambda>w. w < 2 = 1", OF ldLarge less])
      have lessZero: "S (S z) < 2 = 0"
        unfolding less_def using z by simp
      have bot: "False"
        by (rule zero_successE[OF lessZero lessLarge])
      show "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S r"
        by (rule exF[OF bot not_false])
    qed
  qed
qed

lemma subst_body_zeroD:
  assumes b: "b N"
      and tg: "tag_T b = T_ZERO"
      and H: "Q (subst_body b x y)"
  shows "Q b"
proof -
  have R:
    "Q (if tag_T b = T_VAR then
         (if load_T b = 0 then x
          else if load_T b = 1 then y
          else b)
       else if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using H
    by (rule defI[OF subst_body_def])
  have nvar: "\<not> tag_T b = T_VAR"
    using tg by simp
  have R0:
    "Q (if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nvar R
    by (rule cond_elseQ_E[where c="tag_T b = T_VAR"
            and a="if load_T b = 0 then x
                   else if load_T b = 1 then y
                   else b"])
  show ?thesis
    using tg R0
    by (rule cond_thenQ_E[where c="tag_T b = T_ZERO" and a=b])
qed

lemma subst_body_sucD:
  assumes b: "b N"
      and tg: "tag_T b = T_SUC"
      and H: "Q (subst_body b x y)"
  shows "Q (pack_T T_SUC (subst_body (load_T b) x y))"
proof -
  have R:
    "Q (if tag_T b = T_VAR then
         (if load_T b = 0 then x
          else if load_T b = 1 then y
          else b)
       else if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using H
    by (rule defI[OF subst_body_def])
  have nvar: "\<not> tag_T b = T_VAR"
    using tg by simp
  have R0:
    "Q (if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nvar R
    by (rule cond_elseQ_E[where c="tag_T b = T_VAR"
            and a="if load_T b = 0 then x
                   else if load_T b = 1 then y
                   else b"])
  have nzero: "\<not> tag_T b = T_ZERO"
    using tg by simp
  have R1:
    "Q (if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nzero R0
    by (rule cond_elseQ_E[where c="tag_T b = T_ZERO" and a=b])
  show ?thesis
    using tg R1
    by (rule cond_thenQ_E[where c="tag_T b = T_SUC" and a="pack_T T_SUC (subst_body (load_T b) x y)"])
qed

lemma subst_body_predD:
  assumes b: "b N"
      and tg: "tag_T b = T_PRED"
      and H: "Q (subst_body b x y)"
  shows "Q (pack_T T_PRED (subst_body (load_T b) x y))"
proof -
  have R:
    "Q (if tag_T b = T_VAR then
         (if load_T b = 0 then x
          else if load_T b = 1 then y
          else b)
       else if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using H
    by (rule defI[OF subst_body_def])
  have nvar: "\<not> tag_T b = T_VAR"
    using tg by simp
  have R0:
    "Q (if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nvar R
    by (rule cond_elseQ_E[where c="tag_T b = T_VAR"
            and a="if load_T b = 0 then x
                   else if load_T b = 1 then y
                   else b"])
  have nzero: "\<not> tag_T b = T_ZERO"
    using tg by simp
  have R1:
    "Q (if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nzero R0
    by (rule cond_elseQ_E[where c="tag_T b = T_ZERO" and a=b])
  have nsuc: "\<not> tag_T b = T_SUC"
    using tg by simp
  have R2:
    "Q (if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nsuc R1
    by (rule cond_elseQ_E[where c="tag_T b = T_SUC" and a="pack_T T_SUC (subst_body (load_T b) x y)"])
  show ?thesis
    using tg R2
    by (rule cond_thenQ_E[where c="tag_T b = T_PRED" and a="pack_T T_PRED (subst_body (load_T b) x y)"])
qed

lemma subst_body_ifzD:
  assumes b: "b N"
      and tg: "tag_T b = T_IFZ"
      and H: "Q (subst_body b x y)"
  shows
    "Q (pack_T T_IFZ
      \<langle>subst_body (cpx (load_T b)) x y,
       \<langle>subst_body (cpx (cpy (load_T b))) x y,
        subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
proof -
  have R:
    "Q (if tag_T b = T_VAR then
         (if load_T b = 0 then x
          else if load_T b = 1 then y
          else b)
       else if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using H
    by (rule defI[OF subst_body_def])
  have nvar: "\<not> tag_T b = T_VAR"
    using tg by simp
  have R0:
    "Q (if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nvar R
    by (rule cond_elseQ_E[where c="tag_T b = T_VAR"
            and a="if load_T b = 0 then x
                   else if load_T b = 1 then y
                   else b"])
  have nzero: "\<not> tag_T b = T_ZERO"
    using tg by simp
  have R1:
    "Q (if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nzero R0
    by (rule cond_elseQ_E[where c="tag_T b = T_ZERO" and a=b])
  have nsuc: "\<not> tag_T b = T_SUC"
    using tg by simp
  have R2:
    "Q (if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nsuc R1
    by (rule cond_elseQ_E[where c="tag_T b = T_SUC" and a="pack_T T_SUC (subst_body (load_T b) x y)"])
  have npred: "\<not> tag_T b = T_PRED"
    using tg by simp
  have R3:
    "Q (if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using npred R2
    by (rule cond_elseQ_E[where c="tag_T b = T_PRED" and a="pack_T T_PRED (subst_body (load_T b) x y)"])
  show ?thesis
    using tg R3
    by (rule cond_thenQ_E[where c="tag_T b = T_IFZ"
            and a="pack_T T_IFZ
              \<langle>subst_body (cpx (load_T b)) x y,
               \<langle>subst_body (cpx (cpy (load_T b))) x y,
                subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>"])
qed

lemma subst_body_appD:
  assumes b: "b N"
      and tg: "tag_T b = T_APP"
      and H: "Q (subst_body b x y)"
  shows
    "Q (pack_T T_APP
      \<langle>cpx (load_T b),
       \<langle>subst_body (cpx (cpy (load_T b))) x y,
        subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
proof -
  have R:
    "Q (if tag_T b = T_VAR then
         (if load_T b = 0 then x
          else if load_T b = 1 then y
          else b)
       else if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using H
    by (rule defI[OF subst_body_def])
  have nvar: "\<not> tag_T b = T_VAR"
    using tg by simp
  have R0:
    "Q (if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nvar R
    by (rule cond_elseQ_E[where c="tag_T b = T_VAR"
            and a="if load_T b = 0 then x
                   else if load_T b = 1 then y
                   else b"])
  have nzero: "\<not> tag_T b = T_ZERO"
    using tg by simp
  have R1:
    "Q (if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nzero R0
    by (rule cond_elseQ_E[where c="tag_T b = T_ZERO" and a=b])
  have nsuc: "\<not> tag_T b = T_SUC"
    using tg by simp
  have R2:
    "Q (if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nsuc R1
    by (rule cond_elseQ_E[where c="tag_T b = T_SUC" and a="pack_T T_SUC (subst_body (load_T b) x y)"])
  have npred: "\<not> tag_T b = T_PRED"
    using tg by simp
  have R3:
    "Q (if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using npred R2
    by (rule cond_elseQ_E[where c="tag_T b = T_PRED" and a="pack_T T_PRED (subst_body (load_T b) x y)"])
  have nifz: "\<not> tag_T b = T_IFZ"
    using tg by simp
  show ?thesis
    using nifz R3
    by (rule cond_elseQ_E[where c="tag_T b = T_IFZ"
            and a="pack_T T_IFZ
              \<langle>subst_body (cpx (load_T b)) x y,
               \<langle>subst_body (cpx (cpy (load_T b))) x y,
                subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>"])
qed

lemma eval_fuel_subst_body_zeroD:
  assumes n: "n N" and b: "b N" and x: "x N" and y: "y N" and A: "A N"
      and vx: "vx N" and vy: "vy N" and tg: "tag_T b = T_ZERO"
      and run: "eval_fuel (S n) (subst_body b x y) A = S r"
  shows "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S r"
proof -
  have runOld: "eval_fuel (S n) b A = S r"
    using run by (rule subst_body_zeroD[OF b tg])
  have oldValue: "eval_fuel (S n) b A = S 0"
    by (rule eval_fuel_zero_step[OF n tg])
  have resultEq: "S 0 = S r"
    by (rule same_success[OF oldValue runOld])
  have newValue: "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S 0"
    by (rule eval_fuel_zero_step[OF n tg])
  show ?thesis
    using newValue resultEq by (rule eq_trans)
qed

lemma eval_fuel_subst_body_sucD:
  assumes n: "n N" and b: "b N" and x: "x N" and y: "y N" and A: "A N"
      and vx: "vx N" and vy: "vy N" and tg: "tag_T b = T_SUC"
      and run: "eval_fuel (S n) (subst_body b x y) A = S r"
      and IH: "\<And>q. eval_fuel n (subst_body (load_T b) x y) A = S q \<Longrightarrow>
        eval_fuel n (load_T b) (vx \<triangleright> vy \<triangleright> Nil) = S q"
  shows "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S r"
proof -
  let ?child_orig = "load_T b"
  let ?child_sub = "subst_body ?child_orig x y"
  let ?packed = "pack_T T_SUC ?child_sub"
  let ?A2 = "vx \<triangleright> vy \<triangleright> Nil"
  have childOrigN: "?child_orig N"
    by (rule load_T_N[OF b])
  have childSubN: "?child_sub N"
    by (rule subst_body_N[OF childOrigN x y])
  have A2N: "?A2 N"
    using vx vy by simp
  have packedN: "?packed N"
    by (rule pack_T_N[OF _ childSubN], simp)
  have tagPacked: "tag_T ?packed = T_SUC"
    by (rule tag_pack_T[OF _ childSubN], simp)
  have loadPacked: "load_T ?packed = ?child_sub"
    by (rule load_pack_T[OF _ childSubN], simp)
  have runPacked: "eval_fuel (S n) ?packed A = S r"
    using run by (rule subst_body_sucD[OF b tg])
  have childEvalN: "eval_fuel n ?child_sub A N"
    by (rule eval_fuel_N[OF n childSubN A])
  show ?thesis
  proof (rule cases_nat_2[where x="eval_fuel n ?child_sub A"])
    show "eval_fuel n ?child_sub A N"
      by (rule childEvalN)
  next
    assume childTimeout: "eval_fuel n ?child_sub A = 0"
    have packedChildTimeout: "eval_fuel n (load_T ?packed) A = 0"
      by (rule eqSubst[where a="?child_sub" and b="load_T ?packed"
            and Q="\<lambda>z. eval_fuel n z A = 0",
            OF eqSym[OF loadPacked] childTimeout])
    have timeout: "eval_fuel (S n) ?packed A = 0"
      by (rule eval_fuel_suc_timeout[OF n tagPacked packedChildTimeout])
    show "eval_fuel (S n) b ?A2 = S r"
      by (rule zero_successE[OF timeout runPacked])
  next
    fix q
    assume q: "q N" and childSuccess: "eval_fuel n ?child_sub A = S q"
    have packedChildSuccess: "eval_fuel n (load_T ?packed) A = S q"
      by (rule eqSubst[where a="?child_sub" and b="load_T ?packed"
            and Q="\<lambda>z. eval_fuel n z A = S q",
            OF eqSym[OF loadPacked] childSuccess])
    have packedValue: "eval_fuel (S n) ?packed A = S (S q)"
      by (rule eval_fuel_suc_value[OF n tagPacked packedChildSuccess])
    have resultEq: "S (S q) = S r"
      by (rule same_success[OF packedValue runPacked])
    have childNew: "eval_fuel n ?child_orig ?A2 = S q"
      by (rule IH[OF childSuccess])
    have newValue: "eval_fuel (S n) b ?A2 = S (S q)"
      by (rule eval_fuel_suc_value[OF n tg childNew])
    show "eval_fuel (S n) b ?A2 = S r"
      using newValue resultEq by (rule eq_trans)
  qed
qed

lemma eval_fuel_subst_body_predD:
  assumes n: "n N" and b: "b N" and x: "x N" and y: "y N" and A: "A N"
      and vx: "vx N" and vy: "vy N" and tg: "tag_T b = T_PRED"
      and run: "eval_fuel (S n) (subst_body b x y) A = S r"
      and IH: "\<And>q. eval_fuel n (subst_body (load_T b) x y) A = S q \<Longrightarrow>
        eval_fuel n (load_T b) (vx \<triangleright> vy \<triangleright> Nil) = S q"
  shows "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S r"
proof -
  let ?child_orig = "load_T b"
  let ?child_sub = "subst_body ?child_orig x y"
  let ?packed = "pack_T T_PRED ?child_sub"
  let ?A2 = "vx \<triangleright> vy \<triangleright> Nil"
  have childOrigN: "?child_orig N"
    by (rule load_T_N[OF b])
  have childSubN: "?child_sub N"
    by (rule subst_body_N[OF childOrigN x y])
  have A2N: "?A2 N"
    using vx vy by simp
  have packedN: "?packed N"
    by (rule pack_T_N[OF _ childSubN], simp)
  have tagPacked: "tag_T ?packed = T_PRED"
    by (rule tag_pack_T[OF _ childSubN], simp)
  have loadPacked: "load_T ?packed = ?child_sub"
    by (rule load_pack_T[OF _ childSubN], simp)
  have runPacked: "eval_fuel (S n) ?packed A = S r"
    using run by (rule subst_body_predD[OF b tg])
  have childEvalN: "eval_fuel n ?child_sub A N"
    by (rule eval_fuel_N[OF n childSubN A])
  show ?thesis
  proof (rule cases_nat_2[where x="eval_fuel n ?child_sub A"])
    show "eval_fuel n ?child_sub A N"
      by (rule childEvalN)
  next
    assume childTimeout: "eval_fuel n ?child_sub A = 0"
    have packedChildTimeout: "eval_fuel n (load_T ?packed) A = 0"
      by (rule eqSubst[where a="?child_sub" and b="load_T ?packed"
            and Q="\<lambda>z. eval_fuel n z A = 0",
            OF eqSym[OF loadPacked] childTimeout])
    have timeout: "eval_fuel (S n) ?packed A = 0"
      by (rule eval_fuel_pred_timeout[OF n tagPacked packedChildTimeout])
    show "eval_fuel (S n) b ?A2 = S r"
      by (rule zero_successE[OF timeout runPacked])
  next
    fix q
    assume q: "q N" and childSuccess: "eval_fuel n ?child_sub A = S q"
    have packedChildSuccess: "eval_fuel n (load_T ?packed) A = S q"
      by (rule eqSubst[where a="?child_sub" and b="load_T ?packed"
            and Q="\<lambda>z. eval_fuel n z A = S q",
            OF eqSym[OF loadPacked] childSuccess])
    have packedValue: "eval_fuel (S n) ?packed A = S (P q)"
      by (rule eval_fuel_pred_value[OF n tagPacked packedChildSuccess])
    have resultEq: "S (P q) = S r"
      by (rule same_success[OF packedValue runPacked])
    have childNew: "eval_fuel n ?child_orig ?A2 = S q"
      by (rule IH[OF childSuccess])
    have newValue: "eval_fuel (S n) b ?A2 = S (P q)"
      by (rule eval_fuel_pred_value[OF n tg childNew])
    show "eval_fuel (S n) b ?A2 = S r"
      using newValue resultEq by (rule eq_trans)
  qed
qed

lemma eval_fuel_subst_body_ifzD:
  assumes n: "n N" and b: "b N" and x: "x N" and y: "y N" and A: "A N"
      and vx: "vx N" and vy: "vy N" and tg: "tag_T b = T_IFZ"
      and run: "eval_fuel (S n) (subst_body b x y) A = S r"
      and IHcond: "\<And>q. eval_fuel n (subst_body (hyp_of (load_T b)) x y) A = S q \<Longrightarrow>
        eval_fuel n (hyp_of (load_T b)) (vx \<triangleright> vy \<triangleright> Nil) = S q"
      and IHthen: "\<And>q. eval_fuel n (subst_body (hyp_of (conc_of (load_T b))) x y) A = S q \<Longrightarrow>
        eval_fuel n (hyp_of (conc_of (load_T b))) (vx \<triangleright> vy \<triangleright> Nil) = S q"
      and IHelse: "\<And>q. eval_fuel n (subst_body (conc_of (conc_of (load_T b))) x y) A = S q \<Longrightarrow>
        eval_fuel n (conc_of (conc_of (load_T b))) (vx \<triangleright> vy \<triangleright> Nil) = S q"
  shows "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S r"
proof -
  let ?cond_orig = "hyp_of (load_T b)"
  let ?then_orig = "hyp_of (conc_of (load_T b))"
  let ?else_orig = "conc_of (conc_of (load_T b))"
  let ?cond_sub = "subst_body ?cond_orig x y"
  let ?then_sub = "subst_body ?then_orig x y"
  let ?else_sub = "subst_body ?else_orig x y"
  let ?A2 = "vx \<triangleright> vy \<triangleright> Nil"
  let ?args = "\<langle>?then_sub, ?else_sub\<rangle>"
  let ?payload = "\<langle>?cond_sub, ?args\<rangle>"
  let ?packed = "pack_T T_IFZ ?payload"
  have loadN: "load_T b N"
    by (rule load_T_N[OF b])
  have condOrigN: "?cond_orig N"
    by (rule cpx_terminates[OF loadN])
  have tailN: "conc_of (load_T b) N"
    by (rule cpy_terminates[OF loadN])
  have thenOrigN: "?then_orig N"
    by (rule cpx_terminates[OF tailN])
  have elseOrigN: "?else_orig N"
    by (rule cpy_terminates[OF tailN])
  have condSubN: "?cond_sub N"
    by (rule subst_body_N[OF condOrigN x y])
  have thenSubN: "?then_sub N"
    by (rule subst_body_N[OF thenOrigN x y])
  have elseSubN: "?else_sub N"
    by (rule subst_body_N[OF elseOrigN x y])
  have argsN: "?args N"
    using thenSubN elseSubN by simp
  have payloadN: "?payload N"
    using condSubN argsN by simp
  have tagPacked: "tag_T ?packed = T_IFZ"
    by (rule tag_pack_T[OF _ payloadN], simp)
  have loadPacked: "load_T ?packed = ?payload"
    by (rule load_pack_T[OF _ payloadN], simp)
  have payloadCond: "hyp_of ?payload = ?cond_sub"
    by (rule cpx_proj[OF condSubN argsN])
  have payloadArgs: "conc_of ?payload = ?args"
    by (rule cpy_proj[OF condSubN argsN])
  have argsThen: "hyp_of ?args = ?then_sub"
    by (rule cpx_proj[OF thenSubN elseSubN])
  have argsElse: "conc_of ?args = ?else_sub"
    by (rule cpy_proj[OF thenSubN elseSubN])
  have selectCond: "hyp_of (load_T ?packed) = ?cond_sub"
    by (rule eqSubst[where a="?payload" and b="load_T ?packed" and Q="\<lambda>z. hyp_of z = ?cond_sub", OF eqSym[OF loadPacked] payloadCond])
  have selectArgs: "conc_of (load_T ?packed) = ?args"
    by (rule eqSubst[where a="?payload" and b="load_T ?packed" and Q="\<lambda>z. conc_of z = ?args", OF eqSym[OF loadPacked] payloadArgs])
  have selectThen: "hyp_of (conc_of (load_T ?packed)) = ?then_sub"
    by (rule eqSubst[where a="?args" and b="conc_of (load_T ?packed)" and Q="\<lambda>z. hyp_of z = ?then_sub", OF eqSym[OF selectArgs] argsThen])
  have selectElse: "conc_of (conc_of (load_T ?packed)) = ?else_sub"
    by (rule eqSubst[where a="?args" and b="conc_of (load_T ?packed)" and Q="\<lambda>z. conc_of z = ?else_sub", OF eqSym[OF selectArgs] argsElse])
  have runPacked: "eval_fuel (S n) ?packed A = S r"
    using run by (rule subst_body_ifzD[OF b tg])
  have condEvalN: "eval_fuel n ?cond_sub A N"
    by (rule eval_fuel_N[OF n condSubN A])
  show ?thesis
  proof (rule cases_nat_2[where x="eval_fuel n ?cond_sub A"])
    show "eval_fuel n ?cond_sub A N"
      by (rule condEvalN)
  next
    assume condTimeout: "eval_fuel n ?cond_sub A = 0"
    have packedCondTimeout: "eval_fuel n (hyp_of (load_T ?packed)) A = 0"
      by (rule eqSubst[where a="?cond_sub" and b="hyp_of (load_T ?packed)" and Q="\<lambda>z. eval_fuel n z A = 0", OF eqSym[OF selectCond] condTimeout])
    have timeout: "eval_fuel (S n) ?packed A = 0"
      by (rule eval_fuel_ifz_cond_timeout[OF n tagPacked packedCondTimeout])
    show "eval_fuel (S n) b ?A2 = S r"
      by (rule zero_successE[OF timeout runPacked])
  next
    fix c
    assume c: "c N" and condSuccess: "eval_fuel n ?cond_sub A = S c"
    show "eval_fuel (S n) b ?A2 = S r"
    proof (rule cases_nat_2[where x=c])
      show "c N"
        by (rule c)
    next
      assume cz: "c = 0"
      have condZero: "eval_fuel n ?cond_sub A = S 0"
        using condSuccess sucCong[OF cz] by (rule eq_trans)
      have packedCondZero: "eval_fuel n (hyp_of (load_T ?packed)) A = S 0"
        by (rule eqSubst[where a="?cond_sub" and b="hyp_of (load_T ?packed)" and Q="\<lambda>z. eval_fuel n z A = S 0", OF eqSym[OF selectCond] condZero])
      have thenEvalN: "eval_fuel n ?then_sub A N"
        by (rule eval_fuel_N[OF n thenSubN A])
      show "eval_fuel (S n) b ?A2 = S r"
      proof (rule cases_nat_2[where x="eval_fuel n ?then_sub A"])
        show "eval_fuel n ?then_sub A N"
          by (rule thenEvalN)
      next
        assume thenTimeout: "eval_fuel n ?then_sub A = 0"
        have packedThenTimeout: "eval_fuel n (hyp_of (conc_of (load_T ?packed))) A = 0"
          by (rule eqSubst[where a="?then_sub" and b="hyp_of (conc_of (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = 0", OF eqSym[OF selectThen] thenTimeout])
        have packedThenN: "eval_fuel n (hyp_of (conc_of (load_T ?packed))) A N"
          by (rule eqSubst[where a="?then_sub" and b="hyp_of (conc_of (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A N", OF eqSym[OF selectThen] thenEvalN])
        have step: "eval_fuel (S n) ?packed A = eval_fuel n (hyp_of (conc_of (load_T ?packed))) A"
          by (rule eval_fuel_ifz_zero[OF n tagPacked packedCondZero packedThenN])
        have timeout: "eval_fuel (S n) ?packed A = 0"
          using step packedThenTimeout by (rule eq_trans)
        show "eval_fuel (S n) b ?A2 = S r"
          by (rule zero_successE[OF timeout runPacked])
      next
        fix q
        assume q: "q N" and thenSuccess: "eval_fuel n ?then_sub A = S q"
        have packedThenSuccess: "eval_fuel n (hyp_of (conc_of (load_T ?packed))) A = S q"
          by (rule eqSubst[where a="?then_sub" and b="hyp_of (conc_of (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = S q", OF eqSym[OF selectThen] thenSuccess])
        have packedValue: "eval_fuel (S n) ?packed A = S q"
          by (rule eval_fuel_ifz_zero_value[OF n tagPacked packedCondZero packedThenSuccess])
        have resultEq: "S q = S r"
          by (rule same_success[OF packedValue runPacked])
        have condNew: "eval_fuel n ?cond_orig ?A2 = S 0"
          by (rule IHcond[OF condZero])
        have thenNew: "eval_fuel n ?then_orig ?A2 = S q"
          by (rule IHthen[OF thenSuccess])
        have newValue: "eval_fuel (S n) b ?A2 = S q"
          by (rule eval_fuel_ifz_zero_value[OF n tg condNew thenNew])
        show "eval_fuel (S n) b ?A2 = S r"
          using newValue resultEq by (rule eq_trans)
      qed
    next
      fix d
      assume d: "d N" and cnz: "c = S d"
      have condNonzero: "eval_fuel n ?cond_sub A = S (S d)"
        using condSuccess sucCong[OF cnz] by (rule eq_trans)
      have packedCondNonzero: "eval_fuel n (hyp_of (load_T ?packed)) A = S (S d)"
        by (rule eqSubst[where a="?cond_sub" and b="hyp_of (load_T ?packed)" and Q="\<lambda>z. eval_fuel n z A = S (S d)", OF eqSym[OF selectCond] condNonzero])
      have elseEvalN: "eval_fuel n ?else_sub A N"
        by (rule eval_fuel_N[OF n elseSubN A])
      show "eval_fuel (S n) b ?A2 = S r"
      proof (rule cases_nat_2[where x="eval_fuel n ?else_sub A"])
        show "eval_fuel n ?else_sub A N"
          by (rule elseEvalN)
      next
        assume elseTimeout: "eval_fuel n ?else_sub A = 0"
        have packedElseTimeout: "eval_fuel n (conc_of (conc_of (load_T ?packed))) A = 0"
          by (rule eqSubst[where a="?else_sub" and b="conc_of (conc_of (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = 0", OF eqSym[OF selectElse] elseTimeout])
        have packedElseN: "eval_fuel n (conc_of (conc_of (load_T ?packed))) A N"
          by (rule eqSubst[where a="?else_sub" and b="conc_of (conc_of (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A N", OF eqSym[OF selectElse] elseEvalN])
        have step: "eval_fuel (S n) ?packed A = eval_fuel n (conc_of (conc_of (load_T ?packed))) A"
          by (rule eval_fuel_ifz_nonzero[OF n tagPacked packedCondNonzero packedElseN])
        have timeout: "eval_fuel (S n) ?packed A = 0"
          using step packedElseTimeout by (rule eq_trans)
        show "eval_fuel (S n) b ?A2 = S r"
          by (rule zero_successE[OF timeout runPacked])
      next
        fix q
        assume q: "q N" and elseSuccess: "eval_fuel n ?else_sub A = S q"
        have packedElseSuccess: "eval_fuel n (conc_of (conc_of (load_T ?packed))) A = S q"
          by (rule eqSubst[where a="?else_sub" and b="conc_of (conc_of (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = S q", OF eqSym[OF selectElse] elseSuccess])
        have packedValue: "eval_fuel (S n) ?packed A = S q"
          by (rule eval_fuel_ifz_nonzero_value[OF n tagPacked packedCondNonzero packedElseSuccess])
        have resultEq: "S q = S r"
          by (rule same_success[OF packedValue runPacked])
        have condNew: "eval_fuel n ?cond_orig ?A2 = S (S d)"
          by (rule IHcond[OF condNonzero])
        have elseNew: "eval_fuel n ?else_orig ?A2 = S q"
          by (rule IHelse[OF elseSuccess])
        have newValue: "eval_fuel (S n) b ?A2 = S q"
          by (rule eval_fuel_ifz_nonzero_value[OF n tg condNew elseNew])
        show "eval_fuel (S n) b ?A2 = S r"
          using newValue resultEq by (rule eq_trans)
      qed
    qed
  qed
qed

lemma eval_fuel_subst_body_appD:
  assumes n: "n N" and b: "b N" and x: "x N" and y: "y N" and A: "A N"
      and vx: "vx N" and vy: "vy N" and tg: "tag_T b = T_APP"
      and run: "eval_fuel (S n) (subst_body b x y) A = S r"
      and IHarg1: "\<And>q. eval_fuel n (subst_body (hyp_of (conc_of (load_T b))) x y) A = S q \<Longrightarrow>
        eval_fuel n (hyp_of (conc_of (load_T b))) (vx \<triangleright> vy \<triangleright> Nil) = S q"
      and IHarg2: "\<And>q. eval_fuel n (subst_body (conc_of (conc_of (load_T b))) x y) A = S q \<Longrightarrow>
        eval_fuel n (conc_of (conc_of (load_T b))) (vx \<triangleright> vy \<triangleright> Nil) = S q"
  shows "eval_fuel (S n) b (vx \<triangleright> vy \<triangleright> Nil) = S r"
proof -
  let ?dfn = "hyp_of (load_T b)"
  let ?arg1_orig = "hyp_of (conc_of (load_T b))"
  let ?arg2_orig = "conc_of (conc_of (load_T b))"
  let ?arg1_sub = "subst_body ?arg1_orig x y"
  let ?arg2_sub = "subst_body ?arg2_orig x y"
  let ?A2 = "vx \<triangleright> vy \<triangleright> Nil"
  let ?args = "\<langle>?arg1_sub, ?arg2_sub\<rangle>"
  let ?payload = "\<langle>?dfn, ?args\<rangle>"
  let ?packed = "pack_T T_APP ?payload"
  have nvar: "\<not> tag_T b = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T b = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T b = T_SUC"
    using tg by simp
  have npred: "\<not> tag_T b = T_PRED"
    using tg by simp
  have nifz: "\<not> tag_T b = T_IFZ"
    using tg by simp
  have loadN: "load_T b N"
    by (rule load_T_N[OF b])
  have dfnN: "?dfn N"
    by (rule cpx_terminates[OF loadN])
  have tailN: "conc_of (load_T b) N"
    by (rule cpy_terminates[OF loadN])
  have arg1OrigN: "?arg1_orig N"
    by (rule cpx_terminates[OF tailN])
  have arg2OrigN: "?arg2_orig N"
    by (rule cpy_terminates[OF tailN])
  have arg1SubN: "?arg1_sub N"
    by (rule subst_body_N[OF arg1OrigN x y])
  have arg2SubN: "?arg2_sub N"
    by (rule subst_body_N[OF arg2OrigN x y])
  have argsN: "?args N"
    using arg1SubN arg2SubN by simp
  have payloadN: "?payload N"
    using dfnN argsN by simp
  have tagPacked: "tag_T ?packed = T_APP"
    by (rule tag_pack_T[OF _ payloadN], simp)
  have packedNvar: "\<not> tag_T ?packed = T_VAR"
    using tagPacked by simp
  have packedNzero: "\<not> tag_T ?packed = T_ZERO"
    using tagPacked by simp
  have packedNsuc: "\<not> tag_T ?packed = T_SUC"
    using tagPacked by simp
  have packedNpred: "\<not> tag_T ?packed = T_PRED"
    using tagPacked by simp
  have packedNifz: "\<not> tag_T ?packed = T_IFZ"
    using tagPacked by simp
  have loadPacked: "load_T ?packed = ?payload"
    by (rule load_pack_T[OF _ payloadN], simp)
  have payloadDfn: "hyp_of ?payload = ?dfn"
    by (rule cpx_proj[OF dfnN argsN])
  have payloadArgs: "conc_of ?payload = ?args"
    by (rule cpy_proj[OF dfnN argsN])
  have argsArg1: "hyp_of ?args = ?arg1_sub"
    by (rule cpx_proj[OF arg1SubN arg2SubN])
  have argsArg2: "conc_of ?args = ?arg2_sub"
    by (rule cpy_proj[OF arg1SubN arg2SubN])
  have selectDfn: "hyp_of (load_T ?packed) = ?dfn"
    by (rule eqSubst[where a="?payload" and b="load_T ?packed" and Q="\<lambda>z. hyp_of z = ?dfn", OF eqSym[OF loadPacked] payloadDfn])
  have selectArgs: "conc_of (load_T ?packed) = ?args"
    by (rule eqSubst[where a="?payload" and b="load_T ?packed" and Q="\<lambda>z. conc_of z = ?args", OF eqSym[OF loadPacked] payloadArgs])
  have selectArg1: "hyp_of (conc_of (load_T ?packed)) = ?arg1_sub"
    by (rule eqSubst[where a="?args" and b="conc_of (load_T ?packed)" and Q="\<lambda>z. hyp_of z = ?arg1_sub", OF eqSym[OF selectArgs] argsArg1])
  have selectArg2: "conc_of (conc_of (load_T ?packed)) = ?arg2_sub"
    by (rule eqSubst[where a="?args" and b="conc_of (load_T ?packed)" and Q="\<lambda>z. conc_of z = ?arg2_sub", OF eqSym[OF selectArgs] argsArg2])
  have runPacked: "eval_fuel (S n) ?packed A = S r"
    using run by (rule subst_body_appD[OF b tg])
  have arg1EvalN: "eval_fuel n ?arg1_sub A N"
    by (rule eval_fuel_N[OF n arg1SubN A])
  show ?thesis
  proof (rule cases_nat_2[where x="eval_fuel n ?arg1_sub A"])
    show "eval_fuel n ?arg1_sub A N"
      by (rule arg1EvalN)
  next
    assume arg1Timeout: "eval_fuel n ?arg1_sub A = 0"
    have packedArg1Timeout: "eval_fuel n (hyp_of (conc_of (load_T ?packed))) A = 0"
      by (rule eqSubst[where a="?arg1_sub" and b="hyp_of (conc_of (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = 0", OF eqSym[OF selectArg1] arg1Timeout])
    have timeout: "eval_fuel (S n) ?packed A = 0"
      by (rule eval_fuel_app_arg1_timeout[OF n packedNvar packedNzero packedNsuc packedNpred packedNifz packedArg1Timeout])
    show "eval_fuel (S n) b ?A2 = S r"
      by (rule zero_successE[OF timeout runPacked])
  next
    fix p
    assume p: "p N" and arg1Success: "eval_fuel n ?arg1_sub A = S p"
    have packedArg1Success: "eval_fuel n (hyp_of (conc_of (load_T ?packed))) A = S p"
      by (rule eqSubst[where a="?arg1_sub" and b="hyp_of (conc_of (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = S p", OF eqSym[OF selectArg1] arg1Success])
    have arg2EvalN: "eval_fuel n ?arg2_sub A N"
      by (rule eval_fuel_N[OF n arg2SubN A])
    show "eval_fuel (S n) b ?A2 = S r"
    proof (rule cases_nat_2[where x="eval_fuel n ?arg2_sub A"])
      show "eval_fuel n ?arg2_sub A N"
        by (rule arg2EvalN)
    next
      assume arg2Timeout: "eval_fuel n ?arg2_sub A = 0"
      have packedArg2Timeout: "eval_fuel n (conc_of (conc_of (load_T ?packed))) A = 0"
        by (rule eqSubst[where a="?arg2_sub" and b="conc_of (conc_of (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = 0", OF eqSym[OF selectArg2] arg2Timeout])
      have timeout: "eval_fuel (S n) ?packed A = 0"
        by (rule eval_fuel_app_arg2_timeout[OF n packedNvar packedNzero packedNsuc packedNpred packedNifz packedArg1Success packedArg2Timeout])
      show "eval_fuel (S n) b ?A2 = S r"
        by (rule zero_successE[OF timeout runPacked])
    next
      fix q
      assume q: "q N" and arg2Success: "eval_fuel n ?arg2_sub A = S q"
      have packedArg2Success: "eval_fuel n (conc_of (conc_of (load_T ?packed))) A = S q"
        by (rule eqSubst[where a="?arg2_sub" and b="conc_of (conc_of (load_T ?packed))" and Q="\<lambda>z. eval_fuel n z A = S q", OF eqSym[OF selectArg2] arg2Success])
      have appAsnN: "p \<triangleright> q \<triangleright> Nil N"
        using p q by simp
      have bodyTermN: "nth ?dfn dfns N"
        by (rule nth_N'[OF dfns_N dfnN])
      have bodyEvalN: "eval_fuel n (nth ?dfn dfns) (p \<triangleright> q \<triangleright> Nil) N"
        by (rule eval_fuel_N[OF n bodyTermN appAsnN])
      show "eval_fuel (S n) b ?A2 = S r"
      proof (rule cases_nat_2[where x="eval_fuel n (nth ?dfn dfns) (p \<triangleright> q \<triangleright> Nil)"])
        show "eval_fuel n (nth ?dfn dfns) (p \<triangleright> q \<triangleright> Nil) N"
          by (rule bodyEvalN)
      next
        assume bodyTimeout: "eval_fuel n (nth ?dfn dfns) (p \<triangleright> q \<triangleright> Nil) = 0"
        have packedBodyTimeout: "eval_fuel n (nth (hyp_of (load_T ?packed)) dfns) (p \<triangleright> q \<triangleright> Nil) = 0"
          by (rule eqSubst[where a="?dfn" and b="hyp_of (load_T ?packed)" and Q="\<lambda>z. eval_fuel n (nth z dfns) (p \<triangleright> q \<triangleright> Nil) = 0", OF eqSym[OF selectDfn] bodyTimeout])
        have timeout: "eval_fuel (S n) ?packed A = 0"
          by (rule eval_fuel_app_body_timeout[OF n packedNvar packedNzero packedNsuc packedNpred packedNifz packedArg1Success packedArg2Success packedBodyTimeout])
        show "eval_fuel (S n) b ?A2 = S r"
          by (rule zero_successE[OF timeout runPacked])
      next
        fix z
        assume z: "z N" and bodySuccess: "eval_fuel n (nth ?dfn dfns) (p \<triangleright> q \<triangleright> Nil) = S z"
        have packedBodySuccess: "eval_fuel n (nth (hyp_of (load_T ?packed)) dfns) (p \<triangleright> q \<triangleright> Nil) = S z"
          by (rule eqSubst[where a="?dfn" and b="hyp_of (load_T ?packed)" and Q="\<lambda>w. eval_fuel n (nth w dfns) (p \<triangleright> q \<triangleright> Nil) = S z", OF eqSym[OF selectDfn] bodySuccess])
        have packedValue: "eval_fuel (S n) ?packed A = S z"
          by (rule eval_fuel_app_value[OF n packedNvar packedNzero packedNsuc packedNpred packedNifz packedArg1Success packedArg2Success packedBodySuccess])
        have resultEq: "S z = S r"
          by (rule same_success[OF packedValue runPacked])
        have arg1New: "eval_fuel n ?arg1_orig ?A2 = S p"
          by (rule IHarg1[OF arg1Success])
        have arg2New: "eval_fuel n ?arg2_orig ?A2 = S q"
          by (rule IHarg2[OF arg2Success])
        have newValue: "eval_fuel (S n) b ?A2 = S z"
          by (rule eval_fuel_app_value[OF n nvar nzero nsuc npred nifz arg1New arg2New bodySuccess])
        show "eval_fuel (S n) b ?A2 = S r"
          using newValue resultEq by (rule eq_trans)
      qed
    qed
  qed
qed

lemma fresh_T_app_tag:
  assumes i: "i N" and t: "t N" and fresh: "fresh_T i t"
      and nvar: "\<not> tag_T t = T_VAR" and nzero: "\<not> tag_T t = T_ZERO"
      and nsuc: "\<not> tag_T t = T_SUC" and npred: "\<not> tag_T t = T_PRED"
      and nifz: "\<not> tag_T t = T_IFZ"
  shows "tag_T t = T_APP"
proof -
  have unfolded:
    "if tag_T t = T_VAR then load_T t < i = 1
     else if tag_T t = T_ZERO then True
     else if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    using fresh by (rule defI[OF fresh_T_def[where k=i and t=t]])
  have step1:
    "if tag_T t = T_ZERO then True
     else if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nvar unfolded])
  have step2:
    "if tag_T t = T_SUC then fresh_T i (load_T t)
     else if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nzero step1])
  have step3:
    "if tag_T t = T_PRED then fresh_T i (load_T t)
     else if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nsuc step2])
  have step4:
    "if tag_T t = T_IFZ then
       fresh_T i (hyp_of (load_T t)) \<and>
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF npred step3])
  have step5:
    "if tag_T t = T_APP then
       fresh_T i (hyp_of (conc_of (load_T t))) \<and>
       fresh_T i (conc_of (conc_of (load_T t)))
     else False"
    by (rule notcond_thenE[OF nifz step4])
  have tagN: "tag_T t N"
    by (rule tag_T_N[OF t])
  have appB: "(tag_T t = T_APP) B"
    by (rule eqBool[OF tagN], simp)
  show ?thesis
  proof (rule cases_bool[where q="tag_T t = T_APP"])
    show "(tag_T t = T_APP) B"
      by (rule appB)
  next
    assume tg: "tag_T t = T_APP"
    show "tag_T t = T_APP"
      by (rule tg)
  next
    assume ntg: "\<not> tag_T t = T_APP"
    have bot: "False"
      by (rule notcond_thenE[OF ntg step5])
    show "tag_T t = T_APP"
      by (rule exF[OF bot], simp)
  qed
qed

lemma eval_fuel_subst_bodyD:
  assumes k: "k N" and b: "b N" and x: "x N" and y: "y N" and A: "A N"
      and vx: "vx N" and vy: "vy N" and evx: "evals x A vx" and evy: "evals y A vy"
      and fresh: "fresh_T 2 b" and run: "eval_fuel k (subst_body b x y) A = S r"
  shows "eval_fuel k b (vx \<triangleright> vy \<triangleright> Nil) = S r"
proof -
  let ?A2 = "vx \<triangleright> vy \<triangleright> Nil"
  have twoN: "2 N"
    by simp
  have A2N: "?A2 N"
    using vx vy by simp
  have main:
    "\<forall>u. \<forall>q. fresh_T 2 u \<longrightarrow>
      (eval_fuel k (subst_body u x y) A = S q) \<longrightarrow>
      eval_fuel k u ?A2 = S q"
  proof (rule ind[OF k])
    show
      "\<forall>u. \<forall>q. fresh_T 2 u \<longrightarrow>
        (eval_fuel 0 (subst_body u x y) A = S q) \<longrightarrow>
        eval_fuel 0 u ?A2 = S q"
    proof (rule forallI)
      fix u
      assume u: "u N"
      show
        "\<forall>q. fresh_T 2 u \<longrightarrow>
          (eval_fuel 0 (subst_body u x y) A = S q) \<longrightarrow>
          eval_fuel 0 u ?A2 = S q"
      proof (rule forallI)
        fix q
        assume q: "q N"
        show
          "fresh_T 2 u \<longrightarrow>
            (eval_fuel 0 (subst_body u x y) A = S q) \<longrightarrow>
            eval_fuel 0 u ?A2 = S q"
        proof (rule implI)
          show "fresh_T 2 u B"
            by (rule fresh_T_bool[OF twoN u])
        next
          assume freshU: "fresh_T 2 u"
          show
            "(eval_fuel 0 (subst_body u x y) A = S q) \<longrightarrow>
              eval_fuel 0 u ?A2 = S q"
          proof (rule implI)
            have subN: "subst_body u x y N"
              by (rule subst_body_N[OF u x y])
            have evalN: "eval_fuel 0 (subst_body u x y) A N"
              by (rule eval_fuel_N[OF nat0 subN A])
            have sqN: "S q N"
              by (rule natS[OF q])
            show "(eval_fuel 0 (subst_body u x y) A = S q) B"
              by (rule eqBool[OF evalN sqN])
          next
            assume success: "eval_fuel 0 (subst_body u x y) A = S q"
            have timeout: "eval_fuel 0 (subst_body u x y) A = 0"
              by (rule eval_fuel_zero)
            show "eval_fuel 0 u ?A2 = S q"
              by (rule zero_successE[OF timeout success])
          qed
        qed
      qed
    qed
  next
    fix n
    assume n: "n N"
    assume IH:
      "\<forall>u. \<forall>q. fresh_T 2 u \<longrightarrow>
        (eval_fuel n (subst_body u x y) A = S q) \<longrightarrow>
        eval_fuel n u ?A2 = S q"
    show
      "\<forall>u. \<forall>q. fresh_T 2 u \<longrightarrow>
        (eval_fuel (S n) (subst_body u x y) A = S q) \<longrightarrow>
        eval_fuel (S n) u ?A2 = S q"
    proof (rule forallI)
      fix u
      assume u: "u N"
      show
        "\<forall>q. fresh_T 2 u \<longrightarrow>
          (eval_fuel (S n) (subst_body u x y) A = S q) \<longrightarrow>
          eval_fuel (S n) u ?A2 = S q"
      proof (rule forallI)
        fix q
        assume q: "q N"
        show
          "fresh_T 2 u \<longrightarrow>
            (eval_fuel (S n) (subst_body u x y) A = S q) \<longrightarrow>
            eval_fuel (S n) u ?A2 = S q"
        proof (rule implI)
          show "fresh_T 2 u B"
            by (rule fresh_T_bool[OF twoN u])
        next
          assume freshU: "fresh_T 2 u"
          show
            "(eval_fuel (S n) (subst_body u x y) A = S q) \<longrightarrow>
              eval_fuel (S n) u ?A2 = S q"
          proof (rule implI)
            have sn: "S n N"
              by (rule natS[OF n])
            have subN: "subst_body u x y N"
              by (rule subst_body_N[OF u x y])
            have evalN: "eval_fuel (S n) (subst_body u x y) A N"
              by (rule eval_fuel_N[OF sn subN A])
            have sqN: "S q N"
              by (rule natS[OF q])
            show "(eval_fuel (S n) (subst_body u x y) A = S q) B"
              by (rule eqBool[OF evalN sqN])
          next
            assume result: "eval_fuel (S n) (subst_body u x y) A = S q"
            have sn: "S n N"
              by (rule natS[OF n])
            have IHmeta:
              "\<And>w z. w N \<Longrightarrow> fresh_T 2 w \<Longrightarrow>
                eval_fuel n (subst_body w x y) A = S z \<Longrightarrow>
                eval_fuel n w ?A2 = S z"
            proof -
              fix w z
              assume w: "w N" and freshW: "fresh_T 2 w"
                  and success: "eval_fuel n (subst_body w x y) A = S z"
              have subW: "subst_body w x y N"
                by (rule subst_body_N[OF w x y])
              have z: "z N"
                by (rule eval_fuel_result_N[OF n subW A success])
              have IHw:
                "\<forall>z. fresh_T 2 w \<longrightarrow>
                  (eval_fuel n (subst_body w x y) A = S z) \<longrightarrow>
                  eval_fuel n w ?A2 = S z"
                by (rule forallE[where a=w, OF IH w])
              have IHwz:
                "fresh_T 2 w \<longrightarrow>
                  (eval_fuel n (subst_body w x y) A = S z) \<longrightarrow>
                  eval_fuel n w ?A2 = S z"
                by (rule forallE[where a=z, OF IHw z])
              have successImp:
                "(eval_fuel n (subst_body w x y) A = S z) \<longrightarrow>
                  eval_fuel n w ?A2 = S z"
                using IHwz freshW by (rule implE)
              show "eval_fuel n w ?A2 = S z"
                using successImp success by (rule implE)
            qed
            have loadN: "load_T u N"
              by (rule load_T_N[OF u])
            have condN: "hyp_of (load_T u) N"
              by (rule cpx_terminates[OF loadN])
            have tailN: "conc_of (load_T u) N"
              by (rule cpy_terminates[OF loadN])
            have leftN: "hyp_of (conc_of (load_T u)) N"
              by (rule cpx_terminates[OF tailN])
            have rightN: "conc_of (conc_of (load_T u)) N"
              by (rule cpy_terminates[OF tailN])
            have tagN: "tag_T u N"
              by (rule tag_T_N[OF u])
            have varB: "(tag_T u = T_VAR) B"
              by (rule eqBool[OF tagN], simp)
            have zeroB: "(tag_T u = T_ZERO) B"
              by (rule eqBool[OF tagN], simp)
            have sucB: "(tag_T u = T_SUC) B"
              by (rule eqBool[OF tagN], simp)
            have predB: "(tag_T u = T_PRED) B"
              by (rule eqBool[OF tagN], simp)
            have ifzB: "(tag_T u = T_IFZ) B"
              by (rule eqBool[OF tagN], simp)
            show "eval_fuel (S n) u ?A2 = S q"
            proof (rule cases_bool[where q="tag_T u = T_VAR"])
              show "(tag_T u = T_VAR) B"
                by (rule varB)
            next
              assume tg: "tag_T u = T_VAR"
              show "eval_fuel (S n) u ?A2 = S q"
                by (rule eval_fuel_subst_body_varD[OF sn u x y A vx vy evx evy freshU tg result])
            next
              assume nvar: "\<not> tag_T u = T_VAR"
              show "eval_fuel (S n) u ?A2 = S q"
              proof (rule cases_bool[where q="tag_T u = T_ZERO"])
                show "(tag_T u = T_ZERO) B"
                  by (rule zeroB)
              next
                assume tg: "tag_T u = T_ZERO"
                show "eval_fuel (S n) u ?A2 = S q"
                  by (rule eval_fuel_subst_body_zeroD[OF n u x y A vx vy tg result])
              next
                assume nzero: "\<not> tag_T u = T_ZERO"
                show "eval_fuel (S n) u ?A2 = S q"
                proof (rule cases_bool[where q="tag_T u = T_SUC"])
                  show "(tag_T u = T_SUC) B"
                    by (rule sucB)
                next
                  assume tg: "tag_T u = T_SUC"
                  have freshChild: "fresh_T 2 (load_T u)"
                    by (rule fresh_T_sucD[OF twoN u freshU tg])
                  have IHchild:
                    "\<And>z. eval_fuel n (subst_body (load_T u) x y) A = S z \<Longrightarrow>
                      eval_fuel n (load_T u) ?A2 = S z"
                  proof -
                    fix z
                    assume success: "eval_fuel n (subst_body (load_T u) x y) A = S z"
                    show "eval_fuel n (load_T u) ?A2 = S z"
                      by (rule IHmeta[OF loadN freshChild success])
                  qed
                  show "eval_fuel (S n) u ?A2 = S q"
                    by (rule eval_fuel_subst_body_sucD[OF n u x y A vx vy tg result IHchild])
                next
                  assume nsuc: "\<not> tag_T u = T_SUC"
                  show "eval_fuel (S n) u ?A2 = S q"
                  proof (rule cases_bool[where q="tag_T u = T_PRED"])
                    show "(tag_T u = T_PRED) B"
                      by (rule predB)
                  next
                    assume tg: "tag_T u = T_PRED"
                    have freshChild: "fresh_T 2 (load_T u)"
                      by (rule fresh_T_predD[OF twoN u freshU tg])
                    have IHchild:
                      "\<And>z. eval_fuel n (subst_body (load_T u) x y) A = S z \<Longrightarrow>
                        eval_fuel n (load_T u) ?A2 = S z"
                    proof -
                      fix z
                      assume success: "eval_fuel n (subst_body (load_T u) x y) A = S z"
                      show "eval_fuel n (load_T u) ?A2 = S z"
                        by (rule IHmeta[OF loadN freshChild success])
                    qed
                    show "eval_fuel (S n) u ?A2 = S q"
                      by (rule eval_fuel_subst_body_predD[OF n u x y A vx vy tg result IHchild])
                  next
                    assume npred: "\<not> tag_T u = T_PRED"
                    show "eval_fuel (S n) u ?A2 = S q"
                    proof (rule cases_bool[where q="tag_T u = T_IFZ"])
                      show "(tag_T u = T_IFZ) B"
                        by (rule ifzB)
                    next
                      assume tg: "tag_T u = T_IFZ"
                      have freshParts:
                        "fresh_T 2 (hyp_of (load_T u)) \<and>
                         fresh_T 2 (hyp_of (conc_of (load_T u))) \<and>
                         fresh_T 2 (conc_of (conc_of (load_T u)))"
                        by (rule fresh_T_ifzD[OF twoN u freshU tg])
                      have freshCondThen:
                        "fresh_T 2 (hyp_of (load_T u)) \<and>
                         fresh_T 2 (hyp_of (conc_of (load_T u)))"
                        by (rule conjE1[OF freshParts])
                      have freshCond: "fresh_T 2 (hyp_of (load_T u))"
                        by (rule conjE1[OF freshCondThen])
                      have freshThen: "fresh_T 2 (hyp_of (conc_of (load_T u)))"
                        by (rule conjE2[OF freshCondThen])
                      have freshElse: "fresh_T 2 (conc_of (conc_of (load_T u)))"
                        by (rule conjE2[OF freshParts])
                      have IHcond:
                        "\<And>z. eval_fuel n (subst_body (hyp_of (load_T u)) x y) A = S z \<Longrightarrow>
                          eval_fuel n (hyp_of (load_T u)) ?A2 = S z"
                      proof -
                        fix z
                        assume success: "eval_fuel n (subst_body (hyp_of (load_T u)) x y) A = S z"
                        show "eval_fuel n (hyp_of (load_T u)) ?A2 = S z"
                          by (rule IHmeta[OF condN freshCond success])
                      qed
                      have IHthen:
                        "\<And>z. eval_fuel n (subst_body (hyp_of (conc_of (load_T u))) x y) A = S z \<Longrightarrow>
                          eval_fuel n (hyp_of (conc_of (load_T u))) ?A2 = S z"
                      proof -
                        fix z
                        assume success: "eval_fuel n (subst_body (hyp_of (conc_of (load_T u))) x y) A = S z"
                        show "eval_fuel n (hyp_of (conc_of (load_T u))) ?A2 = S z"
                          by (rule IHmeta[OF leftN freshThen success])
                      qed
                      have IHelse:
                        "\<And>z. eval_fuel n (subst_body (conc_of (conc_of (load_T u))) x y) A = S z \<Longrightarrow>
                          eval_fuel n (conc_of (conc_of (load_T u))) ?A2 = S z"
                      proof -
                        fix z
                        assume success: "eval_fuel n (subst_body (conc_of (conc_of (load_T u))) x y) A = S z"
                        show "eval_fuel n (conc_of (conc_of (load_T u))) ?A2 = S z"
                          by (rule IHmeta[OF rightN freshElse success])
                      qed
                      show "eval_fuel (S n) u ?A2 = S q"
                        by (rule eval_fuel_subst_body_ifzD[OF n u x y A vx vy tg result IHcond IHthen IHelse])
                    next
                      assume nifz: "\<not> tag_T u = T_IFZ"
                      have tg: "tag_T u = T_APP"
                        by (rule fresh_T_app_tag[OF twoN u freshU nvar nzero nsuc npred nifz])
                      have freshArgs:
                        "fresh_T 2 (hyp_of (conc_of (load_T u))) \<and>
                         fresh_T 2 (conc_of (conc_of (load_T u)))"
                        by (rule fresh_T_appD[OF twoN u freshU nvar nzero nsuc npred nifz])
                      have freshArg1: "fresh_T 2 (hyp_of (conc_of (load_T u)))"
                        by (rule conjE1[OF freshArgs])
                      have freshArg2: "fresh_T 2 (conc_of (conc_of (load_T u)))"
                        by (rule conjE2[OF freshArgs])
                      have IHarg1:
                        "\<And>z. eval_fuel n (subst_body (hyp_of (conc_of (load_T u))) x y) A = S z \<Longrightarrow>
                          eval_fuel n (hyp_of (conc_of (load_T u))) ?A2 = S z"
                      proof -
                        fix z
                        assume success: "eval_fuel n (subst_body (hyp_of (conc_of (load_T u))) x y) A = S z"
                        show "eval_fuel n (hyp_of (conc_of (load_T u))) ?A2 = S z"
                          by (rule IHmeta[OF leftN freshArg1 success])
                      qed
                      have IHarg2:
                        "\<And>z. eval_fuel n (subst_body (conc_of (conc_of (load_T u))) x y) A = S z \<Longrightarrow>
                          eval_fuel n (conc_of (conc_of (load_T u))) ?A2 = S z"
                      proof -
                        fix z
                        assume success: "eval_fuel n (subst_body (conc_of (conc_of (load_T u))) x y) A = S z"
                        show "eval_fuel n (conc_of (conc_of (load_T u))) ?A2 = S z"
                          by (rule IHmeta[OF rightN freshArg2 success])
                      qed
                      show "eval_fuel (S n) u ?A2 = S q"
                        by (rule eval_fuel_subst_body_appD[OF n u x y A vx vy tg result IHarg1 IHarg2])
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  have subN: "subst_body b x y N"
    by (rule subst_body_N[OF b x y])
  have r: "r N"
    by (rule eval_fuel_result_N[OF k subN A run])
  have mainB:
    "\<forall>q. fresh_T 2 b \<longrightarrow>
      (eval_fuel k (subst_body b x y) A = S q) \<longrightarrow>
      eval_fuel k b ?A2 = S q"
    by (rule forallE[where a=b, OF main b])
  have mainR:
    "fresh_T 2 b \<longrightarrow>
      (eval_fuel k (subst_body b x y) A = S r) \<longrightarrow>
      eval_fuel k b ?A2 = S r"
    by (rule forallE[where a=r, OF mainB r])
  have runImp:
    "(eval_fuel k (subst_body b x y) A = S r) \<longrightarrow>
      eval_fuel k b ?A2 = S r"
    using mainR fresh by (rule implE)
  show ?thesis
    using runImp run by (rule implE)
qed

lemma evals_subst_bodyD:
  assumes b: "b N" and x: "x N" and y: "y N" and A: "A N"
      and vx: "vx N" and vy: "vy N"
      and evx: "evals x A vx" and evy: "evals y A vy"
      and fresh: "fresh_T 2 b"
      and ev: "evals (subst_body b x y) A r"
  shows "evals b (vx \<triangleright> vy \<triangleright> Nil) r"
proof -
  show ?thesis
    using ev
  proof (rule evalsE)
    fix k
    assume k: "k N"
        and run: "eval_fuel k (subst_body b x y) A = S r"
    have transported: "eval_fuel k b (vx \<triangleright> vy \<triangleright> Nil) = S r"
      by (rule eval_fuel_subst_bodyD[OF k b x y A vx vy evx evy fresh run])
    show "evals b (vx \<triangleright> vy \<triangleright> Nil) r"
      by (rule evalsI[OF k transported])
  qed
qed

lemma dfn_is_rangeE:
  assumes d: "d N"
      and di: "dfn_is d k b"
  shows "d < len dfns = 1"
proof -
  have ld: "len dfns N"
    by (rule len_nat[OF dfns_N])
  have gB: "(d < len dfns = 1) B"
    by (rule eqBool[OF less_terminates[OF d ld]], simp)
  have R:
    "if d < len dfns = 1
     then nth d dfns = b \<and> fresh_T k b
     else False"
    using di by (rule defI[OF dfn_is_def])
  show ?thesis
  proof (rule cases_bool[where q="d < len dfns = 1"])
    show "(d < len dfns = 1) B"
      by (rule gB)
  next
    assume g: "d < len dfns = 1"
    show ?thesis
      by (rule g)
  next
    assume ng: "\<not> d < len dfns = 1"
    have F: "False"
      using ng R by (rule notcond_thenE)
    show ?thesis
      by (rule exF[OF F not_false])
  qed
qed

lemma dfn_is_freshE:
  assumes d: "d N"
      and di: "dfn_is d k b"
  shows "fresh_T k b"
proof -
  have dr: "d < len dfns = 1"
    using d di by (rule dfn_is_rangeE)
  have R:
    "if d < len dfns = 1
     then nth d dfns = b \<and> fresh_T k b
     else False"
    using di by (rule defI[OF dfn_is_def])
  have C: "nth d dfns = b \<and> fresh_T k b"
    using dr R by (rule cond_thenE)
  show ?thesis
    using C by (rule conjE2)
qed


lemma evals_subst_body_appI:
  assumes d: "d N" and x: "x N" and y: "y N" and A: "A N"
      and vx: "vx N" and vy: "vy N"
      and di: "dfn_is d 2 (nth d dfns)"
      and evx: "evals x A vx" and evy: "evals y A vy"
      and evbody: "evals (subst_body (nth d dfns) x y) A r"
  shows "evals (pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>) A r"
proof -
  have dr: "d < len dfns = 1"
    by (rule dfn_is_rangeE[OF d di])
  have bodyN: "nth d dfns N"
    using dfns_N dr by (rule nth_in_range_N)
  have fresh: "fresh_T 2 (nth d dfns)"
    by (rule dfn_is_freshE[OF d di])
  have bodyEval: "evals (nth d dfns) (vx \<triangleright> vy \<triangleright> Nil) r"
    by (rule evals_subst_bodyD[OF bodyN x y A vx vy evx evy fresh evbody])
  show ?thesis
    by (rule evals_appI[OF d x y A evx evy bodyEval])
qed

end

(* ===== DEAD CODE: superseded by the fuel/step-indexed stack (bga_fuller).
   This locale's soundness rested on the (unprovable-by-term-induction)
   substitution lemmas sat_subst_F / sat_hyp_put, left. =====
locale bga_subst_semantics = bga_semantics + bga_subst +
  fixes asn_put :: "asn \<Rightarrow> num \<Rightarrow> val \<Rightarrow> asn"
  assumes  asn_put_def:  "asn_put A i v :=  
              if i = 0 then
                   if A = Nil then v \<triangleright> Nil
                   else v \<triangleright> list_tl A
              else if A = Nil then 0 \<triangleright> asn_put Nil (i - 1) v
              else list_hd A \<triangleright> asn_put (list_tl A) (i - 1) v"
begin

text \<open>Freshness is inherited by every member of a hypothesis list.
  All the propositions involved (fresh_H, fresh_F, membership) are proper
  booleans, so we can run the induction through the grounded object
  implication.\<close>
lemma fresh_H_mem:
  assumes i: "i N" and G: "G N" and f: "f N"
      and fr: "fresh_H i G" and mm: "f \<in> G"
  shows "fresh_F i f"
proof -
  have main: "fresh_H i G \<longrightarrow> (f \<in> G \<longrightarrow> fresh_F i f)"
  proof (rule list_induct[OF G])
    show "fresh_H i Nil \<longrightarrow> (f \<in> Nil \<longrightarrow> fresh_F i f)"
    proof (rule implI)
      show "fresh_H i Nil B" by (rule fresh_H_bool[OF i nil_nat])
    next
      assume "fresh_H i Nil"
      show "f \<in> Nil \<longrightarrow> fresh_F i f"
      proof (rule implI)
        show "(f \<in> Nil) B" by (rule mem_bool[OF f nil_nat])
      next
        assume mn: "f \<in> Nil"
        show "fresh_F i f" by (rule exF[OF mn mem_nil])
      qed
    qed
  next
    fix h t
    assume h: "h N" and t: "t N"
       and IH: "fresh_H i t \<longrightarrow> (f \<in> t \<longrightarrow> fresh_F i f)"
    have ht: "h \<triangleright> t N" using h t by simp
    show "fresh_H i (h \<triangleright> t) \<longrightarrow> (f \<in> (h \<triangleright> t) \<longrightarrow> fresh_F i f)"
    proof (rule implI)
      show "fresh_H i (h \<triangleright> t) B" by (rule fresh_H_bool[OF i ht])
    next
      assume frht: "fresh_H i (h \<triangleright> t)"
      have ne: "\<not> (h \<triangleright> t = Nil)" using h t by simp
      have unf0: "if (h \<triangleright> t) = Nil then True
                    else fresh_F i (list_hd (h \<triangleright> t)) \<and> fresh_H i (list_tl (h \<triangleright> t))"
        using frht by (rule defI[OF fresh_H_def[where k=i and G="h \<triangleright> t"]])
      have conj0: "fresh_F i (list_hd (h \<triangleright> t)) \<and> fresh_H i (list_tl (h \<triangleright> t))"
        by (rule notcond_thenE[OF ne unf0])
      have frh: "fresh_F i h"
        using conjE1[OF conj0] by (simp only: list_hd_cons[OF h t])
      have frt: "fresh_H i t"
        using conjE2[OF conj0] by (simp only: list_tl_cons[OF h t])
      show "f \<in> (h \<triangleright> t) \<longrightarrow> fresh_F i f"
      proof (rule implI)
        show "(f \<in> (h \<triangleright> t)) B" by (rule mem_bool[OF f ht])
      next
        assume mm2: "f \<in> (h \<triangleright> t)"
        have split: "f \<in> (h \<triangleright> t) \<longleftrightarrow> (if h = f then True else f \<in> t)"
          by (rule mem_cons[OF h t f])
        have cond: "if h = f then True else f \<in> t"
          by (rule implE[OF iffE1[OF split] mm2])
        show "fresh_F i f"
        proof (rule cases_bool[where q="h = f"])
          show "(h = f) B" by (rule eqBool[OF h f])
        next
          assume hf: "h = f"
          show "fresh_F i f"
            using hf frh by (rule eqSubst[where Q="\<lambda>z. fresh_F i z"])
        next
          assume hf: "\<not> h = f"
          have ft: "f \<in> t" by (rule notcond_thenE[OF hf cond])
          have imp1: "f \<in> t \<longrightarrow> fresh_F i f" by (rule implE[OF IH frt])
          show "fresh_F i f" by (rule implE[OF imp1 ft])
        qed
      qed
    qed
  qed
  have imp1: "f \<in> G \<longrightarrow> fresh_F i f" by (rule implE[OF main fr])
  show "fresh_F i f" by (rule implE[OF imp1 mm])
qed

(* 4th is maybe a bit hard?*)
lemma sat_subst_F: "\<lbrakk>f N; i N; s N\<rbrakk> \<Longrightarrow> sat (subst_F f i s) A \<longleftrightarrow> sat f (asn_put A i (eval s A))"


lemma sat_hyp_put: "\<lbrakk>G N; i N; v N; fresh_H i G; sat_hyp G A\<rbrakk> \<Longrightarrow> sat_hyp G (asn_put A i v)"


lemma nth_suc_cons:
  assumes k: "k N" and h: "h N" and t: "t N" and nk: "nth k t N"
  shows "nth (S k) (h \<triangleright> t) = nth k t"
proof -
  have ne: "\<not> h \<triangleright> t = Nil" using h t by simp
  have nz: "\<not> S k = 0" using k by simp
  have sk1: "S k - 1 = k" using k by simp
  have tl: "list_tl (h \<triangleright> t) = t" using h t by simp
  have deep: "nth (S k - 1) (list_tl (h \<triangleright> t)) = nth k t" using sk1 tl nk by simp
  have inner: "(if S k = 0 then list_hd (h \<triangleright> t) else nth (S k - 1) (list_tl (h \<triangleright> t))) = nth k t"
    using nz nk deep by (rule condI2Eq)
  show ?thesis
    by (rule defE[OF nth_def[where i="S k" and xs="h \<triangleright> t"]], rule condI2Eq[OF ne nk inner])
qed

text \<open>With the totalised nth (out-of-range yields 0 rather
  than omega), "nth i Nil" reduces to 0 and nth
  is everywhere grounded.\<close>
lemma nth_nil: "nth i Nil = 0"
  apply (rule defE[OF nth_def[where i=i and xs=Nil]])
  apply (rule condI1Eq[where d=0])
    apply (rule nil_nat[unfolded isNat_def])
   apply (rule nat0)
  apply (rule nat0[unfolded isNat_def])
  done

lemma nth_N:
  assumes xs: "xs N"
  shows "\<forall>i. nth i xs N"
proof (rule list_induct[OF xs])
  show "\<forall>i. nth i Nil N"
  proof (rule forallI)
    fix i assume iN: "i N"
    show "nth i Nil N"
      using eqSym[OF nth_nil] nat0 by (rule eqSubst[where Q="\<lambda>z. z N"])
  qed
next
  fix h t
  assume h: "h N" and t: "t N" and IH: "\<forall>i. nth i t N"
  show "\<forall>i. nth i (h \<triangleright> t) N"
  proof (rule forallI)
    fix i assume iN: "i N"
    show "nth i (h \<triangleright> t) N"
    proof (rule cases_nat_2[where x=i])
      show "i N" by (rule iN)
    next
      assume "i = 0"
      show "nth 0 (h \<triangleright> t) N"
        using eqSym[OF nth_zero_cons[OF h t]] h
        by (rule eqSubst[where Q="\<lambda>z. z N"])
    next
      fix k assume k: "k N" and ik: "i = S k"
      have nkt: "nth k t N" by (rule forallE[OF IH k])
      have red: "nth (S k) (h \<triangleright> t) = nth k t" by (rule nth_suc_cons[OF k h t nkt])
      show "nth (S k) (h \<triangleright> t) N"
        using eqSym[OF red] nkt by (rule eqSubst[where Q="\<lambda>z. z N"])
    qed
  qed
qed

lemma nth_N':
  assumes xs: "xs N" and i: "i N"
  shows "nth i xs N"
  by (rule forallE[OF nth_N[OF xs] i])

text \<open>These need A N (for a junk A the
  guard A = Nil is not grounded).\<close>

lemma asn_put_N:
  assumes A: "A N" and i: "i N" and v: "v N"
  shows "asn_put A i v N"
proof -
  have main: "\<forall>b. asn_put b i v N"
  proof (rule ind[OF i])
    show "\<forall>b. asn_put b 0 v N"
    proof (rule forallI)
      fix b assume B: "b N"
      show "asn_put b 0 v N"
      proof (rule cases_bool[where q = "b = Nil"])
        show "(b = Nil) B" by (rule eqBool[OF B nil_nat])
      next
        assume c: "b = Nil"
        have d: "v \<triangleright> Nil N" using v by simp
        have r: "asn_put b 0 v = v \<triangleright> Nil"
          apply (rule defE[OF asn_put_def[where A = b and i = 0 and v = v]])
          apply (rule condI1Eq[where d = "v \<triangleright> Nil"], rule zeroRefl, rule d)
          apply (rule condI1Eq[where d = "v \<triangleright> Nil"], rule c, rule d, rule d[unfolded isNat_def])
          done
        show "asn_put b 0 v N" by (rule eq_impl_term[OF r])
      next
        assume c: "\<not> b = Nil"
        have d: "v \<triangleright> list_tl b N" using v B by simp
        have r: "asn_put b 0 v = v \<triangleright> list_tl b"
          apply (rule defE[OF asn_put_def[where A = b and i = 0 and v = v]])
          apply (rule condI1Eq[where d = "v \<triangleright> list_tl b"], rule zeroRefl, rule d)
          apply (rule condI2Eq[where d = "v \<triangleright> list_tl b"], rule c, rule d, rule d[unfolded isNat_def])
          done
        show "asn_put b 0 v N" by (rule eq_impl_term[OF r])
      qed
    qed
  next
    fix k assume k: "k N" and IH: "\<forall>b. asn_put b k v N"
    have nz: "\<not> S k = 0" using k by simp
    have sk1: "S k - 1 = k" using k by simp
    show "\<forall>b. asn_put b (S k) v N"
    proof (rule forallI)
      fix b assume B: "b N"
      show "asn_put b (S k) v N"
      proof (rule cases_bool[where q = "b = Nil"])
        show "(b = Nil) B" by (rule eqBool[OF B nil_nat])
      next
        assume c: "b = Nil"
        have recN: "asn_put Nil k v N" by (rule forallE[OF IH nil_nat])
        have d: "0 \<triangleright> asn_put Nil k v N" using recN by simp
        have r: "asn_put b (S k) v = 0 \<triangleright> asn_put Nil k v"
          apply (rule defE[OF asn_put_def[where A = b and i = "S k" and v = v]])
          apply (rule condI2Eq[where d = "0 \<triangleright> asn_put Nil k v"], rule nz, rule d)
          apply (rule condI1Eq[where d = "0 \<triangleright> asn_put Nil k v"], rule c, rule d)
          apply (rule eqSubst[where Q = "\<lambda>n. 0 \<triangleright> asn_put Nil n v = 0 \<triangleright> asn_put Nil k v", OF eqSym[OF sk1]], rule d[unfolded isNat_def])
          done
        show "asn_put b (S k) v N" by (rule eq_impl_term[OF r])
      next
        assume c: "\<not> b = Nil"
        have recN: "asn_put (list_tl b) k v N" by (rule forallE[OF IH list_tl_nat[OF B]])
        have d: "list_hd b \<triangleright> asn_put (list_tl b) k v N" using B recN by simp
        have r: "asn_put b (S k) v = list_hd b \<triangleright> asn_put (list_tl b) k v"
          apply (rule defE[OF asn_put_def[where A = b and i = "S k" and v = v]])
          apply (rule condI2Eq[where d = "list_hd b \<triangleright> asn_put (list_tl b) k v"], rule nz, rule d)
          apply (rule condI2Eq[where d = "list_hd b \<triangleright> asn_put (list_tl b) k v"], rule c, rule d)
          apply (rule eqSubst[where Q = "\<lambda>n. list_hd b \<triangleright> asn_put (list_tl b) n v = list_hd b \<triangleright> asn_put (list_tl b) k v", OF eqSym[OF sk1]], rule d[unfolded isNat_def])
          done
        show "asn_put b (S k) v N" by (rule eq_impl_term[OF r])
      qed
    qed
  qed
  show ?thesis by (rule forallE[OF main A])
qed

lemma asn_put_0_nil:
  assumes v: "v N" shows "asn_put Nil 0 v = v \<triangleright> Nil"
proof -
  have d: "v \<triangleright> Nil N" using v by simp
  show ?thesis
    apply (rule defE[OF asn_put_def[where A = Nil and i = 0 and v = v]])
    apply (rule condI1Eq[where d = "v \<triangleright> Nil"], rule zeroRefl, rule d)
    apply (rule condI1Eq[where d = "v \<triangleright> Nil"], rule nil_nat[unfolded isNat_def], rule d, rule d[unfolded isNat_def])
    done
qed

lemma asn_put_0_ne:
  assumes A: "A N" and v: "v N" and ne: "\<not> A = Nil"
  shows "asn_put A 0 v = v \<triangleright> list_tl A"
proof -
  have d: "v \<triangleright> list_tl A N" using v A by simp
  show ?thesis
    apply (rule defE[OF asn_put_def[where A = A and i = 0 and v = v]])
    apply (rule condI1Eq[where d = "v \<triangleright> list_tl A"], rule zeroRefl, rule d)
    apply (rule condI2Eq[where d = "v \<triangleright> list_tl A"], rule ne, rule d, rule d[unfolded isNat_def])
    done
qed

lemma asn_put_S_nil:
  assumes v: "v N" and k: "k N"
  shows "asn_put Nil (S k) v = 0 \<triangleright> asn_put Nil k v"
proof -
  have nz: "\<not> S k = 0" using k by simp
  have sk1: "S k - 1 = k" using k by simp
  have recN: "asn_put Nil k v N" by (rule asn_put_N[OF nil_nat k v])
  have d: "0 \<triangleright> asn_put Nil k v N" using recN by simp
  show ?thesis
    apply (rule defE[OF asn_put_def[where A = Nil and i = "S k" and v = v]])
    apply (rule condI2Eq[where d = "0 \<triangleright> asn_put Nil k v"], rule nz, rule d)
    apply (rule condI1Eq[where d = "0 \<triangleright> asn_put Nil k v"], rule nil_nat[unfolded isNat_def], rule d)
    apply (rule eqSubst[where Q = "\<lambda>n. 0 \<triangleright> asn_put Nil n v = 0 \<triangleright> asn_put Nil k v", OF eqSym[OF sk1]], rule d[unfolded isNat_def])
    done
qed

lemma asn_put_S_ne:
  assumes A: "A N" and v: "v N" and k: "k N" and ne: "\<not> A = Nil"
  shows "asn_put A (S k) v = list_hd A \<triangleright> asn_put (list_tl A) k v"
proof -
  have nz: "\<not> S k = 0" using k by simp
  have sk1: "S k - 1 = k" using k by simp
  have recN: "asn_put (list_tl A) k v N" by (rule asn_put_N[OF list_tl_nat[OF A] k v])
  have d: "list_hd A \<triangleright> asn_put (list_tl A) k v N" using A recN by simp
  show ?thesis
    apply (rule defE[OF asn_put_def[where A = A and i = "S k" and v = v]])
    apply (rule condI2Eq[where d = "list_hd A \<triangleright> asn_put (list_tl A) k v"], rule nz, rule d)
    apply (rule condI2Eq[where d = "list_hd A \<triangleright> asn_put (list_tl A) k v"], rule ne, rule d)
    apply (rule eqSubst[where Q = "\<lambda>n. list_hd A \<triangleright> asn_put (list_tl A) n v = list_hd A \<triangleright> asn_put (list_tl A) k v", OF eqSym[OF sk1]], rule d[unfolded isNat_def])
    done
qed

lemma nth_put_eq:
  assumes A: "A N" and i: "i N" and v: "v N"
  shows "nth i (asn_put A i v) = v"
proof -
  have main: "\<forall>b. nth i (asn_put b i v) = v"
  proof (rule ind[OF i])
    show "\<forall>b. nth 0 (asn_put b 0 v) = v"
    proof (rule forallI)
      fix b assume B: "b N"
      show "nth 0 (asn_put b 0 v) = v"
      proof (rule cases_bool[where q = "b = Nil"])
        show "(b = Nil) B" by (rule eqBool[OF B nil_nat])
      next
        assume c: "b = Nil"
        have r: "asn_put b 0 v = v \<triangleright> Nil"
          using eqSym[OF c] asn_put_0_nil[OF v]
          by (rule eqSubst[where Q = "\<lambda>z. asn_put z 0 v = v \<triangleright> Nil"])
        show "nth 0 (asn_put b 0 v) = v"
          using eqSym[OF r] nth_zero_cons[OF v nil_nat]
          by (rule eqSubst[where Q = "\<lambda>z. nth 0 z = v"])
      next
        assume c: "\<not> b = Nil"
        have r: "asn_put b 0 v = v \<triangleright> list_tl b" by (rule asn_put_0_ne[OF B v c])
        show "nth 0 (asn_put b 0 v) = v"
          using eqSym[OF r] nth_zero_cons[OF v list_tl_nat[OF B]]
          by (rule eqSubst[where Q = "\<lambda>z. nth 0 z = v"])
      qed
    qed
  next
    fix k assume k: "k N" and IH: "\<forall>b. nth k (asn_put b k v) = v"
    show "\<forall>b. nth (S k) (asn_put b (S k) v) = v"
    proof (rule forallI)
      fix b assume B: "b N"
      show "nth (S k) (asn_put b (S k) v) = v"
      proof (rule cases_bool[where q = "b = Nil"])
        show "(b = Nil) B" by (rule eqBool[OF B nil_nat])
      next
        assume c: "b = Nil"
        have r: "asn_put b (S k) v = 0 \<triangleright> asn_put Nil k v"
          using eqSym[OF c] asn_put_S_nil[OF v k]
          by (rule eqSubst[where Q = "\<lambda>z. asn_put z (S k) v = 0 \<triangleright> asn_put Nil k v"])
        have ih: "nth k (asn_put Nil k v) = v" by (rule forallE[OF IH nil_nat])
        have nthN: "nth k (asn_put Nil k v) N" by (rule eq_impl_term[OF ih])
        have recN: "asn_put Nil k v N" by (rule asn_put_N[OF nil_nat k v])
        have sc: "nth (S k) (0 \<triangleright> asn_put Nil k v) = nth k (asn_put Nil k v)"
          by (rule nth_suc_cons[OF k nat0 recN nthN])
        have sv: "nth (S k) (0 \<triangleright> asn_put Nil k v) = v" using sc ih by (rule eq_trans)
        show "nth (S k) (asn_put b (S k) v) = v"
          using eqSym[OF r] sv by (rule eqSubst[where Q = "\<lambda>z. nth (S k) z = v"])
      next
        assume c: "\<not> b = Nil"
        have r: "asn_put b (S k) v = list_hd b \<triangleright> asn_put (list_tl b) k v" by (rule asn_put_S_ne[OF B v k c])
        have ih: "nth k (asn_put (list_tl b) k v) = v" by (rule forallE[OF IH list_tl_nat[OF B]])
        have nthN: "nth k (asn_put (list_tl b) k v) N" by (rule eq_impl_term[OF ih])
        have recN: "asn_put (list_tl b) k v N" by (rule asn_put_N[OF list_tl_nat[OF B] k v])
        have sc: "nth (S k) (list_hd b \<triangleright> asn_put (list_tl b) k v) = nth k (asn_put (list_tl b) k v)"
          by (rule nth_suc_cons[OF k list_hd_nat[OF B] recN nthN])
        have sv: "nth (S k) (list_hd b \<triangleright> asn_put (list_tl b) k v) = v" using sc ih by (rule eq_trans)
        show "nth (S k) (asn_put b (S k) v) = v"
          using eqSym[OF r] sv by (rule eqSubst[where Q = "\<lambda>z. nth (S k) z = v"])
      qed
    qed
  qed
  show ?thesis by (rule forallE[OF main A])
qed

lemma nth_zero_ne_nil:
  assumes L: "L N" and ne: "\<not> L = Nil"
  shows "nth 0 L = list_hd L"
proof -
  have rec: "list_hd L \<triangleright> list_tl L = L" by (rule cons_reconstr[OF L ne])
  have z: "nth 0 (list_hd L \<triangleright> list_tl L) = list_hd L"
    by (rule nth_zero_cons[OF list_hd_nat[OF L] list_tl_nat[OF L]])
  show ?thesis
    using rec z by (rule eqSubst[where Q="\<lambda>z. nth 0 z = list_hd L"])
qed

lemma nth_suc_ne_nil:
  assumes m: "m N" and L: "L N" and ne: "\<not> L = Nil"
  shows "nth (S m) L = nth m (list_tl L)"
proof -
  have rec: "list_hd L \<triangleright> list_tl L = L" by (rule cons_reconstr[OF L ne])
  have nmtl: "nth m (list_tl L) N" by (rule nth_N'[OF list_tl_nat[OF L] m])
  have z: "nth (S m) (list_hd L \<triangleright> list_tl L) = nth m (list_tl L)"
    by (rule nth_suc_cons[OF m list_hd_nat[OF L] list_tl_nat[OF L] nmtl])
  show ?thesis
    using rec z by (rule eqSubst[where Q="\<lambda>z. nth (S m) z = nth m (list_tl L)"])
qed

text \<open>Coincidence away from the updated index: for @{text "j \<noteq> i"} the value at
  @{text j} is unaffected by @{text "asn_put A i v"}.  Now that @{text nth} is
  total this holds unconditionally (no range guard).\<close>
lemma nth_put_ne:
  assumes A: "A N" and i: "i N" and v: "v N" and j: "j N" and ne: "\<not> j = i"
  shows "nth j (asn_put A i v) = nth j A"
proof -
  have main: "\<forall>A. \<forall>j. (\<not> j = i) \<longrightarrow> nth j (asn_put A i v) = nth j A"
  proof (rule ind[OF i])
    (* ================= base: i = 0 ================= *)
    show "\<forall>A. \<forall>j. (\<not> j = 0) \<longrightarrow> nth j (asn_put A 0 v) = nth j A"
    proof (rule forallI)
      fix Aa assume Aa: "Aa N"
      show "\<forall>j. (\<not> j = 0) \<longrightarrow> nth j (asn_put Aa 0 v) = nth j Aa"
      proof (rule forallI)
        fix jj assume jj: "jj N"
        show "(\<not> jj = 0) \<longrightarrow> nth jj (asn_put Aa 0 v) = nth jj Aa"
        proof (rule implI)
          show "(\<not> jj = 0) B" by (rule not_bool[OF eqBool[OF jj nat0]])
        next
          assume jnz: "\<not> jj = 0"
          show "nth jj (asn_put Aa 0 v) = nth jj Aa"
          proof (rule cases_nat_2[where x=jj])
            show "jj N" by (rule jj)
          next
            assume jz: "jj = 0"
            show "nth 0 (asn_put Aa 0 v) = nth 0 Aa" by (rule exF[OF jz jnz])
          next
            fix m assume m: "m N" and jm: "jj = S m"
            show "nth (S m) (asn_put Aa 0 v) = nth (S m) Aa"
            proof (rule cases_bool[where q="Aa = Nil"])
              show "(Aa = Nil) B" by (rule eqBool[OF Aa nil_nat])
            next
              assume anil: "Aa = Nil"
              have nmNil: "nth m Nil N" by (rule nth_N'[OF nil_nat m])
              have e1: "asn_put Nil 0 v = v \<triangleright> Nil" by (rule asn_put_0_nil[OF v])
              have e2: "nth (S m) (v \<triangleright> Nil) = nth m Nil"
                by (rule nth_suc_cons[OF m v nil_nat nmNil])
              have e3: "nth (S m) (asn_put Nil 0 v) = nth m Nil"
                using eqSym[OF e1] e2 by (rule eqSubst[where Q="\<lambda>z. nth (S m) z = nth m Nil"])
              have e4: "nth (S m) (asn_put Nil 0 v) = 0" using e3 nth_nil by (rule eq_trans)
              have gNil: "nth (S m) (asn_put Nil 0 v) = nth (S m) Nil"
                using e4 eqSym[OF nth_nil] by (rule eq_trans)
              show "nth (S m) (asn_put Aa 0 v) = nth (S m) Aa"
                using eqSym[OF anil] gNil
                by (rule eqSubst[where Q="\<lambda>z. nth (S m) (asn_put z 0 v) = nth (S m) z"])
            next
              assume ann: "\<not> Aa = Nil"
              have nmtl: "nth m (list_tl Aa) N" by (rule nth_N'[OF list_tl_nat[OF Aa] m])
              have e1: "asn_put Aa 0 v = v \<triangleright> list_tl Aa" by (rule asn_put_0_ne[OF Aa v ann])
              have e2: "nth (S m) (v \<triangleright> list_tl Aa) = nth m (list_tl Aa)"
                by (rule nth_suc_cons[OF m v list_tl_nat[OF Aa] nmtl])
              have lhs: "nth (S m) (asn_put Aa 0 v) = nth m (list_tl Aa)"
                using eqSym[OF e1] e2 by (rule eqSubst[where Q="\<lambda>z. nth (S m) z = nth m (list_tl Aa)"])
              have rhs: "nth (S m) Aa = nth m (list_tl Aa)" by (rule nth_suc_ne_nil[OF m Aa ann])
              show "nth (S m) (asn_put Aa 0 v) = nth (S m) Aa"
                using lhs eqSym[OF rhs] by (rule eq_trans)
            qed
          qed
        qed
      qed
    qed
  next
    (* ================= step: i = S k ================= *)
    fix k assume k: "k N"
      and IH: "\<forall>A. \<forall>j. (\<not> j = k) \<longrightarrow> nth j (asn_put A k v) = nth j A"
    show "\<forall>A. \<forall>j. (\<not> j = S k) \<longrightarrow> nth j (asn_put A (S k) v) = nth j A"
    proof (rule forallI)
      fix Aa assume Aa: "Aa N"
      show "\<forall>j. (\<not> j = S k) \<longrightarrow> nth j (asn_put Aa (S k) v) = nth j Aa"
      proof (rule forallI)
        fix jj assume jj: "jj N"
        show "(\<not> jj = S k) \<longrightarrow> nth jj (asn_put Aa (S k) v) = nth jj Aa"
        proof (rule implI)
          show "(\<not> jj = S k) B" by (rule not_bool[OF eqBool[OF jj natS[OF k]]])
        next
          assume jnz2: "\<not> jj = S k"
          show "nth jj (asn_put Aa (S k) v) = nth jj Aa"
          proof (rule cases_nat_2[where x=jj])
            show "jj N" by (rule jj)
          next
            assume jz: "jj = 0"
            show "nth 0 (asn_put Aa (S k) v) = nth 0 Aa"
            proof (rule cases_bool[where q="Aa = Nil"])
              show "(Aa = Nil) B" by (rule eqBool[OF Aa nil_nat])
            next
              assume anil: "Aa = Nil"
              have recN: "asn_put Nil k v N" by (rule asn_put_N[OF nil_nat k v])
              have e1: "asn_put Nil (S k) v = 0 \<triangleright> asn_put Nil k v" by (rule asn_put_S_nil[OF v k])
              have e2: "nth 0 (0 \<triangleright> asn_put Nil k v) = 0" by (rule nth_zero_cons[OF nat0 recN])
              have e3: "nth 0 (asn_put Nil (S k) v) = 0"
                using eqSym[OF e1] e2 by (rule eqSubst[where Q="\<lambda>z. nth 0 z = 0"])
              have gNil: "nth 0 (asn_put Nil (S k) v) = nth 0 Nil"
                using e3 eqSym[OF nth_nil] by (rule eq_trans)
              show "nth 0 (asn_put Aa (S k) v) = nth 0 Aa"
                using eqSym[OF anil] gNil
                by (rule eqSubst[where Q="\<lambda>z. nth 0 (asn_put z (S k) v) = nth 0 z"])
            next
              assume ann: "\<not> Aa = Nil"
              have recN: "asn_put (list_tl Aa) k v N" by (rule asn_put_N[OF list_tl_nat[OF Aa] k v])
              have e1: "asn_put Aa (S k) v = list_hd Aa \<triangleright> asn_put (list_tl Aa) k v"
                by (rule asn_put_S_ne[OF Aa v k ann])
              have e2: "nth 0 (list_hd Aa \<triangleright> asn_put (list_tl Aa) k v) = list_hd Aa"
                by (rule nth_zero_cons[OF list_hd_nat[OF Aa] recN])
              have lhs: "nth 0 (asn_put Aa (S k) v) = list_hd Aa"
                using eqSym[OF e1] e2 by (rule eqSubst[where Q="\<lambda>z. nth 0 z = list_hd Aa"])
              have rhs: "nth 0 Aa = list_hd Aa" by (rule nth_zero_ne_nil[OF Aa ann])
              show "nth 0 (asn_put Aa (S k) v) = nth 0 Aa"
                using lhs eqSym[OF rhs] by (rule eq_trans)
            qed
          next
            fix m assume m: "m N" and jm: "jj = S m"
            show "nth (S m) (asn_put Aa (S k) v) = nth (S m) Aa"
            proof (rule cases_bool[where q="m = k"])
              show "(m = k) B" by (rule eqBool[OF m k])
            next
              assume mk: "m = k"
              have smsk: "S m = S k" using mk by (rule sucCong)
              have jjsk: "jj = S k" using jm smsk by (rule eq_trans)
              show "nth (S m) (asn_put Aa (S k) v) = nth (S m) Aa"
                by (rule exF[OF jjsk jnz2])
            next
              assume mk: "\<not> m = k"
              show "nth (S m) (asn_put Aa (S k) v) = nth (S m) Aa"
              proof (rule cases_bool[where q="Aa = Nil"])
                show "(Aa = Nil) B" by (rule eqBool[OF Aa nil_nat])
              next
                assume anil: "Aa = Nil"
                have recN: "asn_put Nil k v N" by (rule asn_put_N[OF nil_nat k v])
                have nmrec: "nth m (asn_put Nil k v) N" by (rule nth_N'[OF recN m])
                have e1: "asn_put Nil (S k) v = 0 \<triangleright> asn_put Nil k v" by (rule asn_put_S_nil[OF v k])
                have e2: "nth (S m) (0 \<triangleright> asn_put Nil k v) = nth m (asn_put Nil k v)"
                  by (rule nth_suc_cons[OF m nat0 recN nmrec])
                have lhs1: "nth (S m) (asn_put Nil (S k) v) = nth m (asn_put Nil k v)"
                  using eqSym[OF e1] e2 by (rule eqSubst[where Q="\<lambda>z. nth (S m) z = nth m (asn_put Nil k v)"])
                have ihstep1: "\<forall>j. (\<not> j = k) \<longrightarrow> nth j (asn_put Nil k v) = nth j Nil"
                  by (rule forallE[OF IH nil_nat])
                have ihstep2: "(\<not> m = k) \<longrightarrow> nth m (asn_put Nil k v) = nth m Nil"
                  by (rule forallE[OF ihstep1 m])
                have ihm: "nth m (asn_put Nil k v) = nth m Nil" by (rule implE[OF ihstep2 mk])
                have lhs2: "nth (S m) (asn_put Nil (S k) v) = nth m Nil" using lhs1 ihm by (rule eq_trans)
                have lhsz: "nth (S m) (asn_put Nil (S k) v) = 0" using lhs2 nth_nil by (rule eq_trans)
                have gNil: "nth (S m) (asn_put Nil (S k) v) = nth (S m) Nil"
                  using lhsz eqSym[OF nth_nil] by (rule eq_trans)
                show "nth (S m) (asn_put Aa (S k) v) = nth (S m) Aa"
                  using eqSym[OF anil] gNil
                  by (rule eqSubst[where Q="\<lambda>z. nth (S m) (asn_put z (S k) v) = nth (S m) z"])
              next
                assume ann: "\<not> Aa = Nil"
                have recN: "asn_put (list_tl Aa) k v N" by (rule asn_put_N[OF list_tl_nat[OF Aa] k v])
                have nmrec: "nth m (asn_put (list_tl Aa) k v) N" by (rule nth_N'[OF recN m])
                have e1: "asn_put Aa (S k) v = list_hd Aa \<triangleright> asn_put (list_tl Aa) k v"
                  by (rule asn_put_S_ne[OF Aa v k ann])
                have e2: "nth (S m) (list_hd Aa \<triangleright> asn_put (list_tl Aa) k v) = nth m (asn_put (list_tl Aa) k v)"
                  by (rule nth_suc_cons[OF m list_hd_nat[OF Aa] recN nmrec])
                have lhs1: "nth (S m) (asn_put Aa (S k) v) = nth m (asn_put (list_tl Aa) k v)"
                  using eqSym[OF e1] e2 by (rule eqSubst[where Q="\<lambda>z. nth (S m) z = nth m (asn_put (list_tl Aa) k v)"])
                have ihstep1: "\<forall>j. (\<not> j = k) \<longrightarrow> nth j (asn_put (list_tl Aa) k v) = nth j (list_tl Aa)"
                  by (rule forallE[OF IH list_tl_nat[OF Aa]])
                have ihstep2: "(\<not> m = k) \<longrightarrow> nth m (asn_put (list_tl Aa) k v) = nth m (list_tl Aa)"
                  by (rule forallE[OF ihstep1 m])
                have ihm: "nth m (asn_put (list_tl Aa) k v) = nth m (list_tl Aa)" by (rule implE[OF ihstep2 mk])
                have lhs2: "nth (S m) (asn_put Aa (S k) v) = nth m (list_tl Aa)" using lhs1 ihm by (rule eq_trans)
                have rhs: "nth (S m) Aa = nth m (list_tl Aa)" by (rule nth_suc_ne_nil[OF m Aa ann])
                show "nth (S m) (asn_put Aa (S k) v) = nth (S m) Aa"
                  using lhs2 eqSym[OF rhs] by (rule eq_trans)
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  have m1: "\<forall>j. (\<not> j = i) \<longrightarrow> nth j (asn_put A i v) = nth j A" by (rule forallE[OF main A])
  have m2: "(\<not> j = i) \<longrightarrow> nth j (asn_put A i v) = nth j A" by (rule forallE[OF m1 j])
  show ?thesis by (rule implE[OF m2 ne])
qed

lemma eval_var_put:
  assumes A: "A N" and i: "i N" and v: "v N"
  shows "eval (pack_T T_VAR i) (asn_put A i v) = v"
proof -
  have vpN: "pack_T T_VAR i N" by (rule pack_T_N[OF _ i], simp)
  have tg: "tag_T (pack_T T_VAR i) = T_VAR" by (rule tag_pack_T[OF _ i], simp)
  have ld: "load_T (pack_T T_VAR i) = i" by (rule load_pack_T[OF _ i], simp)
  have key: "nth i (asn_put A i v) = v" by (rule nth_put_eq[OF A i v])
  have H: "nth (load_T (pack_T T_VAR i)) (asn_put A i v) = v"
    using eqSym[OF ld] key by (rule eqSubst[where Q = "\<lambda>z. nth z (asn_put A i v) = v"])
  show ?thesis
    apply (rule defE[OF eval_def[where t = "pack_T T_VAR i" and A = "asn_put A i v"]])
    apply (rule condI1Eq[where d = v], rule tg, rule v, rule H)
    done
qed

lemma asn_put_overwrite:
  assumes A: "A N" and i: "i N" and v: "v N" and w: "w N"
  shows "asn_put (asn_put A i v) i w = asn_put A i w"
proof -
  have main: "\<forall>b. asn_put (asn_put b i v) i w = asn_put b i w"
  proof (rule ind[OF i])
    show "\<forall>b. asn_put (asn_put b 0 v) 0 w = asn_put b 0 w"
    proof (rule forallI)
      fix b assume B: "b N"
      show "asn_put (asn_put b 0 v) 0 w = asn_put b 0 w"
      proof (rule cases_bool[where q = "b = Nil"])
        show "(b = Nil) B" by (rule eqBool[OF B nil_nat])
      next
        assume c: "b = Nil"
        have vnil: "v \<triangleright> Nil N" by (rule cons_nat[OF v nil_nat])
        have r1: "asn_put b 0 v = v \<triangleright> Nil"
          using eqSym[OF c] asn_put_0_nil[OF v]
          by (rule eqSubst[where Q = "\<lambda>z. asn_put z 0 v = v \<triangleright> Nil"])
        have ne1: "\<not> v \<triangleright> Nil = Nil" using v by simp
        have r2: "asn_put (v \<triangleright> Nil) 0 w = w \<triangleright> list_tl (v \<triangleright> Nil)" by (rule asn_put_0_ne[OF vnil w ne1])
        have tl1: "list_tl (v \<triangleright> Nil) = Nil" by (rule list_tl_cons[OF v nil_nat])
        have r3: "asn_put b 0 w = w \<triangleright> Nil"
          using eqSym[OF c] asn_put_0_nil[OF w]
          by (rule eqSubst[where Q = "\<lambda>z. asn_put z 0 w = w \<triangleright> Nil"])
        have e2: "asn_put (v \<triangleright> Nil) 0 w = w \<triangleright> Nil"
          using tl1 r2 by (rule eqSubst[where Q = "\<lambda>z. asn_put (v \<triangleright> Nil) 0 w = w \<triangleright> z"])
        have eL: "asn_put (asn_put b 0 v) 0 w = w \<triangleright> Nil"
          using eqSym[OF r1] e2 by (rule eqSubst[where Q = "\<lambda>z. asn_put z 0 w = w \<triangleright> Nil"])
        show "asn_put (asn_put b 0 v) 0 w = asn_put b 0 w"
          using eL eqSym[OF r3] by (rule eq_trans)
      next
        assume c: "\<not> b = Nil"
        have tlB: "list_tl b N" using B by simp
        have vtl: "v \<triangleright> list_tl b N" by (rule cons_nat[OF v tlB])
        have r1: "asn_put b 0 v = v \<triangleright> list_tl b" by (rule asn_put_0_ne[OF B v c])
        have ne1: "\<not> v \<triangleright> list_tl b = Nil" using v tlB by simp
        have r2: "asn_put (v \<triangleright> list_tl b) 0 w = w \<triangleright> list_tl (v \<triangleright> list_tl b)" by (rule asn_put_0_ne[OF vtl w ne1])
        have tl1: "list_tl (v \<triangleright> list_tl b) = list_tl b" by (rule list_tl_cons[OF v tlB])
        have r3: "asn_put b 0 w = w \<triangleright> list_tl b" by (rule asn_put_0_ne[OF B w c])
        have e2: "asn_put (v \<triangleright> list_tl b) 0 w = w \<triangleright> list_tl b"
          using tl1 r2 by (rule eqSubst[where Q = "\<lambda>z. asn_put (v \<triangleright> list_tl b) 0 w = w \<triangleright> z"])
        have eL: "asn_put (asn_put b 0 v) 0 w = w \<triangleright> list_tl b"
          using eqSym[OF r1] e2 by (rule eqSubst[where Q = "\<lambda>z. asn_put z 0 w = w \<triangleright> list_tl b"])
        show "asn_put (asn_put b 0 v) 0 w = asn_put b 0 w"
          using eL eqSym[OF r3] by (rule eq_trans)
      qed
    qed
  next
    fix k assume k: "k N" and IH: "\<forall>b. asn_put (asn_put b k v) k w = asn_put b k w"
    show "\<forall>b. asn_put (asn_put b (S k) v) (S k) w = asn_put b (S k) w"
    proof (rule forallI)
      fix b assume B: "b N"
      show "asn_put (asn_put b (S k) v) (S k) w = asn_put b (S k) w"
      proof (rule cases_bool[where q = "b = Nil"])
        show "(b = Nil) B" by (rule eqBool[OF B nil_nat])
      next
        assume c: "b = Nil"
        have recvN: "asn_put Nil k v N" by (rule asn_put_N[OF nil_nat k v])
        have rv: "asn_put b (S k) v = 0 \<triangleright> asn_put Nil k v"
          using eqSym[OF c] asn_put_S_nil[OF v k]
          by (rule eqSubst[where Q = "\<lambda>z. asn_put z (S k) v = 0 \<triangleright> asn_put Nil k v"])
        have cne: "\<not> 0 \<triangleright> asn_put Nil k v = Nil" using recvN by simp
        have consN: "0 \<triangleright> asn_put Nil k v N" by (rule cons_nat[OF nat0 recvN])
        have r2: "asn_put (0 \<triangleright> asn_put Nil k v) (S k) w
                  = list_hd (0 \<triangleright> asn_put Nil k v) \<triangleright> asn_put (list_tl (0 \<triangleright> asn_put Nil k v)) k w"
          by (rule asn_put_S_ne[OF consN w k cne])
        have hd2: "list_hd (0 \<triangleright> asn_put Nil k v) = 0" by (rule list_hd_cons[OF nat0 recvN])
        have tl2: "list_tl (0 \<triangleright> asn_put Nil k v) = asn_put Nil k v" by (rule list_tl_cons[OF nat0 recvN])
        have ihNil: "asn_put (asn_put Nil k v) k w = asn_put Nil k w" by (rule forallE[OF IH nil_nat])
        have rw: "asn_put b (S k) w = 0 \<triangleright> asn_put Nil k w"
          using eqSym[OF c] asn_put_S_nil[OF w k]
          by (rule eqSubst[where Q = "\<lambda>z. asn_put z (S k) w = 0 \<triangleright> asn_put Nil k w"])
        have s1: "asn_put (0 \<triangleright> asn_put Nil k v) (S k) w
                  = 0 \<triangleright> asn_put (list_tl (0 \<triangleright> asn_put Nil k v)) k w"
          using hd2 r2 by (rule eqSubst[where Q = "\<lambda>z. asn_put (0 \<triangleright> asn_put Nil k v) (S k) w = z \<triangleright> asn_put (list_tl (0 \<triangleright> asn_put Nil k v)) k w"])
        have s2: "asn_put (0 \<triangleright> asn_put Nil k v) (S k) w = 0 \<triangleright> asn_put (asn_put Nil k v) k w"
          using tl2 s1 by (rule eqSubst[where Q = "\<lambda>z. asn_put (0 \<triangleright> asn_put Nil k v) (S k) w = 0 \<triangleright> asn_put z k w"])
        have s3: "asn_put (0 \<triangleright> asn_put Nil k v) (S k) w = 0 \<triangleright> asn_put Nil k w"
          using ihNil s2 by (rule eqSubst[where Q = "\<lambda>z. asn_put (0 \<triangleright> asn_put Nil k v) (S k) w = 0 \<triangleright> z"])
        have eL: "asn_put (asn_put b (S k) v) (S k) w = 0 \<triangleright> asn_put Nil k w"
          using eqSym[OF rv] s3 by (rule eqSubst[where Q = "\<lambda>z. asn_put z (S k) w = 0 \<triangleright> asn_put Nil k w"])
        show "asn_put (asn_put b (S k) v) (S k) w = asn_put b (S k) w"
          using eL eqSym[OF rw] by (rule eq_trans)
      next
        assume c: "\<not> b = Nil"
        have tlB: "list_tl b N" using B by simp
        have hdB: "list_hd b N" using B by simp
        have recvN: "asn_put (list_tl b) k v N" by (rule asn_put_N[OF tlB k v])
        have rv: "asn_put b (S k) v = list_hd b \<triangleright> asn_put (list_tl b) k v" by (rule asn_put_S_ne[OF B v k c])
        have cne: "\<not> list_hd b \<triangleright> asn_put (list_tl b) k v = Nil" using hdB recvN by simp
        have consN: "list_hd b \<triangleright> asn_put (list_tl b) k v N" by (rule cons_nat[OF hdB recvN])
        have r2: "asn_put (list_hd b \<triangleright> asn_put (list_tl b) k v) (S k) w
                  = list_hd (list_hd b \<triangleright> asn_put (list_tl b) k v)
                      \<triangleright> asn_put (list_tl (list_hd b \<triangleright> asn_put (list_tl b) k v)) k w"
          by (rule asn_put_S_ne[OF consN w k cne])
        have hd2: "list_hd (list_hd b \<triangleright> asn_put (list_tl b) k v) = list_hd b" by (rule list_hd_cons[OF hdB recvN])
        have tl2: "list_tl (list_hd b \<triangleright> asn_put (list_tl b) k v) = asn_put (list_tl b) k v" by (rule list_tl_cons[OF hdB recvN])
        have ihB: "asn_put (asn_put (list_tl b) k v) k w = asn_put (list_tl b) k w" by (rule forallE[OF IH tlB])
        have rw: "asn_put b (S k) w = list_hd b \<triangleright> asn_put (list_tl b) k w" by (rule asn_put_S_ne[OF B w k c])
        have s1: "asn_put (list_hd b \<triangleright> asn_put (list_tl b) k v) (S k) w
                  = list_hd b \<triangleright> asn_put (list_tl (list_hd b \<triangleright> asn_put (list_tl b) k v)) k w"
          using hd2 r2 by (rule eqSubst[where Q = "\<lambda>z. asn_put (list_hd b \<triangleright> asn_put (list_tl b) k v) (S k) w = z \<triangleright> asn_put (list_tl (list_hd b \<triangleright> asn_put (list_tl b) k v)) k w"])
        have s2: "asn_put (list_hd b \<triangleright> asn_put (list_tl b) k v) (S k) w
                  = list_hd b \<triangleright> asn_put (asn_put (list_tl b) k v) k w"
          using tl2 s1 by (rule eqSubst[where Q = "\<lambda>z. asn_put (list_hd b \<triangleright> asn_put (list_tl b) k v) (S k) w = list_hd b \<triangleright> asn_put z k w"])
        have s3: "asn_put (list_hd b \<triangleright> asn_put (list_tl b) k v) (S k) w
                  = list_hd b \<triangleright> asn_put (list_tl b) k w"
          using ihB s2 by (rule eqSubst[where Q = "\<lambda>z. asn_put (list_hd b \<triangleright> asn_put (list_tl b) k v) (S k) w = list_hd b \<triangleright> z"])
        have eL: "asn_put (asn_put b (S k) v) (S k) w = list_hd b \<triangleright> asn_put (list_tl b) k w"
          using eqSym[OF rv] s3 by (rule eqSubst[where Q = "\<lambda>z. asn_put z (S k) w = list_hd b \<triangleright> asn_put (list_tl b) k w"])
        show "asn_put (asn_put b (S k) v) (S k) w = asn_put b (S k) w"
          using eL eqSym[OF rw] by (rule eq_trans)
      qed
    qed
  qed
  show ?thesis by (rule forallE[OF main A])
qed

lemma nat_ind_sound:
  assumes p: "p N"
      and i: "i N"
      and a: "a N"
      and G: "G N"
      and fresh: "fresh_H i G"
      and satG: "sat_hyp G A"
      and base: "sat (subst_F p i (pack_T T_ZERO 0)) A"
      and step: "\<And>C. sat_hyp (pack_F F_EQ \<langle>pack_T T_VAR i, pack_T T_VAR i\<rangle> \<triangleright> p \<triangleright> G) C
                  \<Longrightarrow> sat (subst_F p i (pack_T T_SUC (pack_T T_VAR i))) C"
      and an: "eval a A N"
      and AN: "A N"
  shows "sat (subst_F p i a) A"
proof -
  let ?z = "pack_T T_ZERO 0"
  let ?vi = "pack_T T_VAR i"
  let ?svi = "pack_T T_SUC ?vi"
  have zN: "?z N"
    by (rule pack_T_N[OF _ nat0], simp)
  have viN: "?vi N"
    by (rule pack_T_N[OF _ i], simp)
  have sviN: "?svi N"
    by (rule pack_T_N[OF _ viN], simp)
  have main: "\<And>n. n N \<Longrightarrow> sat p (asn_put A i n)"
  proof -
    fix n
    assume n: "n N"
    show "sat p (asn_put A i n)"
    proof (rule ind[OF n])
      have sub0: "sat (subst_F p i ?z) A \<longleftrightarrow> sat p (asn_put A i (eval ?z A))"
        by (rule sat_subst_F[OF p i zN])
      have sub0E: "sat (subst_F p i ?z) A \<longrightarrow> sat p (asn_put A i (eval ?z A))"
        using sub0
        by (rule iffE1)
      have p0: "sat p (asn_put A i (eval ?z A))"
        using sub0E base
        by (rule implE)
      have ez: "eval ?z A = 0"
        by (rule eval_zero)
      show "sat p (asn_put A i 0)"
        using ez p0 by (rule eqSubst[where Q="\<lambda>v. sat p (asn_put A i v)"])
    next
      fix m
      assume m: "m N"
         and IH: "sat p (asn_put A i m)"
      let ?Am = "asn_put A i m"
      have Gm: "sat_hyp G ?Am"
        using G i m fresh satG by (rule sat_hyp_put)
      have ev: "eval ?vi ?Am = m"
        by (rule eval_var_put[OF AN i m])
      have me: "m = eval ?vi ?Am"
        using ev by (rule eqSym)
      have evN: "eval ?vi ?Am N"
        using me m by (rule eqSubst[where Q="\<lambda>v. v N"])
      have vvN: "\<langle>?vi, ?vi\<rangle> N"
        using viN by simp
      have eqN: "pack_F F_EQ \<langle>?vi, ?vi\<rangle> N"
        by (rule pack_F_N[OF _ vvN], simp)
      have tgEq: "tag_F (pack_F F_EQ \<langle>?vi, ?vi\<rangle>) = F_EQ"
        by (rule tag_pack_F[OF _ vvN], simp)
      have ldEq: "load_F (pack_F F_EQ \<langle>?vi, ?vi\<rangle>) = \<langle>?vi, ?vi\<rangle>"
        by (rule load_pack_F[OF _ vvN], simp)
      have satvi: "sat (pack_F F_EQ \<langle>?vi, ?vi\<rangle>) ?Am"
        unfolding sat_def using tgEq ldEq viN evN by simp
      have pG: "sat_hyp (p \<triangleright> G) ?Am"
        using p G IH Gm by (rule sat_hyp_consI)
      have pGN: "p \<triangleright> G N"
        using p G by simp
      have stepG: "sat_hyp (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> p \<triangleright> G) ?Am"
        using eqN pGN satvi pG by (rule sat_hyp_consI)
      have ss: "sat (subst_F p i ?svi) ?Am"
        using stepG by (rule step)
      have subS: "sat (subst_F p i ?svi) ?Am \<longleftrightarrow> sat p (asn_put ?Am i (eval ?svi ?Am))"
        by (rule sat_subst_F[OF p i sviN])
      have subSE: "sat (subst_F p i ?svi) ?Am \<longrightarrow> sat p (asn_put ?Am i (eval ?svi ?Am))"
        using subS by (rule iffE1)
      have ps: "sat p (asn_put ?Am i (eval ?svi ?Am))"
        using subSE ss by (rule implE)
      have es0: "eval ?svi ?Am = S (eval ?vi ?Am)"
        using viN evN by (rule eval_suc)
      have sem: "S (eval ?vi ?Am) = S m"
        using ev by (rule sucCong)
      have es: "eval ?svi ?Am = S m"
        using es0 sem by (rule eq_trans)
      have ps': "sat p (asn_put ?Am i (S m))"
        using es ps by (rule eqSubst[where Q="\<lambda>v. sat p(asn_put (asn_put A i m) i v)"])
      have Sm: "S m N"
        by (rule natS[OF m])
      have ow: "asn_put ?Am i (S m) = asn_put A i (S m)"
        by (rule asn_put_overwrite[OF AN i m Sm])
      show "sat p (asn_put A i (S m))"
        using ow ps' by (rule eqSubst[where Q="\<lambda>C. sat p C"])
    qed
  qed
  have pa: "sat p (asn_put A i (eval a A))"
    using an by (rule main)
  have subA: "sat (subst_F p i a) A \<longleftrightarrow> sat p (asn_put A i (eval a A))"
    by (rule sat_subst_F[OF p i a])
  have subAE: "sat p (asn_put A i (eval a A)) \<longrightarrow> sat (subst_F p i a) A"
    using subA by (rule iffE2)
  show ?thesis
    using subAE pa by (rule implE)
qed

lemma nat_ind_sound_put:
  assumes p: "p N"
      and i: "i N"
      and a: "a N"
      and G: "G N"
      and fresh: "fresh_H i G"
      and satG: "sat_hyp G A"
      and base: "sat (subst_F p i (pack_T T_ZERO 0)) A"
      and step:
        "\<And>m. m N \<Longrightarrow> sat_hyp (pack_F F_EQ \<langle>pack_T T_VAR i, pack_T T_VAR i\<rangle> \<triangleright> p \<triangleright> G) (asn_put A i m) \<Longrightarrow>
          sat (subst_F p i (pack_T T_SUC (pack_T T_VAR i))) (asn_put A i m)"
      and an: "eval a A N"
      and AN: "A N"
  shows "sat (subst_F p i a) A"
proof -
  let ?z = "pack_T T_ZERO 0"
  let ?vi = "pack_T T_VAR i"
  let ?svi = "pack_T T_SUC ?vi"
  have zN: "?z N"
    by (rule pack_T_N[OF _ nat0], simp)
  have viN: "?vi N"
    by (rule pack_T_N[OF _ i], simp)
  have sviN: "?svi N"
    by (rule pack_T_N[OF _ viN], simp)
  have main: "\<And>n. n N \<Longrightarrow> sat p (asn_put A i n)"
  proof -
    fix n
    assume n: "n N"
    show "sat p (asn_put A i n)"
    proof (rule ind[OF n])
      have sub0:
        "sat (subst_F p i ?z) A \<longleftrightarrow>
         sat p (asn_put A i (eval ?z A))"
        by (rule sat_subst_F[OF p i zN])
      have sub0E:
        "sat (subst_F p i ?z) A \<longrightarrow>
         sat p (asn_put A i (eval ?z A))"
        using sub0 by (rule iffE1)
      have p0: "sat p (asn_put A i (eval ?z A))"
        using sub0E base by (rule implE)
      have ez: "eval ?z A = 0"
        by (rule eval_zero)
      show "sat p (asn_put A i 0)"
        using ez p0
        by (rule eqSubst[where Q="\<lambda>v. sat p (asn_put A i v)"])
    next
      fix m
      assume m: "m N"
         and IH: "sat p (asn_put A i m)"
      let ?Am = "asn_put A i m"
      have Gm: "sat_hyp G ?Am"
        using G i m fresh satG by (rule sat_hyp_put)
      have ev: "eval ?vi ?Am = m"
        by (rule eval_var_put[OF AN i m])
      have me: "m = eval ?vi ?Am"
        using ev by (rule eqSym)
      have evN: "eval ?vi ?Am N"
        using me m
        by (rule eqSubst[where Q="\<lambda>v. v N"])
      have vvN: "\<langle>?vi, ?vi\<rangle> N"
        using viN by simp
      have eqN: "pack_F F_EQ \<langle>?vi, ?vi\<rangle> N"
        by (rule pack_F_N[OF _ vvN], simp)
      have tgEq:
        "tag_F (pack_F F_EQ \<langle>?vi, ?vi\<rangle>) = F_EQ"
        by (rule tag_pack_F[OF _ vvN], simp)
      have ldEq:
        "load_F (pack_F F_EQ \<langle>?vi, ?vi\<rangle>) = \<langle>?vi, ?vi\<rangle>"
        by (rule load_pack_F[OF _ vvN], simp)
      have satvi:
        "sat (pack_F F_EQ \<langle>?vi, ?vi\<rangle>) ?Am"
        unfolding sat_def
        using tgEq ldEq viN evN by simp
      have pG: "sat_hyp (p \<triangleright> G) ?Am"
        using p G IH Gm by (rule sat_hyp_consI)
      have pGN: "p \<triangleright> G N"
        using p G by simp
      have stepG:
        "sat_hyp
          (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> p \<triangleright> G)
          ?Am"
        using eqN pGN satvi pG by (rule sat_hyp_consI)
      have ss: "sat (subst_F p i ?svi) ?Am"
        using m stepG by (rule step)
      have subS:
        "sat (subst_F p i ?svi) ?Am \<longleftrightarrow>
         sat p (asn_put ?Am i (eval ?svi ?Am))"
        by (rule sat_subst_F[OF p i sviN])
      have subSE:
        "sat (subst_F p i ?svi) ?Am \<longrightarrow>
         sat p (asn_put ?Am i (eval ?svi ?Am))"
        using subS by (rule iffE1)
      have ps:
        "sat p (asn_put ?Am i (eval ?svi ?Am))"
        using subSE ss by (rule implE)
      have es0:
        "eval ?svi ?Am = S (eval ?vi ?Am)"
        using viN evN by (rule eval_suc)
      have sem: "S (eval ?vi ?Am) = S m"
        using ev by (rule sucCong)
      have es: "eval ?svi ?Am = S m"
        using es0 sem by (rule eq_trans)
      have ps': "sat p (asn_put ?Am i (S m))"
        using es ps
        by (rule eqSubst[
          where Q="\<lambda>v. sat p (asn_put (asn_put A i m) i v)"])
      have Sm: "S m N"
        by (rule natS[OF m])
      have ow: "asn_put ?Am i (S m) = asn_put A i (S m)"
        by (rule asn_put_overwrite[OF AN i m Sm])
      show "sat p (asn_put A i (S m))"
        using ow ps'
        by (rule eqSubst[where Q="\<lambda>C. sat p C"])
    qed
  qed
  have pa: "sat p (asn_put A i (eval a A))"
    using an by (rule main)
  have subA: "sat (subst_F p i a) A \<longleftrightarrow> sat p (asn_put A i (eval a A))"
    by (rule sat_subst_F[OF p i a])
  have subAE:
    "sat p (asn_put A i (eval a A)) \<longrightarrow>
     sat (subst_F p i a) A"
    using subA by (rule iffE2)
  show ?thesis
    using subAE pa by (rule implE)
qed

end
===== end DEAD CODE (bga_subst_semantics) ===== *)

locale bga_subst_rule = bga_subst +

  fixes check_template :: "fm \<Rightarrow> fm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm \<Rightarrow> tm \<Rightarrow> o"
(* Counts down p from max_bound to 0. 
     i is fixed to a fresh variable (e.g., f+1)
  f - formula we are trying to see if valid
  phi - premise formula
  p - template formula
  i - id of variable acting as a place holder in p
  a=b - equality being considered
 *)
  assumes check_template_def: "check_template f phi a b p i :=
    if subst_F p i a = phi \<and> subst_F p i b = f then True
    else if p > 0 = 1 then check_template f phi a b (p - 1) i
    else False"

  fixes rep_vars_T     :: "tm \<Rightarrow> tm \<Rightarrow> tm"
(* rep_vars_T t i: Replaces all leaves in term t with variable i *)
  assumes rep_vars_T_def: "rep_vars_T t i :=
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
                rep_vars_T (cpy (cpy (load_T t))) i\<rangle>\<rangle>"

  fixes rep_vars_F     :: "fm \<Rightarrow> tm \<Rightarrow> fm"
  (* rep_vars_F f i: Replaces all leaves in formula f with variable i *)
  assumes rep_vars_F_def: "rep_vars_F f i :=
    if tag_F f = F_EQ then
      pack_F F_EQ \<langle>rep_vars_T (cpx (load_F f)) i, rep_vars_T (cpy (load_F f)) i\<rangle>
    else
      pack_F F_NEQ \<langle>rep_vars_T (cpx (load_F f)) i, rep_vars_T (cpy (load_F f)) i\<rangle>"

(* unconditional version:
  assumes find_phi_def: "find_phi f a b ptr :=
    if ptr = 0 then False
    else if check_template f (cpx ptr) a b (rep_vars_F f (f+1)) (f + 1) then True
    else find_phi f a b (cpy ptr)"
*)

  fixes find_phi       :: "jdg \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> o"
(* Scans the proof list (ptr) for a valid premise J_phi = \<langle>\<Gamma>, \<phi>\<rangle>
   such that \<Gamma> matches J's context, and p[v_(f+1) \<mapsto> a] = \<phi> and p[v_(f+1) \<mapsto> b] = f *)
  assumes find_phi_def: "find_phi J a b ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J \<and> 
            check_template (conc_of J) (conc_of (list_hd ptr)) a b 
                           (rep_vars_F (conc_of J) (J + 1)) (J + 1) then True
    else find_phi J a b (list_tl ptr)"

(*unconditional version:
  assumes find_eq_def: "find_eq f rest ptr :=
    if ptr = 0 then False
    else if tag_F (cpx ptr) = 0 then
      if find_phi f (cpx (load_F (cpx ptr))) (cpy (load_F (cpx ptr))) rest then True
      else find_eq f rest (cpy ptr)
    else find_eq f rest (cpy ptr)"
*)

  fixes find_eq        :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
(* Scans the proof list (ptr) for an equality judgment J_eq = \<langle>\<Gamma>, a = b\<rangle>
   such that \<Gamma> matches J's context, and calls find_phi *)
  assumes find_eq_def: "find_eq J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J \<and> tag_F (conc_of (list_hd ptr)) = F_EQ then
      if find_phi J (cpx (load_F (conc_of (list_hd ptr)))) (cpy (load_F (conc_of (list_hd ptr)))) rest then True
      else find_eq J rest (list_tl ptr)
    else find_eq J rest (list_tl ptr)"
  fixes check_subst    :: "jdg \<Rightarrow> pf \<Rightarrow> o"

(* checking the substitution rule *)
assumes check_subst_def: "check_subst J rest := find_eq J rest rest"

locale bga_eq_rule = bga_bijective_encoding +

(*
f - formula we are trying to append to the proof
rest - rest of the proof
Proof Rules:
1. f \<turnstile> f 
2. a=b, p[x=a] \<turnstile> p[x=b]
3. \<turnstile> 0 = 0
4. a=b \<turnstile> b=a
5. a=b \<turnstile> S(a) = S(b)
6. S(a)=S(b) \<turnstile> a=b
7. a=a \<turnstile> P(S(a))=a
8. b=b, c\<noteq>0 \<turnstile> (c 0? a: b) = b
9. a=a, c=0 \<turnstile> (c 0? a: b) = a
10. a\<noteq>b \<turnstile> b\<noteq>a
11. a=a \<turnstile> S(a)\<noteq>0
12. a\<noteq>b \<turnstile> S(a)\<noteq>S(b)

*)

  fixes check_eq_rules  :: "hyp \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tmtag \<Rightarrow> tmtag \<Rightarrow> pf \<Rightarrow> o"
(* Equality Rules
1. \<Gamma> \<turnstile> 0 N
2. \<Gamma> \<turnstile> a=b \<Longrightarrow> \<Gamma> \<turnstile> b=a
3. \<Gamma> \<turnstile> a=b \<Longrightarrow> \<Gamma> \<turnstile> S(a)=S(b)
4. \<Gamma> \<turnstile> S(a)=S(b) \<Longrightarrow> \<Gamma> \<turnstile> a=b
5. \<Gamma> \<turnstile> a N \<Longrightarrow> \<Gamma> \<turnstile> P(S(a))=a
6. \<Gamma> \<turnstile> c\<noteq>0 \<Longrightarrow> \<Gamma> \<turnstile> b N \<Longrightarrow> \<Gamma> \<turnstile> (c 0? a: b)=b
7. \<Gamma> \<turnstile> c=0 \<Longrightarrow> \<Gamma> \<turnstile> a N \<Longrightarrow> \<Gamma> \<turnstile> (c 0? a: b)=a
*)
  assumes check_eq_rules_def: "check_eq_rules G lhs rhs tg_L tg_R rest :=
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
    else False"

  fixes check_neq_rules :: "hyp \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tmtag \<Rightarrow> tmtag \<Rightarrow> pf \<Rightarrow> o"
(* Not-Equality Rules
1. \<Gamma> \<turnstile> a\<noteq>b \<Longrightarrow> \<Gamma> \<turnstile> b\<noteq>a
2. \<Gamma> \<turnstile> a N \<Longrightarrow> \<Gamma> \<turnstile> S(a)\<noteq>0
3. \<Gamma> \<turnstile> a\<noteq>b \<Longrightarrow> \<Gamma> \<turnstile> S(a)\<noteq>S(b)
4. \<Gamma> \<turnstile> S(a)\<noteq>S(b) \<Longrightarrow> \<Gamma> \<turnstile> a\<noteq>b
*)
  assumes check_neq_rules_def: "check_neq_rules G lhs rhs tg_L tg_R rest :=
    if mem (G \<tturnstile> pack_F F_NEQ \<langle>rhs, lhs\<rangle>) rest then True
    else if tg_L = T_SUC \<and> rhs = pack_T T_ZERO 0 \<and> 
            mem (G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T lhs\<rangle>) rest then True
    else if tg_L = T_SUC \<and> tg_R = T_SUC \<and> 
            mem (G \<tturnstile> pack_F F_NEQ \<langle>load_T lhs, load_T rhs\<rangle>) rest then True
    else if mem (G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle>) rest then True
    else False"

locale bga_ind_rule = bga_subst_rule+

fixes check_ind_template :: "fm \<Rightarrow> fm \<Rightarrow> tm \<Rightarrow> hyp \<Rightarrow> fm \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> o"
(*counts down 'p', testing if it is the valid induction template 
checks for a p such that:
p[v_i \<rightarrow> a] = \<phi>
\<Gamma> \<turnstile> p[v_i \<rightarrow> 0] in proof
[v_i = v_i, p]+\<Gamma> \<turnstile> p[v_i \<rightarrow> S(v_i)] in proof

*)
  assumes check_ind_template_def: "check_ind_template f phi a G p i rest :=
    if subst_F p i a = f \<and> 
       subst_F p i (pack_T T_ZERO 0) = phi \<and>
       mem (pack_F F_EQ \<langle>pack_T T_VAR i, pack_T T_VAR i\<rangle> \<triangleright> p \<triangleright> G \<tturnstile> 
                subst_F p i (pack_T T_SUC (pack_T T_VAR i))) rest
    then True
    else if p > 0 = 1 then check_ind_template f phi a G (p - 1) i rest
    else False"

  fixes find_ind_base   :: "jdg \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
(*scans the proof list for the base case judgment.
J - \<Gamma> \<turnstile> \<phi>

we check if there exists a term of the form p such that 
p[v_i \<rightarrow> a] = \<phi> and
\<Gamma> \<turnstile> p[v_i \<rightarrow> 0] is in the proof list
[v_i = v_i, p]+\<Gamma> \<turnstile> p[v_i \<rightarrow> S(v_i)] in proof

we do this by going over each judgement in the proof list and looking at its conclusion (\<psi>).
we choose i such that v_i is guaranteed to not be used in \<phi> or \<Gamma> (maybe used in \<psi> or its context,
but that doesn't matter). then we pick an upperbound such that if such a p exists it must fall within it.

*)
assumes find_ind_base_def: "find_ind_base J a rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J then
      if check_ind_template (conc_of J) (conc_of (list_hd ptr)) a (hyp_of J) 
                            (rep_vars_F (conc_of J) (J + 1)) (J + 1) rest
      then True
      else find_ind_base J a rest (list_tl ptr)
    else find_ind_base J a rest (list_tl ptr)"

  fixes check_ind       :: "jdg \<Rightarrow> pf \<Rightarrow> o"
  (* check_ind triggers the search if the Habeas Quid premise \<Gamma> \<turnstile> a N (encoded as a=a) exists *)
  assumes check_ind_def: "check_ind J rest :=
    if fresh_H (J + 1) (hyp_of J) \<and> mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest then
       find_ind_base J (cpx (load_F (conc_of J))) rest rest
    else False"

locale bga_struct_rule = bga_bijective_encoding +


fixes find_cut    :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
fixes check_cut   :: "jdg \<Rightarrow> pf \<Rightarrow> o"

  (* Cut Rule:
  \<Gamma> \<turnstile> a \<Longrightarrow> a + \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> c
  *)
  assumes find_cut_def: "find_cut J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J then
      if mem ((conc_of (list_hd ptr)) \<triangleright> (hyp_of J) \<tturnstile> (conc_of J)) rest then True
      else find_cut J rest (list_tl ptr)
    else find_cut J rest (list_tl ptr)"

  assumes check_cut_def: "check_cut J rest := find_cut J rest rest"

  fixes find_struct :: "jdg \<Rightarrow> hyp \<Rightarrow> pf \<Rightarrow> o"
  assumes find_struct_def: "find_struct J G ptr :=
    if ptr = Nil then False
    else if conc_of (list_hd ptr) = conc_of J \<and> subset (hyp_of (list_hd ptr)) G then True
    else find_struct J G (list_tl ptr)"

  fixes check_struct :: "jdg \<Rightarrow> pf \<Rightarrow> o"
  assumes check_struct_def: "check_struct J rest := find_struct J (hyp_of J) rest"

locale bga_app_rule = bga_subst_rule + bga_dfns + 

(*
J d x y
let J = \<Gamma> \<turnstile> f
checks if
1. \<Gamma> \<turnstile> x=x & \<Gamma> \<turnstile> y=y in proof
2. \<Gamma> \<turnstile> f [d(x,y) \<rightarrow> D_d\<langle>x, y\<rangle>] in proof
*)
fixes app_try :: "jdg \<Rightarrow> num \<Rightarrow> num \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"
  assumes app_try_def: "app_try J d x y rest :=
    dfn_is d 2 (nth d dfns) \<and>
    mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) rest \<and> 
    mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) rest \<and>  
    find_phi J (subst_body (nth d dfns) x y) (pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>) rest"

(* Tries to see if application is satisfied for some y*)
fixes app_y :: "jdg \<Rightarrow> num \<Rightarrow> num \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"
  assumes app_y_def: "app_y J d x y rest :=
    if app_try J d x y rest then True
    else if y > 0 = 1 then app_y J d x (y - 1) rest
    else False"

(* Tries to see if application is satisfied for some x, y with y bounded by f (where J= \<Gamma>\<turnstile>f) *)
  fixes app_x :: "jdg \<Rightarrow> num \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"
  assumes app_x_def: "app_x J d x rest :=
    if app_y J d x (conc_of J) rest then True
    else if x > 0 = 1 then app_x J d (x - 1) rest
    else False"

(*Given a J and an upperbound for def, sees if application can be satisfied by any d,x,y triplet *)
  fixes app_d :: "jdg \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"
  assumes app_d_def: "app_d J d rest :=
    if d < len dfns = 1 then
      (if app_x J d (conc_of J) rest then True
       else if d > 0 = 1 then app_d J (d - 1) rest else False)
    else
      (if d > 0 = 1 then app_d J (d - 1) rest else False)"

  fixes check_app :: "jdg \<Rightarrow> pf \<Rightarrow> o"
  assumes check_app_def: "check_app J rest := app_d J (len dfns - 1) rest"

locale bga_proof_check = bga_subst_rule+ bga_eq_rule+ bga_ind_rule + bga_struct_rule + bga_app_rule+
(*checks if a judgement can be appended to the proof*)
fixes valid_step :: "jdg \<Rightarrow> pf \<Rightarrow> o"

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
(* unconditional version

assumes valid_step_def: "valid_step f rest := 
    if mem f rest then True
    
    else if check_subst f rest then True

    else if tag_F f = F_EQ then
      if cpx (load_F f) = (pack_T T_ZERO 0) \<and> cpy (load_F f) = (pack_T T_ZERO 0) then True
      else if list_in (pack_F F_EQ \<langle>cpy (load_F f), cpx (load_F f)\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = T_SUC \<and> tag_T (cpy (load_F f)) = T_SUC \<and> 
              list_in (pack_F F_EQ \<langle>load_T (cpx (load_F f)), load_T (cpy (load_F f))\<rangle>) rest then True
      else if list_in (pack_F F_EQ \<langle>(pack_T T_SUC (cpx (load_F f))), (pack_T T_SUC (cpy (load_F f)))\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = T_PRED \<and> tag_T (load_T (cpx (load_F f))) = T_SUC \<and> 
              cpx (load_T (load_T (cpx (load_F f)))) = cpy (load_F f) \<and> 
              list_in (pack_F F_EQ \<langle>cpy (load_F f), cpy (load_F f)\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = T_IFZ \<and> 
              cpy (load_F f) = cpy (cpy (load_T (cpx (load_F f)))) \<and> 
              list_in (pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F f))), pack_T T_ZERO 0\<rangle>) rest \<and>
              list_in (pack_F F_EQ \<langle>cpy (load_F f), cpy (load_F f)\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = T_IFZ \<and> 
              cpy (load_F f) = cpx (cpy (load_T (cpx (load_F f)))) \<and> 
              list_in (pack_F F_EQ \<langle>cpx (load_T (cpx (load_F f))), pack_T T_ZERO 0\<rangle>) rest \<and>
              list_in (pack_F F_EQ \<langle>cpy (load_F f), cpy (load_F f)\<rangle>) rest then True
      else False
    else
      if list_in (pack_F F_NEQ \<langle>cpy (load_F f), cpx (load_F f)\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = T_SUC \<and> cpy (load_F f) = (pack_T T_ZERO 0) \<and> 
              list_in (pack_F F_EQ \<langle>load_T (cpx (load_F f)), load_T (cpx (load_F f))\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = T_SUC \<and> tag_T (cpy (load_F f)) = T_SUC \<and> 
              list_in (pack_F F_EQ \<langle>load_T (cpx (load_F f)), load_T (cpy (load_F f))\<rangle>) rest then True
      else if list_in (pack_F F_EQ \<langle>(pack_T T_SUC (cpx (load_F f))), (pack_T T_SUC (cpy (load_F f)))\<rangle>) rest then True
      else False"
*)

(* Checks if the given head of proof is valid*)
fixes check_list :: "pf \<Rightarrow> o"
assumes check_list_def: "check_list pf := 
    if pf = Nil then True
    else if valid_step (list_hd pf) (list_tl pf) then check_list (list_tl pf)
    else False"

(*checks if the given proof is valid for the given judgement*)
fixes is_valid_proof :: "pf \<Rightarrow> jdg \<Rightarrow> o"

assumes is_valid_proof_def: "is_valid_proof pf J := 
    if pf = Nil then False
    else if list_hd pf = J then check_list pf
    else False"

(* ===== DEAD CODE: superseded by bga_fuller.
   Contained the old functional-eval soundness (check_app_sound left)
   and the old `sublocale consistent` interpretation. Commented out;
   nothing live depends on it, and bijective_enc now interprets bga_fuller. =====
locale bga_full = bga_subst_semantics + bga_proof_check
begin

definition mk_eq :: "num \<Rightarrow> num \<Rightarrow> num" where
    "mk_eq a b \<equiv> pack_F 0 \<langle>a, b\<rangle>"

definition mk_neq :: "num \<Rightarrow> num \<Rightarrow> num" where
    "mk_neq a b \<equiv> pack_F 1 \<langle>a, b\<rangle>"


lemma mk_eq_N':
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  shows "mk_eq a b N"
  unfolding mk_eq_def  apply (rule pack_F_N)
  using a_nat b_nat  apply simp+
  done

lemma mk_neq_N':
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  shows "mk_neq a b N"
  unfolding mk_neq_def  apply (rule pack_F_N)
  using a_nat b_nat  apply simp+
  done

lemma sat_eqE': "a N \<Longrightarrow> b N \<Longrightarrow> sat (mk_eq a b) A \<Longrightarrow> eval a A = eval b A"
proof -
  assume a: "a N" and b: "b N" and h: "sat (mk_eq a b) A"
  have p: "\<langle>a, b\<rangle> N" using a b by simp
  have tg: "tag_F (mk_eq a b) = F_EQ"
    unfolding mk_eq_def apply (rule tag_pack_F)
    using a b apply simp+
    done
  have ld: "load_F (mk_eq a b) = \<langle>a, b\<rangle>"
    unfolding mk_eq_def apply (rule load_pack_F)
    using a b apply simp+
    done
  from h[unfolded sat_def] show "eval a A = eval b A"
  proof -
  have step: "eval (hyp_of (load_F (mk_eq a b))) A
            = eval (conc_of (load_F (mk_eq a b))) A"
    by (rule cond_thenE[OF tg h[unfolded sat_def]])
  from step show "eval a A = eval b A"
    using a b apply (simp add: ld)
    apply (rule eq_impl_term2)
    apply simp
    done
qed
qed

lemma subst_T_N:
  assumes t: "t N" and j: "j N" and v: "v N"
  shows "subst_T t j v N"
proof (rule strong_induction[where a=t])
  show "t N" by (rule t)
next
  show "subst_T 0 j v N"
      proof -
    have zN: "pack_T T_ZERO 0 N"
      apply (rule pack_T_N) 
       apply simp 
      done
    have g1: "\<not> (tag_T 0 = T_VAR)" 
      by (simp add: tag_T_zero)
    have g2: "tag_T 0 = T_ZERO"     
      by (rule tag_T_zero)
    have red: "subst_T 0 j v = pack_T T_ZERO 0"
      apply (rule defE[OF subst_T_def[where t=0 and j=j and v=v]])
      apply (rule condI2Eq[OF g1 zN])
      apply (rule condI1Eq[OF g2 zN])
      using zN apply simp
      done
    show "subst_T 0 j v N" using red zN by simp
  qed
next
  fix x assume x: "x N" and IH: "\<And>y. y N \<Longrightarrow> y \<le> x = 1 \<Longrightarrow> subst_T y j v N"
  have sxN:  "S x N"          
    by (rule natS[OF x])
  have sxnz: "S x \<noteq> 0"        
    by (rule sucNonZero[OF x])
  have L:    "load_T (S x) N" 
    by (rule load_T_N[OF sxN])
  have Lx:   "load_T (S x) \<le> x = 1"
    by (rule le_suc_implies_leq[OF decrease_T[OF sxN sxnz] L x])
  have cxL:  "cpx (load_T (S x)) N" 
    by (rule cpx_terminates[OF L])
  have cyL:  "cpy (load_T (S x)) N" 
    by (rule cpy_terminates[OF L])
  have cxLx: "cpx (load_T (S x)) \<le> x = 1"
    by (rule leq_trans[OF cxL L x cpx_mono[OF L] Lx])
  have cyLx: "cpy (load_T (S x)) \<le> x = 1"
    by (rule leq_trans[OF cyL L x cpy_mono[OF L] Lx])
  have cxcyL: "cpx (cpy (load_T (S x))) N" 
    by (rule cpx_terminates[OF cyL])
  have cycyL: "cpy (cpy (load_T (S x))) N" 
    by (rule cpy_terminates[OF cyL])
  have cxcyLx: "cpx (cpy (load_T (S x))) \<le> x = 1"
    by (rule leq_trans[OF cxcyL cyL x cpx_mono[OF cyL] cyLx])
  have cycyLx: "cpy (cpy (load_T (S x))) \<le> x = 1"
    by (rule leq_trans[OF cycyL cyL x cpy_mono[OF cyL] cyLx])
  have r0: "subst_T (load_T (S x)) j v N"             
    by (rule IH[OF L Lx])
  have r1: "subst_T (cpx (load_T (S x))) j v N"       
    by (rule IH[OF cxL cxLx])
  have r2: "subst_T (cpx (cpy (load_T (S x)))) j v N" 
    by (rule IH[OF cxcyL cxcyLx])
  have r3: "subst_T (cpy (cpy (load_T (S x)))) j v N" 
    by (rule IH[OF cycyL cycyLx])  
    (* guards *)
  have tgN:   "tag_T (S x) N"             
    by (rule tag_T_N[OF sxN])
  have gVAR:  "(tag_T (S x) = T_VAR) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gZERO: "(tag_T (S x) = T_ZERO) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gSUC:  "(tag_T (S x) = T_SUC) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gPRED: "(tag_T (S x) = T_PRED) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gIFZ:  "(tag_T (S x) = T_IFZ) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  (* the six branches are all N *)
  have A1N: "(if load_T (S x) = j then v else S x) N"
    apply (rule condT[OF _ v sxN]) 
    apply (rule eqBool[OF L j]) 
    done
  have A2N: "pack_T T_ZERO 0 N"
    apply (rule pack_T_N) 
     apply simp 
    done
  have A3N: "pack_T T_SUC (subst_T (load_T (S x)) j v) N"
    apply (rule pack_T_N)
     apply simp
    apply (rule r0) 
    done
  have A4N: "pack_T T_PRED (subst_T (load_T (S x)) j v) N"
    apply (rule pack_T_N)
     apply simp
    apply (rule r0)
    done
  have iffN: "\<langle>subst_T (cpx (load_T (S x))) j v,
               \<langle>subst_T (cpx (cpy (load_T (S x)))) j v,
                subst_T (cpy (cpy (load_T (S x)))) j v\<rangle>\<rangle> N"
    using r1 r2 r3
    by simp
  have A5N: "pack_T T_IFZ \<langle>subst_T (cpx (load_T (S x))) j v,
               \<langle>subst_T (cpx (cpy (load_T (S x)))) j v,
                subst_T (cpy (cpy (load_T (S x)))) j v\<rangle>\<rangle> N"
    apply (rule pack_T_N)
    apply simp
    apply (rule r1)
    apply (rule r2)
    apply (rule r3)
    done

  have A6N: "pack_T T_APP \<langle>cpx (load_T (S x)),
               \<langle>subst_T (cpx (cpy (load_T (S x)))) j v,
                subst_T (cpy (cpy (load_T (S x)))) j v\<rangle>\<rangle> N"
    apply (rule pack_T_N)
     apply simp
    apply (rule L)
    apply (rule r2)
    apply (rule r3)
    done

  show "subst_T (S x) j v N"
    apply (rule defE[OF subst_T_def[where t="S x" and j=j and v=v]])
    apply (rule condT[OF gVAR A1N])
    apply (rule condT[OF gZERO A2N])
    apply (rule condT[OF gSUC A3N])
    apply (rule condT[OF gPRED A4N])
    apply (rule condT[OF gIFZ A5N])
    apply (rule A6N)
    done
qed

lemma subst_body_N:
  assumes b: "b N" and xa: "x N" and ya: "y N"
  shows "subst_body b x y N"
proof (rule strong_induction[where a=b])
  show "b N"
    by (rule b)
next
  show "subst_body 0 x y N"
    by (rule defE[OF subst_body_def[where b=0 and x=x and y=y]],
        simp add: tag_T_zero)
next
  fix w assume w: "w N" and IH: "\<And>z. z N \<Longrightarrow> z \<le> w = 1 \<Longrightarrow> subst_body z x y N"
  have swN:  "S w N"          using w
    by simp
  have swnz: "S w \<noteq> 0"       
    by (rule sucNonZero[OF w])
  have L:    "load_T (S w) N"
    by (rule load_T_N[OF swN])
  have Lw:   "load_T (S w) \<le> w = 1"
    by (rule le_suc_implies_leq[OF decrease_T[OF swN swnz] L w])
  have cxL: "cpx (load_T (S w)) N" using L
    by simp
  have cyL: "cpy (load_T (S w)) N" using L
    by simp
  have cxLw: "cpx (load_T (S w)) \<le> w = 1"
    by (rule leq_trans[OF cxL L w cpx_mono[OF L] Lw])
  have cyLw: "cpy (load_T (S w)) \<le> w = 1"
    by (rule leq_trans[OF cyL L w cpy_mono[OF L] Lw])
  have cxcyL: "cpx (cpy (load_T (S w))) N" using cyL
    by simp
  have cycyL: "cpy (cpy (load_T (S w))) N" using cyL
    by simp
  have cxcyLw: "cpx (cpy (load_T (S w))) \<le> w = 1"
    by (rule leq_trans[OF cxcyL cyL w cpx_mono[OF cyL] cyLw])
  have cycyLw: "cpy (cpy (load_T (S w))) \<le> w = 1"
    by (rule leq_trans[OF cycyL cyL w cpy_mono[OF cyL] cyLw])
  have r0: "subst_body (load_T (S w)) x y N"           
    by (rule IH[OF L Lw])
  have r1: "subst_body (cpx (load_T (S w))) x y N"     
    by (rule IH[OF cxL cxLw])
  have r2: "subst_body (cpx (cpy (load_T (S w)))) x y N"
    by (rule IH[OF cxcyL cxcyLw])
  have r3: "subst_body (cpy (cpy (load_T (S w)))) x y N"
    by (rule IH[OF cycyL cycyLw])
  have tgN:   "tag_T (S w) N"            
    by (rule tag_T_N[OF swN])
  have gVAR:  "(tag_T (S w) = T_VAR) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gZERO: "(tag_T (S w) = T_ZERO) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gSUC:  "(tag_T (S w) = T_SUC) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gPRED: "(tag_T (S w) = T_PRED) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gIFZ:  "(tag_T (S w) = T_IFZ) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  
  have ldN: "load_T (S w) N" by (rule L)
  have gL0: "(load_T (S w) = 0) B" 
    apply (rule eqBool[OF ldN]) 
    apply simp 
    done
  have gL1: "(load_T (S w) = 1) B" 
    apply (rule eqBool[OF ldN]) 
    apply simp 
    done
  
  have A1N: "(if load_T (S w) = 0 then x else if load_T (S w) = 1 then y else S w) N"
    apply (rule condT[OF gL0 xa])
    apply (rule condT[OF gL1 ya swN])
    done
  have A2N: "S w N" 
    by (rule swN)
  
  have A3N: "pack_T T_SUC (subst_body (load_T (S w)) x y) N"
    apply (rule pack_T_N) 
     apply simp 
    apply (rule r0) 
    done
    
  have A4N: "pack_T T_PRED (subst_body (load_T (S w)) x y) N"
    apply (rule pack_T_N) 
     apply simp 
    apply (rule r0) 
    done
    
  have iffN: "\<langle>subst_body (cpx (load_T (S w))) x y,
               \<langle>subst_body (cpx (cpy (load_T (S w)))) x y,
                subst_body (cpy (cpy (load_T (S w)))) x y\<rangle>\<rangle> N"
    using r1 r2 r3 by simp

  have A5N: "pack_T T_IFZ \<langle>subst_body (cpx (load_T (S w))) x y,
               \<langle>subst_body (cpx (cpy (load_T (S w)))) x y,
                subst_body (cpy (cpy (load_T (S w)))) x y\<rangle>\<rangle> N"
    apply (rule pack_T_N)
    apply simp
    apply (rule r1)
    apply (rule r2)
    apply (rule r3)
    done

  have A6N: "pack_T T_APP \<langle>cpx (load_T (S w)),
               \<langle>subst_body (cpx (cpy (load_T (S w)))) x y,
                subst_body (cpy (cpy (load_T (S w)))) x y\<rangle>\<rangle> N"
    apply (rule pack_T_N)
    apply simp
    apply (rule L)
    apply (rule r2)
    apply (rule r3)
    done

  show "subst_body (S w) x y N"
    apply (rule defE[OF subst_body_def[where b="S w" and x=x and y=y]])
    apply (rule condT[OF gVAR A1N])
    apply (rule condT[OF gZERO A2N])
    apply (rule condT[OF gSUC A3N])
    apply (rule condT[OF gPRED A4N])
    apply (rule condT[OF gIFZ A5N])
    apply (rule A6N)
    done
qed

lemma rep_vars_T_N:
  assumes t: "t N" and i: "i N"
  shows "rep_vars_T t i N"
proof (rule strong_induction[where a=t])
  show "t N" by (rule t)
next
  show "rep_vars_T 0 i N"
  proof -
    have pN: "pack_T T_VAR i N"
      apply (rule pack_T_N) 
       apply simp 
      apply (rule i) 
      done
    have g1: "\<not> (tag_T 0 = T_VAR)" 
      by (simp add: tag_T_zero)
    have g2: "tag_T 0 = T_ZERO"    
      by (rule tag_T_zero)
    have red: "rep_vars_T 0 i = pack_T T_VAR i"
      apply (rule defE[OF rep_vars_T_def[where t=0 and i=i]])
      apply (rule condI2Eq[OF g1 pN])
      apply (rule condI1Eq[OF g2 pN])
      using pN apply simp
      done
    show "rep_vars_T 0 i N" 
      using red pN by simp
  qed
next
  fix x assume x: "x N" and IH: "\<And>y. y N \<Longrightarrow> y \<le> x = 1 \<Longrightarrow> rep_vars_T y i N"
  
  have sxN:  "S x N"          
    by (rule natS[OF x])
  have sxnz: "S x \<noteq> 0"        
    by (rule sucNonZero[OF x])
  have L:    "load_T (S x) N" 
    by (rule load_T_N[OF sxN])
  
  have Lx:   "load_T (S x) \<le> x = 1"
    by (rule le_suc_implies_leq[OF decrease_T[OF sxN sxnz] L x])
    
  have cxL:  "cpx (load_T (S x)) N" 
    by (rule cpx_terminates[OF L])
  have cyL:  "cpy (load_T (S x)) N" 
    by (rule cpy_terminates[OF L])
  
  have cxLx: "cpx (load_T (S x)) \<le> x = 1"
    by (rule leq_trans[OF cxL L x cpx_mono[OF L] Lx])
  have cyLx: "cpy (load_T (S x)) \<le> x = 1"
    by (rule leq_trans[OF cyL L x cpy_mono[OF L] Lx])
    
  have cxcyL: "cpx (cpy (load_T (S x))) N" 
    by (rule cpx_terminates[OF cyL])
  have cycyL: "cpy (cpy (load_T (S x))) N" 
    by (rule cpy_terminates[OF cyL])
  
  have cxcyLx: "cpx (cpy (load_T (S x))) \<le> x = 1"
    by (rule leq_trans[OF cxcyL cyL x cpx_mono[OF cyL] cyLx])
  have cycyLx: "cpy (cpy (load_T (S x))) \<le> x = 1"
    by (rule leq_trans[OF cycyL cyL x cpy_mono[OF cyL] cyLx])
    
  have r0: "rep_vars_T (load_T (S x)) i N"             by (rule IH[OF L Lx])
  have r1: "rep_vars_T (cpx (load_T (S x))) i N"       by (rule IH[OF cxL cxLx])
  have r2: "rep_vars_T (cpx (cpy (load_T (S x)))) i N" by (rule IH[OF cxcyL cxcyLx])
  have r3: "rep_vars_T (cpy (cpy (load_T (S x)))) i N" by (rule IH[OF cycyL cycyLx])

  (* Guards *)
  have tgN:   "tag_T (S x) N"             
    by (rule tag_T_N[OF sxN])
  have gVAR:  "(tag_T (S x) = T_VAR) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gZERO: "(tag_T (S x) = T_ZERO) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gSUC:  "(tag_T (S x) = T_SUC) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gPRED: "(tag_T (S x) = T_PRED) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gIFZ:  "(tag_T (S x) = T_IFZ) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done

  (* Branches *)
  have A1N: "pack_T T_VAR i N"
    apply (rule pack_T_N) 
     apply simp
    apply (rule i) 
    done
  have A2N: "pack_T T_VAR i N" 
    by (rule A1N)
    
  have A3N: "pack_T T_SUC (rep_vars_T (load_T (S x)) i) N"
    apply (rule pack_T_N) 
     apply simp 
    apply (rule r0) 
    done
    
  have A4N: "pack_T T_PRED (rep_vars_T (load_T (S x)) i) N"
    apply (rule pack_T_N) 
     apply simp 
    apply (rule r0) 
    done
    
  have A5N: "pack_T T_IFZ \<langle>rep_vars_T (cpx (load_T (S x))) i, \<langle>rep_vars_T (cpx (cpy (load_T (S x)))) i, rep_vars_T (cpy (cpy (load_T (S x)))) i\<rangle>\<rangle> N"
    apply (rule pack_T_N)
    apply simp
    apply (rule r1)
    apply (rule r2)
    apply (rule r3)
    done
    
  have A6N: "pack_T T_APP \<langle>cpx (load_T (S x)), \<langle>rep_vars_T (cpx (cpy (load_T (S x)))) i, rep_vars_T (cpy (cpy (load_T (S x)))) i\<rangle>\<rangle> N"
    apply (rule pack_T_N)
    apply simp
    apply (rule L)
    apply (rule r2)
    apply (rule r3)
    done

  show "rep_vars_T (S x) i N"
    apply (rule defE[OF rep_vars_T_def[where t="S x" and i=i]])
    apply (rule condT[OF gVAR A1N])
    apply (rule condT[OF gZERO A2N])
    apply (rule condT[OF gSUC A3N])
    apply (rule condT[OF gPRED A4N])
    apply (rule condT[OF gIFZ A5N])
    apply (rule A6N)
    done
qed


lemma subst_F_N:
  assumes f: "f N" and j: "j N" and v: "v N"
  shows "subst_F f j v N"
proof -
  have Lf: "load_F f N" 
    by (rule load_F_N[OF f])
  have cx: "cpx (load_F f) N" 
    by (rule cpx_terminates[OF Lf])
  have cy: "cpy (load_F f) N" 
    by (rule cpy_terminates[OF Lf])
  
  have s_cx: "subst_T (cpx (load_F f)) j v N" 
    by (rule subst_T_N[OF cx j v])
  have s_cy: "subst_T (cpy (load_F f)) j v N" 
    by (rule subst_T_N[OF cy j v])
  
  have tgN: "tag_F f N" 
    by (rule tag_F_N[OF f])
  have gEQ: "(tag_F f = F_EQ) B" 
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  
  have A1N: "pack_F F_EQ \<langle>subst_T (cpx (load_F f)) j v, subst_T (cpy (load_F f)) j v\<rangle> N"
    apply (rule pack_F_N)
    apply simp
    apply (rule s_cx)
    apply (rule s_cy)
    done
    
  have A2N: "pack_F F_NEQ \<langle>subst_T (cpx (load_F f)) j v, subst_T (cpy (load_F f)) j v\<rangle> N"
    apply (rule pack_F_N)
    apply simp
    apply (rule s_cx)
    apply (rule s_cy)
    done

  show "subst_F f j v N"
    apply (rule defE[OF subst_F_def[where f=f and j=j and v=v]])
    apply (rule condT[OF gEQ A1N])
    apply (rule A2N)
    done
qed

lemma rep_vars_F_N:
  assumes f: "f N" and i: "i N"
  shows "rep_vars_F f i N"
proof -
  have Lf: "load_F f N" 
    by (rule load_F_N[OF f])
  have cx: "cpx (load_F f) N" 
    by (rule cpx_terminates[OF Lf])
  have cy: "cpy (load_F f) N" 
    by (rule cpy_terminates[OF Lf])
  
  have r_cx: "rep_vars_T (cpx (load_F f)) i N" 
    by (rule rep_vars_T_N[OF cx i])
  have r_cy: "rep_vars_T (cpy (load_F f)) i N" 
    by (rule rep_vars_T_N[OF cy i])
  
  have tgN: "tag_F f N" 
    by (rule tag_F_N[OF f])
  have gEQ: "(tag_F f = F_EQ) B" 
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  
  have A1N: "pack_F F_EQ \<langle>rep_vars_T (cpx (load_F f)) i, rep_vars_T (cpy (load_F f)) i\<rangle> N"
    apply (rule pack_F_N)
    apply simp
    apply (rule r_cx)
    apply (rule r_cy)
    done
    
  have A2N: "pack_F F_NEQ \<langle>rep_vars_T (cpx (load_F f)) i, rep_vars_T (cpy (load_F f)) i\<rangle> N"
    apply (rule pack_F_N)
    apply simp
    apply (rule r_cx)
    apply (rule r_cy)
    done

  show "rep_vars_F f i N"
    apply (rule defE[OF rep_vars_F_def[where f=f and i=i]])
    apply (rule condT[OF gEQ A1N])
    apply (rule A2N)
    done
qed

lemma check_template_bool [auto]:
  assumes f: "f N" and phi: "phi N" and a: "a N" and b: "b N" and i: "i N" and p: "p N"
  shows "check_template f phi a b p i B"
proof (rule ind[OF p])
  show "check_template f phi a b 0 i B"
    apply (rule defE[OF check_template_def[where p=0]], insert f phi a b i)
    apply simp
    apply (rule condTB[OF _ true_bool false_bool])
    using subst_F_N[OF nat0 i a] subst_F_N[OF nat0 i b] phi f by auto
next
  fix k assume k: "k N" and IH: "check_template f phi a b k i B"
  show "check_template f phi a b (S k) i B"
    apply (rule defE[OF check_template_def[where p="S k"]], insert f phi a b i k IH)
    apply simp
    apply (rule condTB[OF _ true_bool IH])
    using subst_F_N[OF natS[OF k] i a] subst_F_N[OF natS[OF k] i b] phi f by auto
qed

lemma find_phi_bool [auto]:
  assumes J: "J N" and a: "a N" and b: "b N" and ptr: "ptr N"
  shows "find_phi J a b ptr B"
proof (rule list_induct[OF ptr])
  show "find_phi J a b Nil B"
    apply (rule defE[OF find_phi_def[where J=J and a=a and b=b and ptr=Nil]])
    apply simp
    done
next
  fix h t assume h: "h N" and t: "t N" and IH: "find_phi J a b t B"
  show "find_phi J a b (Cons h t) B"
  proof -
    have htN: "h \<triangleright> t N" 
      using h t by simp
    have g1: "(h \<triangleright> t = \<emptyset>) B" 
      apply (rule eqBool[OF htN]) 
      apply simp 
      done

    have eq1: "(hyp_of h = hyp_of J) B" 
      using h J by simp
    
    have cy_J: "conc_of J N" 
      using J by simp
    have cy_h: "conc_of h N" 
      using h by simp
    have SJ: "S J N" 
      using J by simp
    
    have rep: "rep_vars_F (conc_of J) (S J) N" 
      by (rule rep_vars_F_N[OF cy_J SJ])
    
    have eq2: "check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (S J)) (S J) B"
      apply (rule check_template_bool)
      apply (rule cy_J)
      apply (rule cy_h)
      apply (rule a)
        apply (rule b)
      apply (rule SJ)
      apply (rule rep)
      done
      
    have g2: "(hyp_of h = hyp_of J \<and> check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (S J)) (S J)) B"
      using eq1 eq2 by simp

    show "find_phi J a b (h \<triangleright> t) B"
      apply (rule defE[OF find_phi_def[where J=J and a=a and b=b and ptr="h \<triangleright> t"]])
      apply (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t] one_plus_suc[OF J])
      apply (rule condTB[OF g1 false_bool])
      apply (rule condTB[OF g2 true_bool IH])
      done
  qed
qed

lemma app_try_bool [auto]:
  assumes J: "J N" and d: "d N" and x: "x N" and y: "y N" and r: "rest N"
      and dr: "d < len dfns = 1"
  shows "app_try J d x y rest B"
proof (rule defE[OF app_try_def[where J=J and d=d and x=x and y=y and rest=rest]])
  have hj:  "hyp_of J N"             
    using J by simp
  have xx:  "\<langle>x, x\<rangle> N"              
    using x by simp
  have yy:  "\<langle>y, y\<rangle> N"              
    using y by simp
  have pfx: "pack_F F_EQ \<langle>x, x\<rangle> N"  
    by (rule pack_F_N[OF _ xx], simp)
  have pfy: "pack_F F_EQ \<langle>y, y\<rangle> N"  
    by (rule pack_F_N[OF _ yy], simp)
  have jxx: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) N" 
    using hj pfx by simp
  have jyy: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) N" 
    using hj pfy by simp
  have ndf: "nth d dfns N"
    using dfns_N dr 
    apply (rule nth_in_range_N)
    done
  have di: "dfn_is d 2 (nth d dfns) B"
    by (rule dfn_is_bool[OF d _ ndf], simp)
  have sb:  "subst_body (nth d dfns) x y N" 
    by (rule subst_body_N[OF ndf x y])
  have dxy: "\<langle>d, \<langle>x, y\<rangle>\<rangle> N"                 
    using d x y by simp
  have pT:  "pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle> N"    
    by (rule pack_T_N[OF _ dxy], simp)
  have m1: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) rest B" 
    by (rule mem_bool[OF jxx r])
  have m2: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) rest B" 
    by (rule mem_bool[OF jyy r])
  have fp: "find_phi J (subst_body (nth d dfns) x y) (pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>) rest B"
           by (rule find_phi_bool[OF J sb pT r])
  show "dfn_is d T_SUC (nth d dfns) \<and> (hyp_of J \<tturnstile> pack_F F_EQ (x \<tturnstile> x)) \<in> rest \<and>
    (hyp_of J \<tturnstile> pack_F F_EQ (y \<tturnstile> y)) \<in> rest \<and> find_phi J (subst_body (nth d dfns) x y) (pack_T T_APP (d \<tturnstile> (x \<tturnstile> y))) rest B "
    using di m1 m2 fp by simp
qed

lemma sat_neqE': "a N \<Longrightarrow> b N \<Longrightarrow> sat (mk_neq a b) A \<Longrightarrow> eval a A \<noteq> eval b A"
proof -
  assume a: "a N" and b: "b N" and h: "sat (mk_neq a b) A"
  have p: "\<langle>a, b\<rangle> N" 
    using a b by simp
  have tg: "tag_F (mk_neq a b) = F_NEQ"
    unfolding mk_neq_def 
    apply (rule tag_pack_F)
    using a b apply simp+
    done
  have tg_ne: "\<not> (tag_F (mk_neq a b) = F_EQ)"
    using tg by simp
  have ld: "load_F (mk_neq a b) = \<langle>a, b\<rangle>"
    unfolding mk_neq_def 
    apply (rule load_pack_F)
    using a b apply simp+
    done
  have step: "eval (hyp_of (load_F (mk_neq a b))) A
            \<noteq> eval (conc_of (load_F (mk_neq a b))) A"
    by (rule notcond_thenE[OF tg_ne h[unfolded sat_def]])
  from step show "eval a A \<noteq> eval b A"
    using a b by (simp add: ld)
qed

lemma find_struct_bool [auto]:
  assumes J: "J N" and G: "G N" and ptr: "ptr N"
  shows "find_struct J G ptr B"
proof (rule list_induct[OF ptr])
  show "find_struct J G Nil B" by (rule defE[OF find_struct_def[where ptr=Nil]], simp)
next
  fix h t assume h: "h N" and t: "t N" and IH: "find_struct J G t B"
  show "find_struct J G (Cons h t) B"
    by (rule defE[OF find_struct_def[where ptr="Cons h t"]], insert J G h t IH, simp+)
qed

lemma find_cut_bool [auto]:
  assumes J: "J N" and rest: "rest N" and ptr: "ptr N"
  shows "find_cut J rest ptr B"
proof (rule list_induct[OF ptr])
  show "find_cut J rest Nil B"
    apply (rule defE[OF find_cut_def[where J=J and rest=rest and ptr=Nil]])
    apply simp
    done
next
  fix h t assume h: "h N" and t: "t N" and IH: "find_cut J rest t B"
  show "find_cut J rest (Cons h t) B"
  proof -
    have htN: "h \<triangleright> t N" 
      using h t by simp
    have g0: "(h \<triangleright> t = \<emptyset>) B" 
      apply (rule eqBool[OF htN]) 
      apply simp 
      done
    have g1: "(hyp_of h = hyp_of J) B" 
      using h J by simp
    have cc: "conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J N" 
      using h J by simp
    have m: "mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest B"
      by (rule mem_bool[OF cc rest])
    show "find_cut J rest (h \<triangleright> t) B"
      apply (rule defE[OF find_cut_def[where J=J and rest=rest and ptr="h \<triangleright> t"]])
      apply (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
      apply (rule condTB[OF g0 false_bool])
      apply (rule condTB[OF g1 _ IH])
      apply (rule condTB[OF m true_bool IH])
      done
  qed
qed

lemma check_cut_bool [auto]:
  assumes J: "J N" and rest: "rest N"
  shows "check_cut J rest B"
  apply (rule defE[OF check_cut_def[where J=J and rest=rest]])
  apply (rule find_cut_bool[OF J rest rest])
  done

lemma find_eq_bool [auto]:
  assumes J: "J N" and rest: "rest N" and ptr: "ptr N"
  shows "find_eq J rest ptr B"
proof (rule list_induct[OF ptr])
  show "find_eq J rest Nil B"
    apply (rule defE[OF find_eq_def[where J=J and rest=rest and ptr=Nil]])
    apply simp
    done
next
  fix h t assume h: "h N" and t: "t N" and IH: "find_eq J rest t B"
  show "find_eq J rest (Cons h t) B"
  proof -
    have htN: "h \<triangleright> t N" 
      using h t by simp
    have g0: "(h \<triangleright> t = \<emptyset>) B" 
      apply (rule eqBool[OF htN]) 
      apply simp 
      done
    have ch: "conc_of h N" 
      using h by simp
    have eqh: "(hyp_of h = hyp_of J) B" 
      using h J by simp
    have tgh: "tag_F (conc_of h) N" 
      by (rule tag_F_N[OF ch])
    have feqN: "F_EQ N" 
      by simp
    have eqtg: "(tag_F (conc_of h) = F_EQ) B" 
      by (rule eqBool[OF tgh feqN])
    have g1: "(hyp_of h = hyp_of J \<and> tag_F (conc_of h) = F_EQ) B"
      using eqh eqtg by simp

    have Lch: "load_F (conc_of h) N" 
      by (rule load_F_N[OF ch])
    have cxh: "cpx (load_F (conc_of h)) N" 
      by (rule cpx_terminates[OF Lch])
    have cyh: "cpy (load_F (conc_of h)) N" 
      by (rule cpy_terminates[OF Lch])
    have gphi: "find_phi J (cpx (load_F (conc_of h))) (cpy (load_F (conc_of h))) rest B"
      by (rule find_phi_bool[OF J cxh cyh rest])

    show "find_eq J rest (h \<triangleright> t) B"
      apply (rule defE[OF find_eq_def[where J=J and rest=rest and ptr="h \<triangleright> t"]])
      apply (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
      apply (rule condTB[OF g0 false_bool])
      apply (rule condTB[OF g1 _ IH])
      apply (rule condTB[OF gphi true_bool IH])
      done
  qed
qed

lemma check_subst_bool [auto]:
  assumes J: "J N" and rest: "rest N"
  shows "check_subst J rest B"
  apply (rule defE[OF check_subst_def[where J=J and rest=rest]])
  apply (rule find_eq_bool[OF J rest rest])
  done

lemma check_struct_bool [auto]:
  assumes J: "J N" and rest: "rest N"
  shows "check_struct J rest B"
proof -
  have hj: "hyp_of J N" 
    using J by simp
  show ?thesis
    apply (rule defE[OF check_struct_def[where J=J and rest=rest]])
    apply (rule find_struct_bool[OF J hj rest])
    done
qed

(* Habeas quid for the induction step judgment  *)
lemma ind_jdg_N:
  assumes p: "p N" and G: "G N" and i: "i N"
  shows "pack_F F_EQ \<langle>pack_T T_VAR i, pack_T T_VAR i\<rangle> \<triangleright> p \<triangleright> G \<tturnstile>
         subst_F p i (pack_T T_SUC (pack_T T_VAR i)) N"
proof -
  have vi: "pack_T T_VAR i N" 
    by (rule pack_T_N[OF _ i], simp)
  have vv: "\<langle>pack_T T_VAR i, pack_T T_VAR i\<rangle> N" 
    using vi by simp
  have feq: "pack_F F_EQ \<langle>pack_T T_VAR i, pack_T T_VAR i\<rangle> N" 
    by (rule pack_F_N[OF _ vv], simp)
  have sv: "pack_T T_SUC (pack_T T_VAR i) N" 
    by (rule pack_T_N[OF _ vi], simp)
  have cc: "subst_F p i (pack_T T_SUC (pack_T T_VAR i)) N" 
    by (rule subst_F_N[OF p i sv])
  show ?thesis 
    using feq p G cc by simp
qed

lemma check_eq_rules_bool [auto]:
  assumes G: "G N" and lhs: "lhs N" and rhs: "rhs N"
      and tg_L: "tg_L N" and tg_R: "tg_R N" and rest: "rest N"
  shows "check_eq_rules G lhs rhs tg_L tg_R rest B"
proof -
  have sucN: "T_SUC N" 
    by simp
  have predN: "T_PRED N" 
    by simp
  have ifzN: "T_IFZ N" 
    by simp
  have ztz: "pack_T T_ZERO 0 N" 
    by (rule pack_T_N[OF _ nat0], simp)
  have Ll: "load_T lhs N" 
    by (rule load_T_N[OF lhs])
  have Lr: "load_T rhs N" 
    by (rule load_T_N[OF rhs])
  have LLl: "load_T (load_T lhs) N" 
    by (rule load_T_N[OF Ll])
  have cxLLl: "cpx (load_T (load_T lhs)) N" 
    by (rule cpx_terminates[OF LLl])
  have cyLl: "cpy (load_T lhs) N" 
    by (rule cpy_terminates[OF Ll])
  have cycyLl: "cpy (cpy (load_T lhs)) N" 
    by (rule cpy_terminates[OF cyLl])
  have cxcyLl: "cpx (cpy (load_T lhs)) N" 
    by (rule cpx_terminates[OF cyLl])
  have cxLl: "cpx (load_T lhs) N" 
    by (rule cpx_terminates[OF Ll])
  have sucl: "pack_T T_SUC lhs N" 
    by (rule pack_T_N[OF _ lhs], simp)
  have sucr: "pack_T T_SUC rhs N" 
    by (rule pack_T_N[OF _ rhs], simp)
  have tgLL: "tag_T (load_T lhs) N" 
    by (rule tag_T_N[OF Ll])

  have e_lz: "(lhs = pack_T T_ZERO 0) B" 
    by (rule eqBool[OF lhs ztz])
  have e_rz: "(rhs = pack_T T_ZERO 0) B" 
    by (rule eqBool[OF rhs ztz])
  have g1: "(lhs = pack_T T_ZERO 0 \<and> rhs = pack_T T_ZERO 0) B" 
    using e_lz e_rz by auto

  have pr_rl: "\<langle>rhs, lhs\<rangle> N" 
    using rhs lhs by simp
  have pf2: "pack_F F_EQ \<langle>rhs, lhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_rl], simp)
  have j2: "(G \<tturnstile> pack_F F_EQ \<langle>rhs, lhs\<rangle>) N" 
    using G pf2 by simp
  have g2: "mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, lhs\<rangle>) rest B" 
    by (rule mem_bool[OF j2 rest])

  have pr_LlLr: "\<langle>load_T lhs, load_T rhs\<rangle> N" 
    using Ll Lr by simp
  have pf3: "pack_F F_EQ \<langle>load_T lhs, load_T rhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_LlLr], simp)
  have j3: "(G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T rhs\<rangle>) N" 
    using G pf3 by simp
  have m3: "mem (G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T rhs\<rangle>) rest B" 
    by (rule mem_bool[OF j3 rest])
  have e_tgLs: "(tg_L = T_SUC) B" 
    by (rule eqBool[OF tg_L sucN])
  have e_tgRs: "(tg_R = T_SUC) B" 
    by (rule eqBool[OF tg_R sucN])
  have g3: "(tg_L = T_SUC \<and> tg_R = T_SUC \<and>
             mem (G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T rhs\<rangle>) rest) B"
    using e_tgLs e_tgRs m3 by auto

  have pr_ss: "\<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle> N" 
    using sucl sucr by simp
  have pf4: "pack_F F_EQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_ss], simp)
  have j4: "(G \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle>) N" 
    using G pf4 by simp
  have g4: "mem (G \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle>) rest B"
    by (rule mem_bool[OF j4 rest])

  have pr_rr: "\<langle>rhs, rhs\<rangle> N" 
    using rhs by simp
  have pfrr: "pack_F F_EQ \<langle>rhs, rhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_rr], simp)
  have jrr: "(G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) N" 
    using G pfrr by simp
  have mrr: "mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) rest B" 
    by (rule mem_bool[OF jrr rest])

  have e_tgLp: "(tg_L = T_PRED) B" 
    by (rule eqBool[OF tg_L predN])
  have e_tgLLs: "(tag_T (load_T lhs) = T_SUC) B" 
    by (rule eqBool[OF tgLL sucN])
  have e_cx_r: "(load_T (load_T lhs) = rhs) B" 
    by (rule eqBool[OF LLl rhs])
  have g5: "(tg_L = T_PRED \<and> tag_T (load_T lhs) = T_SUC \<and>
             (load_T (load_T lhs)) = rhs \<and>
             mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) rest) B"
    using e_tgLp e_tgLLs e_cx_r mrr by auto

  have pr_cxZ: "\<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle> N" 
    using cxLl ztz by simp
  have pf_neq_cxZ: "pack_F F_NEQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle> N"
    by (rule pack_F_N[OF _ pr_cxZ], simp)
  have j_neq_cxZ: "(G \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) N"
    using G pf_neq_cxZ by simp
  have m6a: "mem (G \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) rest B"
    by (rule mem_bool[OF j_neq_cxZ rest])
  have pf_eq_cxZ: "pack_F F_EQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle> N"
    by (rule pack_F_N[OF _ pr_cxZ], simp)
  have j_eq_cxZ: "(G \<tturnstile> pack_F F_EQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) N"
    using G pf_eq_cxZ by simp
  have m7a: "mem (G \<tturnstile> pack_F F_EQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) rest B"
    by (rule mem_bool[OF j_eq_cxZ rest])

  have e_tgLi: "(tg_L = T_IFZ) B" 
    by (rule eqBool[OF tg_L ifzN])
  have e_r_cycy: "(rhs = cpy (cpy (load_T lhs))) B" 
    by (rule eqBool[OF rhs cycyLl])
  have g6: "(tg_L = T_IFZ \<and> rhs = cpy (cpy (load_T lhs)) \<and>
             mem (G \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) rest \<and>
             mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) rest) B"
    using e_tgLi e_r_cycy m6a mrr by auto

  have e_r_cxcy: "(rhs = cpx (cpy (load_T lhs))) B" 
    by (rule eqBool[OF rhs cxcyLl])
  have g7: "(tg_L = T_IFZ \<and> rhs = cpx (cpy (load_T lhs)) \<and>
             mem (G \<tturnstile> pack_F F_EQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) rest \<and>
             mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) rest) B"
    using e_tgLi e_r_cxcy m7a mrr by auto

  show ?thesis
    apply (rule defE[OF check_eq_rules_def[where G=G and lhs=lhs and rhs=rhs
                                             and tg_L=tg_L and tg_R=tg_R and rest=rest]])
    apply (rule condTB[OF g1 true_bool])
    apply (rule condTB[OF g2 true_bool])
    apply (rule condTB[OF g3 true_bool])
    apply (rule condTB[OF g4 true_bool])
    apply (rule condTB[OF g5 true_bool])
    apply (rule condTB[OF g6 true_bool])
    apply (rule condTB[OF g7 true_bool false_bool])
    done
qed

lemma check_neq_rules_bool [auto]:
  assumes G: "G N" and lhs: "lhs N" and rhs: "rhs N"
      and tg_L: "tg_L N" and tg_R: "tg_R N" and rest: "rest N"
  shows "check_neq_rules G lhs rhs tg_L tg_R rest B"
proof -
  have sucN: "T_SUC N" 
    by simp
  have ztz: "pack_T T_ZERO 0 N" 
    by (rule pack_T_N[OF _ nat0], simp)
  have Ll: "load_T lhs N" 
    by (rule load_T_N[OF lhs])
  have Lr: "load_T rhs N" 
    by (rule load_T_N[OF rhs])
  have sucl: "pack_T T_SUC lhs N" 
    by (rule pack_T_N[OF _ lhs], simp)
  have sucr: "pack_T T_SUC rhs N" 
    by (rule pack_T_N[OF _ rhs], simp)
  have pr_rl: "\<langle>rhs, lhs\<rangle> N" 
    using rhs lhs by simp
  have pf1: "pack_F F_NEQ \<langle>rhs, lhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_rl], simp)
  have j1: "(G \<tturnstile> pack_F F_NEQ \<langle>rhs, lhs\<rangle>) N" 
    using G pf1 by simp
  have g1: "mem (G \<tturnstile> pack_F F_NEQ \<langle>rhs, lhs\<rangle>) rest B" 
    by (rule mem_bool[OF j1 rest])
  have pr_ll: "\<langle>load_T lhs, load_T lhs\<rangle> N" 
    using Ll by simp
  have pf2: "pack_F F_EQ \<langle>load_T lhs, load_T lhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_ll], simp)
  have j2: "(G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T lhs\<rangle>) N" 
    using G pf2 by simp
  have m2: "mem (G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T lhs\<rangle>) rest B" 
    by (rule mem_bool[OF j2 rest])
  have e_tgLs: "(tg_L = T_SUC) B" 
    by (rule eqBool[OF tg_L sucN])
  have e_rz: "(rhs = pack_T T_ZERO 0) B" 
    by (rule eqBool[OF rhs ztz])
  have g2: "(tg_L = T_SUC \<and> rhs = pack_T T_ZERO 0 \<and>
             mem (G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T lhs\<rangle>) rest) B"
    using e_tgLs e_rz m2 by auto

  have pr_lr: "\<langle>load_T lhs, load_T rhs\<rangle> N" 
    using Ll Lr by simp
  have pf3: "pack_F F_NEQ \<langle>load_T lhs, load_T rhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_lr], simp)
  have j3: "(G \<tturnstile> pack_F F_NEQ \<langle>load_T lhs, load_T rhs\<rangle>) N" 
    using G pf3 by simp
  have m3: "mem (G \<tturnstile> pack_F F_NEQ \<langle>load_T lhs, load_T rhs\<rangle>) rest B" 
    by (rule mem_bool[OF j3 rest])
  have e_tgRs: "(tg_R = T_SUC) B" 
    by (rule eqBool[OF tg_R sucN])
  have g3: "(tg_L = T_SUC \<and> tg_R = T_SUC \<and>
             mem (G \<tturnstile> pack_F F_NEQ \<langle>load_T lhs, load_T rhs\<rangle>) rest) B"
    using e_tgLs e_tgRs m3 by auto

  have pr_ss: "\<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle> N" 
    using sucl sucr by simp
  have pf4: "pack_F F_NEQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_ss], simp)
  have j4: "(G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle>) N" 
    using G pf4 by simp
  have g4: "mem (G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle>) rest B"
    by (rule mem_bool[OF j4 rest])

  show ?thesis
    apply (rule defE[OF check_neq_rules_def[where G=G and lhs=lhs and rhs=rhs
                                             and tg_L=tg_L and tg_R=tg_R and rest=rest]])
    apply (rule condTB[OF g1 true_bool])
    apply (rule condTB[OF g2 true_bool])
    apply (rule condTB[OF g3 true_bool])
    apply (rule condTB[OF g4 true_bool false_bool])
    done
qed

lemma check_ind_template_bool [auto]:
  assumes f: "f N" and phi: "phi N" and a: "a N" and G: "G N"
      and p: "p N" and i: "i N" and r: "rest N"
  shows "check_ind_template f phi a G p i rest B"
proof (rule ind[OF p])
  have ztz: "pack_T T_ZERO 0 N" 
    by (rule pack_T_N[OF _ nat0], simp)
  show "check_ind_template f phi a G 0 i rest B"
    apply (rule defE[OF check_ind_template_def[where p=0]], insert f phi a G i r)
    apply simp
    apply (rule condTB[OF _ true_bool false_bool])
    using subst_F_N[OF nat0 i a] subst_F_N[OF nat0 i ztz] f phi ind_jdg_N[OF nat0 G i] r
    by auto
next
  fix k assume k: "k N" and IH: "check_ind_template f phi a G k i rest B"
  have ztz: "pack_T T_ZERO 0 N" 
    by (rule pack_T_N[OF _ nat0], simp)
  have skN: "S k N" 
    by (rule natS[OF k])
  have oneN: "(1::num) N" 
    by simp
  have grN: "(S k > 0) N"
    by (unfold greater_def, rule sub_terminates[OF oneN leq_terminates[OF skN nat0]])
  have g2B: "(S k > 0 = 1) B" 
    by (rule eqBool[OF grN oneN])
  have sk1: "S k - 1 = k" 
    using k by simp
  have RECB: "check_ind_template f phi a G (S k - 1) i rest B" 
    using IH sk1 by simp
  have innerB: "(if S k > 0 = 1 then check_ind_template f phi a G (S k - 1) i rest else False) B"
    by (rule condTB[OF g2B RECB false_bool])
  show "check_ind_template f phi a G (S k) i rest B"
    apply (rule defE[OF check_ind_template_def[where p="S k"]])
    apply (rule condTB[OF _ true_bool innerB])
    using subst_F_N[OF skN i a] subst_F_N[OF skN i ztz] f phi ind_jdg_N[OF skN G i] r
    by auto
qed

lemma find_ind_base_bool [auto]:
  assumes J: "J N" and a: "a N" and rest: "rest N" and ptr: "ptr N"
  shows "find_ind_base J a rest ptr B"
proof (rule list_induct[OF ptr])
  show "find_ind_base J a rest Nil B"
    apply (rule defE[OF find_ind_base_def[where J=J and a=a and rest=rest and ptr=Nil]])
    apply simp
    done
next
  fix h t assume h: "h N" and t: "t N" and IH: "find_ind_base J a rest t B"
  show "find_ind_base J a rest (Cons h t) B"
  proof -
    have htN: "h \<triangleright> t N" 
      using h t by simp
    have g0: "(h \<triangleright> t = \<emptyset>) B" 
      apply (rule eqBool[OF htN]) 
      apply simp 
      done
    have cJ: "conc_of J N" 
      using J by simp
    have ch: "conc_of h N" 
      using h by simp
    have hj: "hyp_of J N" 
      using J by simp
    have SJ: "J + 1 N" 
      using J by simp
    have eqh: "(hyp_of h = hyp_of J) B" 
      using h J by simp
    have rep: "rep_vars_F (conc_of J) (J + 1) N" 
      by (rule rep_vars_F_N[OF cJ SJ])
    have git: "check_ind_template (conc_of J) (conc_of h) a (hyp_of J)
                 (rep_vars_F (conc_of J) (J + 1)) (J + 1) rest B"
      by (rule check_ind_template_bool[OF cJ ch a hj rep SJ rest])
    show "find_ind_base J a rest (h \<triangleright> t) B"
      apply (rule defE[OF find_ind_base_def[where J=J and a=a and rest=rest and ptr="h \<triangleright> t"]])
      apply (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
      apply (rule condTB[OF g0 false_bool])
      apply (rule condTB[OF eqh _ IH])
      apply (rule condTB[OF git true_bool IH])
      done
  qed
qed

lemma check_ind_bool [auto]:
  assumes J: "J N" and r: "rest N"
  shows "check_ind J rest B"
proof -
  have cJ: "conc_of J N" 
    using J by simp
  have hj: "hyp_of J N" 
    using J by simp
  have LcJ: "load_F (conc_of J) N" 
    by (rule load_F_N[OF cJ])
  have cx: "cpx (load_F (conc_of J)) N" 
    by (rule cpx_terminates[OF LcJ])
  have xx: "\<langle>cpx (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle> N" 
    using cx by simp
  have pf: "pack_F F_EQ \<langle>cpx (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle> N"
    by (rule pack_F_N[OF _ xx], simp)
  have jN: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) N"
    using hj pf by simp
  have m: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest B"
    by (rule mem_bool[OF jN r])
  have SJ: "J + 1 N"
    using J by simp
  have fresh: "fresh_H (J + 1) (hyp_of J) B"
    by (rule fresh_H_bool[OF SJ hj])
  have guard: "(fresh_H (J + 1) (hyp_of J) \<and> mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest) B"
    using fresh m by auto
  have fib: "find_ind_base J (cpx (load_F (conc_of J))) rest rest B"
    by (rule find_ind_base_bool[OF J cx r r])
  show ?thesis
    apply (rule defE[OF check_ind_def[where J=J and rest=rest]])
    apply (rule condTB[OF guard fib false_bool])
    done
qed

lemma app_y_bool [auto]:
  assumes J: "J N" and d: "d N" and x: "x N" and y: "y N" and r: "rest N"
      and dr: "d < len dfns = 1"
  shows "app_y J d x y rest B"
proof (rule ind[OF y])
  show "app_y J d x 0 rest B"
    apply (rule defE[OF app_y_def[where y=0]], insert J d x r)
    apply simp
    apply (rule condTB[OF _ true_bool false_bool])
    apply (rule app_try_bool[OF J d x nat0 r dr])
    done
next
  fix k assume k: "k N" and IH: "app_y J d x k rest B"
  have skN: "S k N" 
    by (rule natS[OF k])
  have oneN: "(1::num) N" 
    by simp
  have grN: "(S k > 0) N"
    by (unfold greater_def, rule sub_terminates[OF oneN leq_terminates[OF skN nat0]])
  have g2B: "(S k > 0 = 1) B" 
    by (rule eqBool[OF grN oneN])
  have sk1: "S k - 1 = k" 
    using k by simp
  have RECB: "app_y J d x (S k - 1) rest B" 
    using IH sk1 by simp
  have innerB: "(if S k > 0 = 1 then app_y J d x (S k - 1) rest else False) B"
    by (rule condTB[OF g2B RECB false_bool])
  have gB: "app_try J d x (S k) rest B" 
    by (rule app_try_bool[OF J d x skN r dr])
  show "app_y J d x (S k) rest B"
    apply (rule defE[OF app_y_def[where y="S k"]])
    apply (rule condTB[OF gB true_bool innerB])
    done
qed

lemma app_x_bool [auto]:
  assumes J: "J N" and d: "d N" and x: "x N" and r: "rest N"
      and dr: "d < len dfns = 1"
  shows "app_x J d x rest B"
proof -
  have cJ: "conc_of J N" 
    using J by simp
  show ?thesis
  proof (rule ind[OF x])
    show "app_x J d 0 rest B"
      apply (rule defE[OF app_x_def[where x=0]], insert J d r)
      apply simp
      apply (rule condTB[OF _ true_bool false_bool])
      apply (rule app_y_bool[OF J d nat0 cJ r dr])
      done
  next
    fix k assume k: "k N" and IH: "app_x J d k rest B"
    have skN: "S k N" 
      by (rule natS[OF k])
    have oneN: "(1::num) N" 
      by simp
    have grN: "(S k > 0) N"
      by (unfold greater_def, rule sub_terminates[OF oneN leq_terminates[OF skN nat0]])
    have g2B: "(S k > 0 = 1) B" 
      by (rule eqBool[OF grN oneN])
    have sk1: "S k - 1 = k" 
      using k by simp
    have RECB: "app_x J d (S k - 1) rest B" 
      using IH sk1 by simp
    have innerB: "(if S k > 0 = 1 then app_x J d (S k - 1) rest else False) B"
      by (rule condTB[OF g2B RECB false_bool])
    have gB: "app_y J d (S k) (conc_of J) rest B" 
      by (rule app_y_bool[OF J d skN cJ r dr])
    show "app_x J d (S k) rest B"
      apply (rule defE[OF app_x_def[where x="S k"]])
      apply (rule condTB[OF gB true_bool innerB])
      done
  qed
qed

lemma app_d_bool [auto]:
  assumes J: "J N" and d: "d N" and r: "rest N"
  shows "app_d J d rest B"
proof -
  have ldN: "len dfns N" 
    by (rule len_nat[OF dfns_N])
  have oneN: "(1::num) N" 
    by simp
  have cJ: "conc_of J N" 
    using J by simp
  show ?thesis
  proof (rule ind[OF d])
    have g0: "(0 < len dfns = 1) B" 
      by (rule eqBool[OF less_terminates[OF nat0 ldN] oneN])
    have then0: "0 < len dfns = 1 \<Longrightarrow>
                 (if app_x J 0 (conc_of J) rest then True else False) B"
    proof -
      assume hh: "0 < len dfns = 1"
      have ax: "app_x J 0 (conc_of J) rest B" 
        by (rule app_x_bool[OF J nat0 cJ r hh])
      show "(if app_x J 0 (conc_of J) rest then True else False) B"
        by (rule condTB[OF ax true_bool false_bool])
    qed
    show "app_d J 0 rest B"
      apply (rule defE[OF app_d_def[where d=0]])
      apply simp
      apply (rule condTB'[OF g0 then0])
       apply assumption
      apply (rule false_bool)
      done
  next
    fix k assume k: "k N" and IH: "app_d J k rest B"
    have skN: "S k N" 
      by (rule natS[OF k])
    have grN: "(S k > 0) N"
      by (unfold greater_def, rule sub_terminates[OF oneN leq_terminates[OF skN nat0]])
    have g2B: "(S k > 0 = 1) B" 
      by (rule eqBool[OF grN oneN])
    have sk1: "S k - 1 = k" 
      using k by simp
    have RECB: "app_d J (S k - 1) rest B" 
      using IH sk1 by simp
    have innerB: "(if S k > 0 = 1 then app_d J (S k - 1) rest else False) B"
      by (rule condTB[OF g2B RECB false_bool])
    have gS: "(S k < len dfns = 1) B" 
      by (rule eqBool[OF less_terminates[OF skN ldN] oneN])
    have thenS: "S k < len dfns = 1 \<Longrightarrow>
                 (if app_x J (S k) (conc_of J) rest then True
                  else if S k > 0 = 1 then app_d J (S k - 1) rest else False) B"
    proof -
      assume hh: "S k < len dfns = 1"
      have ax: "app_x J (S k) (conc_of J) rest B" 
        by (rule app_x_bool[OF J skN cJ r hh])
      show "(if app_x J (S k) (conc_of J) rest then True
             else if S k > 0 = 1 then app_d J (S k - 1) rest else False) B"
        by (rule condTB[OF ax true_bool innerB])
    qed
    show "app_d J (S k) rest B"
      apply (rule defE[OF app_d_def[where d="S k"]])
      apply (rule condTB'[OF gS thenS])
       apply assumption
      apply (rule innerB)
      done
  qed
qed

lemma check_app_bool [auto]:
  assumes J: "J N" and r: "rest N"
  shows "check_app J rest B"
proof -
  have oneN: "(1::num) N" 
    by simp
  have ld1: "len dfns - 1 N" 
    by (rule sub_terminates[OF len_nat[OF dfns_N] oneN])
  show ?thesis
    apply (rule defE[OF check_app_def[where J=J and rest=rest]])
    apply (rule app_d_bool[OF J ld1 r])
    done
qed

lemma valid_step_bool [auto]:
  assumes J: "J N" and r: "rest N"
  shows "valid_step J rest B"
proof -
  have cJ: "conc_of J N" 
    using J by simp
  have hj: "hyp_of J N" 
    using J by simp
  have LcJ: "load_F (conc_of J) N" 
    by (rule load_F_N[OF cJ])
  have cx: "cpx (load_F (conc_of J)) N" 
    by (rule cpx_terminates[OF LcJ])
  have cy: "cpy (load_F (conc_of J)) N" 
    by (rule cpy_terminates[OF LcJ])
  have tgx: "tag_T (cpx (load_F (conc_of J))) N" 
    by (rule tag_T_N[OF cx])
  have tgy: "tag_T (cpy (load_F (conc_of J))) N" 
    by (rule tag_T_N[OF cy])
  have feqN: "F_EQ N" 
    by simp

  have g1: "mem (conc_of J) (hyp_of J) B" 
    by (rule mem_bool[OF cJ hj])
  have g2: "check_cut J rest B" 
    by (rule check_cut_bool[OF J r])
  have g3: "check_subst J rest B" 
    by (rule check_subst_bool[OF J r])
  have g4: "check_ind J rest B" 
    by (rule check_ind_bool[OF J r])
  have g5: "check_app J rest B" 
    by (rule check_app_bool[OF J r])
  have g6: "check_struct J rest B" 
    by (rule check_struct_bool[OF J r])
  have g7: "(tag_F (conc_of J) = F_EQ) B" 
    by (rule eqBool[OF tag_F_N[OF cJ] feqN])
  have beq: "check_eq_rules (hyp_of J) (cpx (load_F (conc_of J))) (cpy (load_F (conc_of J)))
               (tag_T (cpx (load_F (conc_of J)))) (tag_T (cpy (load_F (conc_of J)))) rest B"
    by (rule check_eq_rules_bool[OF hj cx cy tgx tgy r])
  have bneq: "check_neq_rules (hyp_of J) (cpx (load_F (conc_of J))) (cpy (load_F (conc_of J)))
               (tag_T (cpx (load_F (conc_of J)))) (tag_T (cpy (load_F (conc_of J)))) rest B"
    by (rule check_neq_rules_bool[OF hj cx cy tgx tgy r])

  show ?thesis
    apply (rule defE[OF valid_step_def[where J=J and rest=rest]])
    apply (rule condTB[OF g1 true_bool])
    apply (rule condTB[OF g2 true_bool])
    apply (rule condTB[OF g3 true_bool])
    apply (rule condTB[OF g4 true_bool])
    apply (rule condTB[OF g5 true_bool])
    apply (rule condTB[OF g6 true_bool])
    apply (rule condTB[OF g7 beq bneq])
    done
qed

lemma check_list_bool [auto]:
  assumes pfn: "pf N"
  shows "check_list pf B"
proof (rule list_induct[OF pfn])
  show "check_list Nil B"
    apply (rule defE[OF check_list_def[where pf=Nil]])
    apply simp
    done
next
  fix h t assume h: "h N" and t: "t N" and IH: "check_list t B"
  show "check_list (Cons h t) B"
  proof -
    have htN: "h \<triangleright> t N" 
      using h t by simp
    have g0: "(h \<triangleright> t = \<emptyset>) B" 
      apply (rule eqBool[OF htN]) 
      apply simp 
      done
    have vs: "valid_step h t B" 
      by (rule valid_step_bool[OF h t])
    show "check_list (h \<triangleright> t) B"
      apply (rule defE[OF check_list_def[where pf="h \<triangleright> t"]])
      apply (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
      apply (rule condTB[OF g0 true_bool])
      apply (rule condTB[OF vs IH false_bool])
      done
  qed
qed

lemma proof_is_bool: "p N \<Longrightarrow> J N \<Longrightarrow> is_valid_proof p J B"
proof -
  assume p: "p N" and J: "J N"
  have g0: "(p = Nil) B" 
    by (rule eqBool[OF p nil_nat])
  have g1: "(list_hd p = J) B" 
    by (rule eqBool[OF list_hd_nat[OF p] J])
  have cl: "check_list p B" 
    by (rule check_list_bool[OF p])
  show "is_valid_proof p J B"
    apply (rule defE[OF is_valid_proof_def[where pf=p and J=J]])
    apply (rule condTB[OF g0 false_bool])
    apply (rule condTB[OF g1 cl false_bool])
    done
qed

lemma dfn_is_rangeE:
  assumes d: "d N"
      and di: "dfn_is d k b"
  shows "d < len dfns = 1"
proof -
  have ld: "len dfns N"
    by (rule len_nat[OF dfns_N])
  have gB: "(d < len dfns = 1) B"
    by (rule eqBool[OF less_terminates[OF d ld]], simp)
  have R:
    "if d < len dfns = 1
     then nth d dfns = b \<and> fresh_T k b
     else False"
    using di by (rule defI[OF dfn_is_def])
  show ?thesis
  proof (rule cases_bool[where q="d < len dfns = 1"])
    show "(d < len dfns = 1) B"
      by (rule gB)
  next
    assume g: "d < len dfns = 1"
    show ?thesis
      by (rule g)
  next
    assume ng: "\<not> d < len dfns = 1"
    have F: "False"
      using ng R by (rule notcond_thenE)
    show ?thesis
      by (rule exF[OF F not_false])
  qed
qed

lemma dfn_is_bodyE:
  assumes d: "d N"
      and di: "dfn_is d k b"
  shows "nth d dfns = b"
proof -
  have dr: "d < len dfns = 1"
    using d di by (rule dfn_is_rangeE)
  have R:
    "if d < len dfns = 1
     then nth d dfns = b \<and> fresh_T k b
     else False"
    using di by (rule defI[OF dfn_is_def])
  have C: "nth d dfns = b \<and> fresh_T k b"
    using dr R by (rule cond_thenE)
  show ?thesis
    using C by (rule conjE1)
qed

lemma dfn_is_freshE:
  assumes d: "d N"
      and di: "dfn_is d k b"
  shows "fresh_T k b"
proof -
  have dr: "d < len dfns = 1"
    using d di by (rule dfn_is_rangeE)
  have R:
    "if d < len dfns = 1
     then nth d dfns = b \<and> fresh_T k b
     else False"
    using di by (rule defI[OF dfn_is_def])
  have C: "nth d dfns = b \<and> fresh_T k b"
    using dr R by (rule cond_thenE)
  show ?thesis
    using C by (rule conjE2)
qed

lemma neq_impl_term:
  assumes ne: "a \<noteq> b"
  shows "a N"
proof -
  have eB: "(a = b) B"
    unfolding bJudg_def
    apply (rule disjI2)
    using ne unfolding neq_def by assumption
  have C: "(a N) \<and> (b N)"
    by (rule eqE[OF eB])
  show ?thesis
    using C by (rule conjE1)
qed

lemma neq_impl_term2:
  assumes ne: "a \<noteq> b"
  shows "b N"
proof -
  have eB: "(a = b) B"
    unfolding bJudg_def
    apply (rule disjI2)
    using ne unfolding neq_def by assumption
  have C: "(a N) \<and> (b N)"
    by (rule eqE[OF eB])
  show ?thesis
    using C by (rule conjE2)
qed

lemma mem_cons_head:
  assumes h: "h N" and t: "t N"
  shows "h \<in> (h \<triangleright> t)"
  using h t by simp

lemma mem_cons_tail:
  assumes h: "h N"
      and t: "t N"
      and x: "x N"
      and xt: "x \<in> t"
  shows "x \<in> (h \<triangleright> t)"
proof -
  have rhs: "if h = x then True else x \<in> t"
  proof (rule cases_bool[where q="h = x"])
    show "(h = x) B"
      by (rule eqBool[OF h x])
  next
    assume hx: "h = x"
    have e: "(if h = x then True else x \<in> t) \<longleftrightarrow> True"
      by (rule condI1B[OF hx true_bool])
    show "if h = x then True else x \<in> t"
      using true e by simp
  next
    assume hx: "\<not> (h = x)"
    have e: "(if h = x then True else x \<in> t) \<longleftrightarrow> x \<in> t"
      by (rule condI2B[OF hx mem_bool[OF x t]])
    show "if h = x then True else x \<in> t"
      using xt e by simp
  qed
  have bck: "(if h = x then True else x \<in> t) \<longrightarrow> x \<in> (h \<triangleright> t)"
    by (rule iffE2[OF mem_cons[OF h t x]])
  show "x \<in> (h \<triangleright> t)"
    using bck rhs
    by (rule implE)
qed

lemma subset_nilI:
  assumes G: "G N"
  shows "subset Nil G"
proof -
  have nn: "Nil = Nil"
    using nil_nat by simp
  have eq: "subset Nil G \<longleftrightarrow> True"
    apply (rule defE[OF subset_def[where G'=Nil and G=G]])
    apply (rule condI1B[OF nn true_bool])
    done
  have bck: "True \<longrightarrow> subset Nil G"
    by (rule iffE2[OF eq])
  show ?thesis
    using bck true by (rule implE)
qed

lemma subset_cons_right:
  assumes h: "h N"
      and G': "G' N"
      and G: "G N"
      and sub: "subset G' G"
  shows "subset G' (h \<triangleright> G)"
proof -
  have hG: "h \<triangleright> G N"
    using h G by simp
  have main: "subset G' G \<longrightarrow> subset G' (h \<triangleright> G)"
  proof (rule list_induct[OF G', where Q="\<lambda>L. subset L G \<longrightarrow> subset L (h \<triangleright> G)"])
    show "subset Nil G \<longrightarrow> subset Nil (h \<triangleright> G)"
    proof (rule implI)
      show "subset Nil G B"
        by (rule subset_bool[OF nil_nat G])
    next
      assume "subset Nil G"
      show "subset Nil (h \<triangleright> G)"
        by (rule subset_nilI[OF hG])
    qed
  next
    fix a t
    assume a: "a N"
       and t: "t N"
       and IH: "subset t G \<longrightarrow> subset t (h \<triangleright> G)"
    have atN: "a \<triangleright> t N"
      using a t by simp
    show "subset (a \<triangleright> t) G \<longrightarrow> subset (a \<triangleright> t) (h \<triangleright> G)"
    proof (rule implI)
      show "subset (a \<triangleright> t) G B"
        by (rule subset_bool[OF atN G])
    next
      assume atG: "subset (a \<triangleright> t) G"
      have split: "mem a G \<and> subset t G"
        using atG a t G by simp
      have aG: "mem a G"
        using split by (rule conjE1)
      have tG: "subset t G"
        using split by (rule conjE2)
      have thG: "subset t (h \<triangleright> G)"
        using IH tG by (rule implE)
      have ahG: "mem a (h \<triangleright> G)"
        using h G a aG by (rule mem_cons_tail)
      have pair: "mem a (h \<triangleright> G) \<and> subset t (h \<triangleright> G)"
        apply (rule conjI)
        apply (rule ahG)
        apply (rule thG)
        done
      have eq:
        "subset (a \<triangleright> t) (h \<triangleright> G) \<longleftrightarrow>
         (mem a (h \<triangleright> G) \<and> subset t (h \<triangleright> G))"
        by (rule subset_cons[OF a t hG])
      have bck: "(mem a (h \<triangleright> G) \<and> subset t (h \<triangleright> G)) \<longrightarrow> subset (a \<triangleright> t) (h \<triangleright> G)"
        by (rule iffE2[OF eq])
      show "subset (a \<triangleright> t) (h \<triangleright> G)"
        using bck pair by (rule implE)
    qed
  qed
  show ?thesis
    using main sub by (rule implE)
qed

lemma subset_refl:
  assumes G: "G N"
  shows "subset G G"
proof (rule list_induct[OF G])
  show "subset Nil Nil"
    by (rule subset_nilI[OF nil_nat])
next
  fix h t
  assume h: "h N"
     and t: "t N"
     and IH: "subset t t"
  have htN: "h \<triangleright> t N"
    using h t by simp
  have tail: "subset t (h \<triangleright> t)"
    using h t t IH by (rule subset_cons_right)
  have head: "mem h (h \<triangleright> t)"
    using h t by simp
  have pair: "mem h (h \<triangleright> t) \<and> subset t (h \<triangleright> t)"
    apply (rule conjI)
    apply (rule head)
    apply (rule tail)
    done
  have eq: "subset (h \<triangleright> t) (h \<triangleright> t) \<longleftrightarrow> (mem h (h \<triangleright> t) \<and> subset t (h \<triangleright> t))"
    by (rule subset_cons[OF h t htN])
  have bck: "(mem h (h \<triangleright> t) \<and> subset t (h \<triangleright> t)) \<longrightarrow> subset (h \<triangleright> t) (h \<triangleright> t)"
    by (rule iffE2[OF eq])
  show "subset (h \<triangleright> t) (h \<triangleright> t)"
    using bck pair by (rule implE)
qed

lemma subset_cons_headE:
  assumes h: "h N" and t: "t N" and G: "G N"
      and sub: "subset (h \<triangleright> t) G"
  shows "h \<in> G"
proof -
  have C: "h \<in> G \<and> subset t G"
    using h t G sub by simp
  show ?thesis
    using C by (rule conjE1)
qed

lemma subset_cons_tailE:
  assumes h: "h N" and t: "t N" and G: "G N"
      and sub: "subset (h \<triangleright> t) G"
  shows "subset t G"
proof -
  have C: "h \<in> G \<and> subset t G"
    using h t G sub by simp
  show ?thesis
    using C by (rule conjE2)
qed

lemma lt_twoE:
  assumes i: "i N"
      and lt: "i < 2 = 1"
  obtains zero where "i = 0"
        | one where "i = 1"
proof -
  show thesis
  proof (rule cases_nat_2[where x=i and Q="\<lambda>_. thesis"])
    show "i N"
      using i .
  next
    assume i0: "i = 0"
    show thesis
      by (rule that(1)[OF i0])
  next
    fix j
    assume j: "j N"
       and ij: "i = S j"
    have sjlt: "S j < S 1 = 1"
      using lt ij by simp
    have oneN: "(1::num) N"
      by simp
    have jlt: "j < 1 = 1"
      by (rule less_monotone_pred[OF j oneN sjlt])
    have j0: "j = 0"
      using j jlt by (rule x_less_1_is_0)
    have i1: "i = 1"
      using ij j0 by simp
    show thesis
      by (rule that(2)[OF i1])
  qed
qed

lemma nth_one_two [simp]:
  assumes x: "x N" and y: "y N"
  shows "nth 1 (x \<triangleright> y \<triangleright> Nil) = y"
proof -
  have xy: "y \<triangleright> Nil N"
    using y by simp
  show ?thesis
    apply (rule defE[OF nth_def[where i=1 and xs="x \<triangleright> y \<triangleright> Nil"]])
    using x y xy
    apply simp
    done
qed

(* Generic continuation forms of the evaluator equations. *)
(* for some of these we have to peel the branches but they are repetitive
since for so many we just do the reverse direction *) 

lemma eval_varD:
  assumes t: "t N" and tg: "tag_T t = T_VAR"
      and H: "Q (eval t A)"
  shows "Q (nth (load_T t) A)"
  using tg defI[where Q="Q", OF eval_def H] by (rule cond_thenQ_E)

lemma eval_varI:
  assumes t: "t N"
      and tg: "tag_T t = T_VAR"
      and H: "Q (nth (load_T t) A)"
  shows "Q (eval t A)"
proof -
  show ?thesis
    apply (rule defE[OF eval_def[where t=t and A=A]])
    using tg H by (rule cond_thenQ_I)
qed

lemma eval_zeroD:
  assumes t: "t N" and tg: "tag_T t = T_ZERO"
      and H: "Q (eval t A)"
  shows "Q 0"
proof -
  have nvar: "\<not> tag_T t = T_VAR" using tg by simp
  show "Q 0"
    using tg cond_elseQ_E[where Q="Q", OF nvar defI[where Q="Q", OF eval_def H]]
    by (rule cond_thenQ_E)
qed

lemma eval_zeroI:
  assumes t: "t N" and tg: "tag_T t = T_ZERO"
      and H: "Q 0"
  shows "Q (eval t A)"
proof -
  have nvar: "\<not> tag_T t = T_VAR" using tg by simp
  show ?thesis
    by (rule defE[OF eval_def[where t=t and A=A]],
        rule cond_elseQ_I[where Q="Q", OF nvar cond_thenQ_I[where Q="Q", OF tg H]])
qed

lemma eval_sucD:
  assumes t: "t N"
      and tg: "tag_T t = T_SUC"
      and H: "Q (eval t A)"
  shows "Q (S (eval (load_T t) A))"
proof -
  have nvar: "\<not> tag_T t = T_VAR" using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO" using tg by simp
  show ?thesis
    using tg cond_elseQ_E[where Q="Q", OF nzero cond_elseQ_E[where Q="Q", OF nvar defI[where Q="Q", OF eval_def H]]]
    by (rule cond_thenQ_E)
qed

lemma eval_sucI:
  assumes t: "t N"
      and tg: "tag_T t = T_SUC"
      and H: "Q (S (eval (load_T t) A))"
  shows "Q (eval t A)"
proof -
  have nvar: "\<not> tag_T t = T_VAR" using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO" using tg by simp
  show ?thesis
    by (rule defE[OF eval_def[where t=t and A=A]],
        rule cond_elseQ_I[where Q="Q", OF nvar cond_elseQ_I[where Q="Q", OF nzero cond_thenQ_I[where Q="Q", OF tg H]]])
qed

lemma eval_predD:
  assumes t: "t N"
      and tg: "tag_T t = T_PRED"
      and H: "Q (eval t A)"
  shows "Q (P (eval (load_T t) A))"
proof -
  have nvar: "\<not> tag_T t = T_VAR" using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO" using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC" using tg by simp
  show ?thesis
    using tg cond_elseQ_E[where Q="Q", OF nsuc cond_elseQ_E[where Q="Q", OF nzero cond_elseQ_E[where Q="Q", OF nvar defI[where Q="Q", OF eval_def H]]]]
    by (rule cond_thenQ_E)
qed

lemma eval_predI:
  assumes t: "t N"
      and tg: "tag_T t = T_PRED"
      and H: "Q (P (eval (load_T t) A))"
  shows "Q (eval t A)"
proof -
  have nvar: "\<not> tag_T t = T_VAR" using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO" using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC" using tg by simp
  show ?thesis
    by (rule defE[OF eval_def[where t=t and A=A]],
        rule cond_elseQ_I[where Q="Q", OF nvar cond_elseQ_I[where Q="Q", OF nzero cond_elseQ_I[where Q="Q", OF nsuc cond_thenQ_I[where Q="Q", OF tg H]]]])
qed

lemma eval_ifzD:
  assumes t: "t N"
      and tg: "tag_T t = T_IFZ"
      and H: "Q (eval t A)"
  shows
    "Q (if eval (cpx (load_T t)) A = 0
       then eval (cpx (cpy (load_T t))) A
       else eval (cpy (cpy (load_T t))) A)"
proof -
  have nvar: "\<not> tag_T t = T_VAR" using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO" using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC" using tg by simp
  have npred: "\<not> tag_T t = T_PRED" using tg by simp
  show ?thesis
    using tg cond_elseQ_E[where Q="Q", OF npred cond_elseQ_E[where Q="Q", OF nsuc cond_elseQ_E[where Q="Q", OF nzero cond_elseQ_E[where Q="Q", OF nvar defI[where Q="Q", OF eval_def H]]]]]
    by (rule cond_thenQ_E)
qed

lemma eval_ifzI:
  assumes t: "t N"
      and tg: "tag_T t = T_IFZ"
      and H:
        "Q (if eval (cpx (load_T t)) A = 0
           then eval (cpx (cpy (load_T t))) A
           else eval (cpy (cpy (load_T t))) A)"
  shows "Q (eval t A)"
proof -
  have nvar: "\<not> tag_T t = T_VAR" using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO" using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC" using tg by simp
  have npred: "\<not> tag_T t = T_PRED" using tg by simp
  show ?thesis
    by (rule defE[OF eval_def[where t=t and A=A]],
        rule cond_elseQ_I[where Q="Q", OF nvar cond_elseQ_I[where Q="Q", OF nzero cond_elseQ_I[where Q="Q", OF nsuc cond_elseQ_I[where Q="Q", OF npred cond_thenQ_I[where Q="Q", OF tg H]]]]])
qed

lemma eval_appD:
  assumes t: "t N"
      and nvar: "\<not> tag_T t = T_VAR"
      and nzero: "\<not> tag_T t = T_ZERO"
      and nsuc: "\<not> tag_T t = T_SUC"
      and npred: "\<not> tag_T t = T_PRED"
      and nifz: "\<not> tag_T t = T_IFZ"
      and H: "Q (eval t A)"
  shows "Q (if eval (cpx (cpy (load_T t))) A = eval (cpx (cpy (load_T t))) A
            then (if eval (cpy (cpy (load_T t))) A = eval (cpy (cpy (load_T t))) A
                  then eval (nth (cpx (load_T t)) dfns)
                         ((eval (cpx (cpy (load_T t))) A)\<triangleright> ((eval (cpy (cpy (load_T t))) A) \<triangleright> Nil))
                  else 0)
            else 0)"
  by (rule cond_elseQ_E[where Q="Q", OF nifz cond_elseQ_E[where Q="Q", OF npred cond_elseQ_E[where Q="Q", OF nsuc cond_elseQ_E[where Q="Q", OF nzero cond_elseQ_E[where Q="Q", OF nvar defI[where Q="Q", OF eval_def H]]]]]])

lemma eval_appI:
  assumes t: "t N"
      and tg: "tag_T t = T_APP"
      and H:
        "Q (if eval (cpx (cpy (load_T t))) A = eval (cpx (cpy (load_T t))) A
            then (if eval (cpy (cpy (load_T t))) A = eval (cpy (cpy (load_T t))) A
                  then eval (nth (cpx (load_T t)) dfns)
                         ((eval (cpx (cpy (load_T t))) A)\<triangleright> ((eval (cpy (cpy (load_T t))) A) \<triangleright> Nil))
                  else 0)
            else 0)"
  shows "Q (eval t A)"
proof -
  have nvar: "\<not> tag_T t = T_VAR" using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO" using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC" using tg by simp
  have npred: "\<not> tag_T t = T_PRED" using tg by simp
  have nifz: "\<not> tag_T t = T_IFZ" using tg by simp
  show ?thesis
    by (rule defE[OF eval_def[where t=t and A=A]],
        rule cond_elseQ_I[where Q="Q", OF nvar cond_elseQ_I[where Q="Q", OF nzero cond_elseQ_I[where Q="Q", OF nsuc cond_elseQ_I[where Q="Q", OF npred cond_elseQ_I[where Q="Q", OF nifz H]]]]])
qed

text \<open>Call-by-value: a grounded application forces its arguments to be
  grounded.  From @{text "eval t A N"} with @{text t} an application we can
  read off the argument values and the underlying body value.\<close>
lemma eval_app_arg1N:
  assumes t: "t N" and tg: "tag_T t = T_APP" and hN: "eval t A N"
  shows "eval (cpx (cpy (load_T t))) A N"
proof -
  let ?a1 = "eval (cpx (cpy (load_T t))) A"
  have body:
    "(if ?a1 = ?a1
      then (if eval (cpy (cpy (load_T t))) A = eval (cpy (cpy (load_T t))) A
            then eval (nth (cpx (load_T t)) dfns)
                   ((?a1)\<triangleright> ((eval (cpy (cpy (load_T t))) A) \<triangleright> Nil))
            else 0)
      else 0) N"
    by (rule eval_appD[where Q="\<lambda>x. x N", OF t _ _ _ _ _ hN], (simp add: tg)+)
  have gB: "(?a1 = ?a1) B" by (rule condE3[OF body])
  show "?a1 N" by (rule conjE1[OF eqE[OF gB]])
qed

lemma eval_app_arg2N:
  assumes t: "t N" and tg: "tag_T t = T_APP" and hN: "eval t A N"
  shows "eval (cpy (cpy (load_T t))) A N"
proof -
  let ?a1 = "eval (cpx (cpy (load_T t))) A"
  let ?a2 = "eval (cpy (cpy (load_T t))) A"
  have g1: "?a1 = ?a1" by (rule eval_app_arg1N[OF t tg hN, unfolded isNat_def])
  have body:
    "(if ?a1 = ?a1
      then (if ?a2 = ?a2
            then eval (nth (cpx (load_T t)) dfns) ((?a1)\<triangleright> ((?a2) \<triangleright> Nil))
            else 0)
      else 0) N"
    by (rule eval_appD[where Q="\<lambda>x. x N", OF t _ _ _ _ _ hN], (simp add: tg)+)
  have inner: "(if ?a2 = ?a2 then eval (nth (cpx (load_T t)) dfns) ((?a1)\<triangleright> ((?a2) \<triangleright> Nil)) else 0) N"
    by (rule condE1[OF g1 body])
  have gB: "(?a2 = ?a2) B" by (rule condE3[OF inner])
  show "?a2 N" by (rule conjE1[OF eqE[OF gB]])
qed

lemma eval_app_val:
  assumes t: "t N" and tg: "tag_T t = T_APP" and hN: "eval t A N"
  shows "eval t A = eval (nth (cpx (load_T t)) dfns)
                      ((eval (cpx (cpy (load_T t))) A)\<triangleright> ((eval (cpy (cpy (load_T t))) A) \<triangleright> Nil))"
proof -
  let ?a1 = "eval (cpx (cpy (load_T t))) A"
  let ?a2 = "eval (cpy (cpy (load_T t))) A"
  let ?body = "eval (nth (cpx (load_T t)) dfns) ((?a1)\<triangleright> ((?a2) \<triangleright> Nil))"
  have a1N: "?a1 N" by (rule eval_app_arg1N[OF t tg hN])
  have a2N: "?a2 N" by (rule eval_app_arg2N[OF t tg hN])
  have g1: "?a1 = ?a1" by (rule a1N[unfolded isNat_def])
  have g2: "?a2 = ?a2" by (rule a2N[unfolded isNat_def])
  have refl: "eval t A = eval t A" by (rule hN[unfolded isNat_def])
  have red: "eval t A = (if ?a1 = ?a1 then (if ?a2 = ?a2 then ?body else 0) else 0)"
    by (rule eval_appD[where Q="\<lambda>x. eval t A = x", OF t _ _ _ _ _ refl], (simp add: tg)+)
  have outerN: "(if ?a1 = ?a1 then (if ?a2 = ?a2 then ?body else 0) else 0) N"
    using red hN by (rule eqSubst[where Q="\<lambda>z. z N"])
  have innerN: "(if ?a2 = ?a2 then ?body else 0) N" by (rule condE1[OF g1 outerN])
  have bodyN: "?body N" by (rule condE1[OF g2 innerN])
  have e1: "(if ?a1 = ?a1 then (if ?a2 = ?a2 then ?body else 0) else 0) = (if ?a2 = ?a2 then ?body else 0)"
    by (rule condI1Eq[OF g1 innerN innerN[unfolded isNat_def]])
  have e2: "(if ?a2 = ?a2 then ?body else 0) = ?body"
    by (rule condI1Eq[OF g2 bodyN bodyN[unfolded isNat_def]])
  have t1: "eval t A = (if ?a2 = ?a2 then ?body else 0)" using red e1 by (rule eq_trans)
  show ?thesis using t1 e2 by (rule eq_trans)
qed

(* Continuation forms of subst_body's constructor equations. *)

lemma subst_body_var0D:
  assumes b: "b N"
      and tg: "tag_T b = T_VAR"
      and ld: "load_T b = 0"
      and H: "Q (subst_body b x y)"
  shows "Q x"
proof -
  have R:
    "Q (if tag_T b = T_VAR then
         (if load_T b = 0 then x
          else if load_T b = 1 then y
          else b)
       else if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using H
    by (rule defI[OF subst_body_def])
  have R0:
    "Q (if load_T b = 0 then x
       else if load_T b = 1 then y
       else b)"
    using tg R by (rule cond_thenQ_E[where c="tag_T b = T_VAR"
            and a="if load_T b = 0 then x
                   else if load_T b = 1 then y
                   else b"])
  show ?thesis
    using ld R0  by (rule cond_thenQ_E[where c="load_T b = 0" and a=x])
qed

lemma subst_body_var1D:
  assumes b: "b N"
      and tg: "tag_T b = T_VAR"
      and ld: "load_T b = 1"
      and H: "Q (subst_body b x y)"
  shows "Q y"
proof -
  have R:
    "Q (if tag_T b = T_VAR then
         (if load_T b = 0 then x
          else if load_T b = 1 then y
          else b)
       else if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using H
    by (rule defI[OF subst_body_def])
  have R0:
    "Q (if load_T b = 0 then x
       else if load_T b = 1 then y
       else b)"
    using tg R by (rule cond_thenQ_E[where c="tag_T b = T_VAR"
            and a="if load_T b = 0 then x
                   else if load_T b = 1 then y
                   else b"])
  have nzero: "\<not> load_T b = 0"
    using ld by simp
  have R1:
    "Q (if load_T b = 1 then y
       else b)"
    using nzero R0 by (rule cond_elseQ_E[where c="load_T b = 0" and a=x])
  show ?thesis
    using ld R1  by (rule cond_thenQ_E[where c="load_T b = 1" and a=y])
qed

lemma subst_body_zeroD:
  assumes b: "b N"
      and tg: "tag_T b = T_ZERO"
      and H: "Q (subst_body b x y)"
  shows "Q b"
proof -
  have R:
    "Q (if tag_T b = T_VAR then
         (if load_T b = 0 then x
          else if load_T b = 1 then y
          else b)
       else if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using H
    by (rule defI[OF subst_body_def])
  have nvar: "\<not> tag_T b = T_VAR"
    using tg by simp
  have R0:
    "Q (if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nvar R
    by (rule cond_elseQ_E[where c="tag_T b = T_VAR"
            and a="if load_T b = 0 then x
                   else if load_T b = 1 then y
                   else b"])
  show ?thesis
    using tg R0
    by (rule cond_thenQ_E[where c="tag_T b = T_ZERO" and a=b])
qed

lemma subst_body_sucD:
  assumes b: "b N"
      and tg: "tag_T b = T_SUC"
      and H: "Q (subst_body b x y)"
  shows "Q (pack_T T_SUC (subst_body (load_T b) x y))"
proof -
  have R:
    "Q (if tag_T b = T_VAR then
         (if load_T b = 0 then x
          else if load_T b = 1 then y
          else b)
       else if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using H
    by (rule defI[OF subst_body_def])
  have nvar: "\<not> tag_T b = T_VAR"
    using tg by simp
  have R0:
    "Q (if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nvar R
    by (rule cond_elseQ_E[where c="tag_T b = T_VAR"
            and a="if load_T b = 0 then x
                   else if load_T b = 1 then y
                   else b"])
  have nzero: "\<not> tag_T b = T_ZERO"
    using tg by simp
  have R1:
    "Q (if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nzero R0
    by (rule cond_elseQ_E[where c="tag_T b = T_ZERO" and a=b])
  show ?thesis
    using tg R1
    by (rule cond_thenQ_E[where c="tag_T b = T_SUC" and a="pack_T T_SUC (subst_body (load_T b) x y)"])
qed

lemma subst_body_predD:
  assumes b: "b N"
      and tg: "tag_T b = T_PRED"
      and H: "Q (subst_body b x y)"
  shows "Q (pack_T T_PRED (subst_body (load_T b) x y))"
proof -
  have R:
    "Q (if tag_T b = T_VAR then
         (if load_T b = 0 then x
          else if load_T b = 1 then y
          else b)
       else if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using H
    by (rule defI[OF subst_body_def])
  have nvar: "\<not> tag_T b = T_VAR"
    using tg by simp
  have R0:
    "Q (if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nvar R
    by (rule cond_elseQ_E[where c="tag_T b = T_VAR"
            and a="if load_T b = 0 then x
                   else if load_T b = 1 then y
                   else b"])
  have nzero: "\<not> tag_T b = T_ZERO"
    using tg by simp
  have R1:
    "Q (if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nzero R0
    by (rule cond_elseQ_E[where c="tag_T b = T_ZERO" and a=b])
  have nsuc: "\<not> tag_T b = T_SUC"
    using tg by simp
  have R2:
    "Q (if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nsuc R1
    by (rule cond_elseQ_E[where c="tag_T b = T_SUC" and a="pack_T T_SUC (subst_body (load_T b) x y)"])
  show ?thesis
    using tg R2
    by (rule cond_thenQ_E[where c="tag_T b = T_PRED" and a="pack_T T_PRED (subst_body (load_T b) x y)"])
qed

lemma subst_body_ifzD:
  assumes b: "b N"
      and tg: "tag_T b = T_IFZ"
      and H: "Q (subst_body b x y)"
  shows
    "Q (pack_T T_IFZ
      \<langle>subst_body (cpx (load_T b)) x y,
       \<langle>subst_body (cpx (cpy (load_T b))) x y,
        subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
proof -
  have R:
    "Q (if tag_T b = T_VAR then
         (if load_T b = 0 then x
          else if load_T b = 1 then y
          else b)
       else if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using H
    by (rule defI[OF subst_body_def])
  have nvar: "\<not> tag_T b = T_VAR"
    using tg by simp
  have R0:
    "Q (if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nvar R
    by (rule cond_elseQ_E[where c="tag_T b = T_VAR"
            and a="if load_T b = 0 then x
                   else if load_T b = 1 then y
                   else b"])
  have nzero: "\<not> tag_T b = T_ZERO"
    using tg by simp
  have R1:
    "Q (if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nzero R0
    by (rule cond_elseQ_E[where c="tag_T b = T_ZERO" and a=b])
  have nsuc: "\<not> tag_T b = T_SUC"
    using tg by simp
  have R2:
    "Q (if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nsuc R1
    by (rule cond_elseQ_E[where c="tag_T b = T_SUC" and a="pack_T T_SUC (subst_body (load_T b) x y)"])
  have npred: "\<not> tag_T b = T_PRED"
    using tg by simp
  have R3:
    "Q (if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using npred R2
    by (rule cond_elseQ_E[where c="tag_T b = T_PRED" and a="pack_T T_PRED (subst_body (load_T b) x y)"])
  show ?thesis
    using tg R3
    by (rule cond_thenQ_E[where c="tag_T b = T_IFZ"
            and a="pack_T T_IFZ
              \<langle>subst_body (cpx (load_T b)) x y,
               \<langle>subst_body (cpx (cpy (load_T b))) x y,
                subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>"])
qed

lemma subst_body_appD:
  assumes b: "b N"
      and tg: "tag_T b = T_APP"
      and H: "Q (subst_body b x y)"
  shows
    "Q (pack_T T_APP
      \<langle>cpx (load_T b),
       \<langle>subst_body (cpx (cpy (load_T b))) x y,
        subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
proof -
  have R:
    "Q (if tag_T b = T_VAR then
         (if load_T b = 0 then x
          else if load_T b = 1 then y
          else b)
       else if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using H
    by (rule defI[OF subst_body_def])
  have nvar: "\<not> tag_T b = T_VAR"
    using tg by simp
  have R0:
    "Q (if tag_T b = T_ZERO then b
       else if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nvar R
    by (rule cond_elseQ_E[where c="tag_T b = T_VAR"
            and a="if load_T b = 0 then x
                   else if load_T b = 1 then y
                   else b"])
  have nzero: "\<not> tag_T b = T_ZERO"
    using tg by simp
  have R1:
    "Q (if tag_T b = T_SUC then
         pack_T T_SUC (subst_body (load_T b) x y)
       else if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nzero R0
    by (rule cond_elseQ_E[where c="tag_T b = T_ZERO" and a=b])
  have nsuc: "\<not> tag_T b = T_SUC"
    using tg by simp
  have R2:
    "Q (if tag_T b = T_PRED then
         pack_T T_PRED (subst_body (load_T b) x y)
       else if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using nsuc R1
    by (rule cond_elseQ_E[where c="tag_T b = T_SUC" and a="pack_T T_SUC (subst_body (load_T b) x y)"])
  have npred: "\<not> tag_T b = T_PRED"
    using tg by simp
  have R3:
    "Q (if tag_T b = T_IFZ then
         pack_T T_IFZ
           \<langle>subst_body (cpx (load_T b)) x y,
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
       else
         pack_T T_APP
           \<langle>cpx (load_T b),
            \<langle>subst_body (cpx (cpy (load_T b))) x y,
             subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>)"
    using npred R2
    by (rule cond_elseQ_E[where c="tag_T b = T_PRED" and a="pack_T T_PRED (subst_body (load_T b) x y)"])
  have nifz: "\<not> tag_T b = T_IFZ"
    using tg by simp
  show ?thesis
    using nifz R3
    by (rule cond_elseQ_E[where c="tag_T b = T_IFZ"
            and a="pack_T T_IFZ
              \<langle>subst_body (cpx (load_T b)) x y,
               \<langle>subst_body (cpx (cpy (load_T b))) x y,
                subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>"])
qed

lemma template_instance_sound:
  assumes p: "p N" and i: "i N"
      and a: "a N" and b: "b N"
      and phi: "phi N" and f: "f N"
      and pa: "subst_F p i a = phi"
      and pb: "subst_F p i b = f"
      and sphi: "sat phi A"
      and tr: "\<And>R. R (eval a A) \<Longrightarrow> R (eval b A)"
  shows "sat f A"
proof -
  have saN: "subst_F p i a N"
    by (rule subst_F_N[OF p i a])
  have sbN: "subst_F p i b N"
    by (rule subst_F_N[OF p i b])
  have spa: "sat (subst_F p i a) A"
    using eqSym[OF pa] sphi
    by (rule eqSubst[where Q="\<lambda>q. sat q A"])
  have ia:
    "sat (subst_F p i a) A \<longrightarrow>
     sat p (asn_put A i (eval a A))"
    using sat_subst_F[OF p i a]
    by (rule iffE1)
  have upa: "sat p (asn_put A i (eval a A))"
    using ia spa by (rule implE)
  have upb: "sat p (asn_put A i (eval b A))"
    using upa
    by (rule tr[where R="\<lambda>v. sat p (asn_put A i v)"])
  have ib:
    "sat p (asn_put A i (eval b A)) \<longrightarrow>
     sat (subst_F p i b) A"
    using sat_subst_F[OF p i b]
    by (rule iffE2)
  have spb: "sat (subst_F p i b) A"
    using ib upb by (rule implE)
  show ?thesis
    using pb spb by (rule eqSubst[where Q="\<lambda>q. sat q A"])
qed

lemma check_templateE:
  assumes f: "f N" and phi: "phi N"
      and a: "a N" and b: "b N"
      and p: "p N" and i: "i N"
      and chk: "check_template f phi a b p i"
      and H:
        "\<And>q. q N \<Longrightarrow>
          subst_F q i a = phi \<Longrightarrow>
          subst_F q i b = f \<Longrightarrow> R"
  shows R
proof -
  have main: "check_template f phi a b p i \<turnstile> R"
  proof (rule ind[OF p])
    show "check_template f phi a b 0 i \<turnstile> R"
    proof (rule entailsI)
      assume chk0: "check_template f phi a b 0 i"
      have C0: "if subst_F 0 i a = phi \<and> subst_F 0 i b = f then True
                  else if 0 > 0 = 1 then check_template f phi a b (0 - 1) i
                  else False"
        using chk0
        by (rule defI[OF check_template_def[
              where f=f and phi=phi and a=a and b=b and p=0 and i=i]])
      have C: "if subst_F 0 i a = phi \<and> subst_F 0 i b = f then True else False"
        using C0 by simp
      have sa: "subst_F 0 i a N"
        by (rule subst_F_N[OF nat0 i a])
      have sb: "subst_F 0 i b N"
        by (rule subst_F_N[OF nat0 i b])
      have eaB: "(subst_F 0 i a = phi) B"
        by (rule eqBool[OF sa phi])
      have ebB: "(subst_F 0 i b = f) B"
        by (rule eqBool[OF sb f])
      have bothB: "(subst_F 0 i a = phi \<and> subst_F 0 i b = f) B"
        using eaB ebB by simp
      show R
      proof (rule cases_bool[where q="subst_F 0 i a = phi \<and> subst_F 0 i b = f"])
        show "(subst_F 0 i a = phi \<and> subst_F 0 i b = f) B"
          by (rule bothB)
      next
        assume both: "subst_F 0 i a = phi \<and> subst_F 0 i b = f"
        have ea: "subst_F 0 i a = phi"
          using both by (rule conjE1)
        have eb: "subst_F 0 i b = f"
          using both by (rule conjE2)
        show R
          using nat0 ea eb by (rule H)
      next
        assume nboth: "\<not>(subst_F 0 i a = phi \<and> subst_F 0 i b = f)"
        have F: "False"
          using nboth C by (rule notcond_thenE)
        show R
          by (rule exF[OF F not_false])
      qed
    qed
   next
    fix k
    assume k: "k N"
       and IH: "check_template f phi a b k i \<turnstile> R"
    show "check_template f phi a b (S k) i \<turnstile> R"
    proof (rule entailsI)
      assume chks: "check_template f phi a b (S k) i"
      have C0: "if subst_F (S k) i a = phi \<and> subst_F (S k) i b = f then True
                  else if S k > 0 = 1 then check_template f phi a b (S k - 1) i
                  else False"
        using chks
        by (rule defI[OF check_template_def[where f=f and phi=phi and a=a and b=b and p="S k" and i=i]])
      have sk: "S k N"
        using k by simp
      have gt: "S k > 0 = 1"
        using k by simp
      have sk1: "S k - 1 = k"
        using k by simp
      have sa: "subst_F (S k) i a N"
        by (rule subst_F_N[OF sk i a])
      have sb: "subst_F (S k) i b N"
        by (rule subst_F_N[OF sk i b])
      have eaB: "(subst_F (S k) i a = phi) B"
        by (rule eqBool[OF sa phi])
      have ebB: "(subst_F (S k) i b = f) B"
        by (rule eqBool[OF sb f])
      have bothB: "(subst_F (S k) i a = phi \<and> subst_F (S k) i b = f) B"
        using eaB ebB by simp
      show R
      proof (rule cases_bool[where q="subst_F (S k) i a = phi \<and> subst_F (S k) i b = f"])
        show "(subst_F (S k) i a = phi \<and> subst_F (S k) i b = f) B"
          by (rule bothB)
      next
        assume both: "subst_F (S k) i a = phi \<and> subst_F (S k) i b = f"
        have ea: "subst_F (S k) i a = phi"
          using both by (rule conjE1)
        have eb: "subst_F (S k) i b = f"
          using both by (rule conjE2)
        show R
          using sk ea eb by (rule H)
      next
        assume nboth: "\<not>(subst_F (S k) i a = phi \<and> subst_F (S k) i b = f)"
        have C1: "if S k > 0 = 1 then check_template f phi a b (S k - 1) i else False"
          using nboth C0 by (rule notcond_thenE)
        have chkp: "check_template f phi a b (S k - 1) i"
          using gt C1 by (rule cond_thenE)
        have chkk: "check_template f phi a b k i"
          using sk1 chkp
          by (rule eqSubst[where Q="\<lambda>q. check_template f phi a b q i"])
        show R
          using IH chkk by (rule entailsE)
      qed
    qed
  qed
  show R
    using main chk by (rule entailsE)
qed

lemma sat_formula_eqE:
  assumes f: "f N"
      and tg: "tag_F f = F_EQ"
      and s: "sat f A"
  shows "eval (cpx (load_F f)) A = eval (cpy (load_F f)) A"
proof -
  have C:
    "if tag_F f = F_EQ
     then eval (cpx (load_F f)) A = eval (cpy (load_F f)) A
     else eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A"
    using s unfolding sat_def .
  show ?thesis
    using tg C by (rule cond_thenE)
qed

lemma sat_formula_neqE:
  assumes f: "f N"
      and tg: "\<not> tag_F f = F_EQ"
      and s: "sat f A"
  shows "eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A"
proof -
  have C:
    "if tag_F f = F_EQ
     then eval (cpx (load_F f)) A = eval (cpy (load_F f)) A
     else eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A"
    using s unfolding sat_def .
  show ?thesis
    using tg C by (rule notcond_thenE)
qed

lemma find_phiE:
  assumes J: "J N" and a: "a N" and b: "b N"
      and rest: "rest N" and ptr: "ptr N"
      and sub: "subset ptr rest"
      and fp: "find_phi J a b ptr"
      and H:
        "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
          hyp_of K = hyp_of J \<Longrightarrow>
          check_template (conc_of J) (conc_of K) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1) \<Longrightarrow> R"
  shows R
proof -
  have main: "subset ptr rest \<turnstile> (find_phi J a b ptr \<turnstile> R)"
  proof (rule list_induct[OF ptr])
    show "subset Nil rest \<turnstile> (find_phi J a b Nil \<turnstile> R)"
    proof (rule entailsI)
      assume sub0: "subset Nil rest"
      show "find_phi J a b Nil \<turnstile> R"
      proof (rule entailsI)
        assume fp0: "find_phi J a b Nil"
        have C0: "if Nil = Nil then False
                    else if hyp_of (list_hd Nil) = hyp_of J \<and>
                               check_template (conc_of J) (conc_of (list_hd Nil)) a b
                              (rep_vars_F (conc_of J) (J + 1)) (J + 1)
                    then True
                    else find_phi J a b (list_tl Nil)"
          using fp0
          by (rule defI[OF find_phi_def[
                where J=J and a=a and b=b and ptr=Nil]])
        have F: "False"
          using C0 by simp
        show R
          by (rule exF[OF F not_false])
      qed
    qed
  next
    fix h t
    assume h: "h N"
       and t: "t N"
       and IH: "subset t rest \<turnstile> (find_phi J a b t \<turnstile> R)"
    show "subset (Cons h t) rest \<turnstile> (find_phi J a b (Cons h t) \<turnstile> R)"
    proof (rule entailsI)
      assume subht: "subset (Cons h t) rest"
      have hrest: "mem h rest"
        using h t rest subht by (rule subset_cons_headE)
      have subt: "subset t rest"
        using h t rest subht by (rule subset_cons_tailE)
      show "find_phi J a b (Cons h t) \<turnstile> R"
      proof (rule entailsI)
        assume fpht: "find_phi J a b (Cons h t)"
        have C0: "if Cons h t = Nil then False
                    else if hyp_of (list_hd (Cons h t)) = hyp_of J \<and> 
                                     check_template (conc_of J) (conc_of (list_hd (Cons h t))) a b
                                     (rep_vars_F (conc_of J) (J + 1)) (J + 1)
                    then True
                    else find_phi J a b (list_tl (Cons h t))"
          using fpht
          by (rule defI[OF find_phi_def[
                where J=J and a=a and b=b and ptr="Cons h t"]])
        have C: "if Cons h t = Nil then False
                   else if hyp_of h = hyp_of J \<and> check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1)
                   then True
                   else find_phi J a b t"
          using C0
          by (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
        have ne: "\<not>(Cons h t = Nil)"
          using h t by simp
        have C1: "if hyp_of h = hyp_of J \<and> check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1)
                    then True
                    else find_phi J a b t"
          using ne C by (rule notcond_thenE)
        have cJ: "conc_of J N"
          using J by simp
        have ch: "conc_of h N"
          using h by simp
        have ji: "J + 1 N"
          using J by simp
        have rp: "rep_vars_F (conc_of J) (J + 1) N"
          by (rule rep_vars_F_N[OF cJ ji])
        have eqB: "(hyp_of h = hyp_of J) B"
          using h J by simp
        have ctB: "check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1) B"
          by (rule check_template_bool[OF cJ ch a b ji rp])
        have bothB: "(hyp_of h = hyp_of J \<and> check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1)) B"
          using eqB ctB by simp
        show R
        proof (rule cases_bool[where q="hyp_of h = hyp_of J \<and> check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1)"])
          show "(hyp_of h = hyp_of J \<and>  check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1)) B"
            by (rule bothB)
        next
          assume both: "hyp_of h = hyp_of J \<and> check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1)"
          have heq: "hyp_of h = hyp_of J"
            using both by (rule conjE1)
          have ct: "check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1)"
            using both by (rule conjE2)
          show R
            using h hrest heq ct by (rule H)
        next
          assume nboth: "\<not>(hyp_of h = hyp_of J \<and> check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1))"
          have fpt: "find_phi J a b t"
            using nboth C1 by (rule notcond_thenE)
          have IR: "find_phi J a b t \<turnstile> R"
            using IH subt by (rule entailsE)
          show R
            using IR fpt by (rule entailsE)
        qed
      qed
    qed
  qed
  have IR: "find_phi J a b ptr \<turnstile> R"
    using main sub by (rule entailsE)
  show R
    using IR fp by (rule entailsE)
qed

lemma check_list_induct_N:
  assumes pf: "pf N"
      and base: "\<And>J A. A N \<Longrightarrow> check_list Nil \<Longrightarrow> J N \<Longrightarrow> mem J Nil \<Longrightarrow>
                   sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
      and step: "\<And>h t. h N \<Longrightarrow> t N \<Longrightarrow>
                   (\<And>J A. A N \<Longrightarrow> check_list t \<Longrightarrow> J N \<Longrightarrow> mem J t \<Longrightarrow>
                      sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A) \<Longrightarrow>
                   (\<And>J A. A N \<Longrightarrow> check_list (Cons h t) \<Longrightarrow>
                      J N \<Longrightarrow> mem J (Cons h t) \<Longrightarrow>
                      sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A)"
  shows "\<And>J A. A N \<Longrightarrow> check_list pf \<Longrightarrow> J N \<Longrightarrow> mem J pf \<Longrightarrow>
                sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
proof -
  have all: "\<forall>A. \<forall>K. check_list pf \<turnstile> (mem K pf \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
  proof (rule list_induct[OF pf])
    show "\<forall>A. \<forall>K. check_list Nil \<turnstile> (mem K Nil \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
    proof (rule forallI) 
      fix A
      assume A: "A N"
      show "\<forall>K. check_list Nil \<turnstile> (mem K Nil \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
      proof (rule forallI)
        fix K
        assume K: "K N"
        show "check_list Nil \<turnstile> (mem K Nil \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
        proof (rule entailsI)
          assume chk0: "check_list Nil"
          show "mem K Nil \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A)"
          proof (rule entailsI)
            assume Km: "mem K Nil"
            show "sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A"
            proof (rule entailsI)
              assume satK: "sat_hyp (hyp_of K) A"
              show "sat (conc_of K) A"
                using A chk0 K Km satK by (rule base)
            qed
          qed
        qed
      qed
    qed
  next
    fix h t
    assume h: "h N"
       and t: "t N"
       and IH: "\<forall>A. \<forall>K. check_list t \<turnstile> (mem K t \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
    show "\<forall>A. \<forall>K. check_list (Cons h t) \<turnstile> (mem K (Cons h t) \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
    proof (rule forallI)
      fix A
      assume A: "A N"
      show "\<forall>K. check_list (Cons h t) \<turnstile> (mem K (Cons h t) \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
      proof (rule forallI)
        fix K
        assume K: "K N"
        show "check_list (Cons h t) \<turnstile> (mem K (Cons h t) \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
        proof (rule entailsI)
          assume chkht: "check_list (Cons h t)"
          show "mem K (Cons h t) \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A)"
          proof (rule entailsI)
            assume Km: "mem K (Cons h t)"
            show "sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A"
            proof (rule entailsI)
              assume satK: "sat_hyp (hyp_of K) A"
              have tail:
                "\<And>L A2. A2 N \<Longrightarrow> check_list t \<Longrightarrow> L N \<Longrightarrow> mem L t \<Longrightarrow>
                   sat_hyp (hyp_of L) A2 \<Longrightarrow> sat (conc_of L) A2"
              proof -
                fix L A2
                assume A2: "A2 N"
                   and chkt: "check_list t"
                   and L: "L N"
                   and Lm: "mem L t"
                   and satL: "sat_hyp (hyp_of L) A2"
                have IA:
                  "\<forall>K. check_list t \<turnstile>
                     (mem K t \<turnstile>
                       (sat_hyp (hyp_of K) A2 \<turnstile> sat (conc_of K) A2))"
                  using IH A2 by (rule forallE)
                have LI:
                  "check_list t \<turnstile>
                    (mem L t \<turnstile>
                      (sat_hyp (hyp_of L) A2 \<turnstile> sat (conc_of L) A2))"
                  using IA L by (rule forallE)
                have LI1: "mem L t \<turnstile> (sat_hyp (hyp_of L) A2 \<turnstile> sat (conc_of L) A2)"
                  using LI chkt by (rule entailsE)
                have LI2: "sat_hyp (hyp_of L) A2 \<turnstile> sat (conc_of L) A2"
                  using LI1 Lm by (rule entailsE)
                show "sat (conc_of L) A2"
                  using LI2 satL by (rule entailsE)
              qed
              show "sat (conc_of K) A"
                using h t tail A chkht K Km satK by (rule step)
            qed
          qed
        qed
      qed
    qed
  qed
  fix J A
  assume A: "A N"
     and chk: "check_list pf"
     and J: "J N"
     and Jm: "mem J pf"
     and satG: "sat_hyp (hyp_of J) A"
  have IA: 
    "\<forall>K. check_list pf \<turnstile> (mem K pf \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
    using all A by (rule forallE)
  have one:
    "check_list pf \<turnstile>
      (mem J pf \<turnstile>
        (sat_hyp (hyp_of J) A \<turnstile> sat (conc_of J) A))"
    using IA J by (rule forallE)
  have two:
    "mem J pf \<turnstile>
      (sat_hyp (hyp_of J) A \<turnstile> sat (conc_of J) A)"
    using one chk by (rule entailsE)
  have three:
    "sat_hyp (hyp_of J) A \<turnstile> sat (conc_of J) A"
    using two Jm by (rule entailsE)
  show "sat (conc_of J) A"
    using three satG by (rule entailsE)
qed

lemma check_list_induct:
  assumes pf: "pf N"
      and base: "\<And>J A. check_list Nil \<Longrightarrow> J N \<Longrightarrow> mem J Nil \<Longrightarrow>
                   sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
      and step: "\<And>h t A. h N \<Longrightarrow> t N \<Longrightarrow>
                   (\<And>J. check_list t \<Longrightarrow> J N \<Longrightarrow> mem J t \<Longrightarrow>
                      sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A) \<Longrightarrow>
                   (\<And>J. check_list (Cons h t) \<Longrightarrow> J N \<Longrightarrow>
                      mem J (Cons h t) \<Longrightarrow>
                      sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A)"
  shows "\<And>J A. check_list pf \<Longrightarrow> J N \<Longrightarrow> mem J pf \<Longrightarrow>
                sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
proof -
  fix J A
  assume chk: "check_list pf"
     and J: "J N"
     and Jm: "mem J pf"
     and satG: "sat_hyp (hyp_of J) A"
  have all:
    "\<forall>K. check_list pf \<turnstile> (mem K pf \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
  proof (rule list_induct[OF pf])
    show "\<forall>K. check_list Nil \<turnstile> (mem K Nil \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
    proof (rule forallI)
      fix K
      assume K: "K N"
      show "check_list Nil \<turnstile> (mem K Nil \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
      proof (rule entailsI)
        assume chk0: "check_list Nil"
        show "mem K Nil \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A)"
        proof (rule entailsI)
          assume Km: "mem K Nil"
          show "sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A"
          proof (rule entailsI)
            assume satK: "sat_hyp (hyp_of K) A"
            show "sat (conc_of K) A"
              using chk0 K Km satK by (rule base)
          qed
        qed
      qed
    qed
  next
    fix h t
    assume h: "h N"
       and t: "t N"
       and IH: "\<forall>K. check_list t \<turnstile> (mem K t \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
    show "\<forall>K. check_list (Cons h t) \<turnstile> (mem K (Cons h t) \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
    proof (rule forallI)
      fix K
      assume K: "K N"
      show "check_list (Cons h t) \<turnstile> (mem K (Cons h t) \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
      proof (rule entailsI)
        assume chkht: "check_list (Cons h t)"
        show "mem K (Cons h t) \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A)"
        proof (rule entailsI)
          assume Km: "mem K (Cons h t)"
          show "sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A"
          proof (rule entailsI)
            assume satK: "sat_hyp (hyp_of K) A"
            have tail: "\<And>L. check_list t \<Longrightarrow> L N \<Longrightarrow> mem L t \<Longrightarrow> sat_hyp (hyp_of L) A \<Longrightarrow> sat (conc_of L) A"
            proof -
              fix L
              assume chkt: "check_list t"
                 and L: "L N"
                 and Lm: "mem L t"
                 and satL: "sat_hyp (hyp_of L) A"
              have LI: "check_list t \<turnstile> (mem L t \<turnstile> (sat_hyp (hyp_of L) A \<turnstile> sat (conc_of L) A))"
                using IH L by (rule forallE)
              have LI1: "mem L t \<turnstile> (sat_hyp (hyp_of L) A \<turnstile> sat (conc_of L) A)"
                using LI chkt by (rule entailsE)
              have LI2: "sat_hyp (hyp_of L) A \<turnstile> sat (conc_of L) A"
                using LI1 Lm by (rule entailsE)
              show "sat (conc_of L) A"
                using LI2 satL by (rule entailsE)
            qed
            show "sat (conc_of K) A"
              using h t tail chkht K Km satK
              by (rule step[where A=A])
          qed
        qed
      qed
    qed
  qed
  have one: "check_list pf \<turnstile> (mem J pf \<turnstile> (sat_hyp (hyp_of J) A \<turnstile> sat (conc_of J) A))"
    using all J by (rule forallE)
  have two: "mem J pf \<turnstile> (sat_hyp (hyp_of J) A \<turnstile> sat (conc_of J) A)"
    using one chk by (rule entailsE)
  have three: "sat_hyp (hyp_of J) A \<turnstile> sat (conc_of J) A"
    using two Jm by (rule entailsE)
  show "sat (conc_of J) A"
    using three satG by (rule entailsE)
qed

lemma find_cutE:
  assumes J: "J N" and rest: "rest N" and ptr: "ptr N"
      and sub: "subset ptr rest"
      and fc: "find_cut J rest ptr"
      and H: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   hyp_of K = hyp_of J \<Longrightarrow>
                   mem (conc_of K \<triangleright> hyp_of J \<tturnstile> conc_of J) rest \<Longrightarrow> R"
  shows R
proof -
  have main: "subset ptr rest \<turnstile> (find_cut J rest ptr \<turnstile> R)"
  proof (rule list_induct[OF ptr])
    show "subset Nil rest \<turnstile> (find_cut J rest Nil \<turnstile> R)"
    proof (rule entailsI)
      assume sub0: "subset Nil rest"
      show "find_cut J rest Nil \<turnstile> R"
      proof (rule entailsI)
        assume fc0: "find_cut J rest Nil"
        have C0: "if Nil = Nil then False
                    else if hyp_of (list_hd Nil) = hyp_of J then
                      if mem (conc_of (list_hd Nil) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
                      then True
                      else find_cut J rest (list_tl Nil)
                    else find_cut J rest (list_tl Nil)"
          using fc0
          by (rule defI[OF find_cut_def[where J=J and rest=rest and ptr=Nil]])
        have F: "False"
          using C0 by simp
        show R
          by (rule exF[OF F not_false])
      qed
    qed
  next
    fix h t
    assume h: "h N"
       and t: "t N"
       and IH: "subset t rest \<turnstile> (find_cut J rest t \<turnstile> R)"
    show "subset (Cons h t) rest \<turnstile> (find_cut J rest (Cons h t) \<turnstile> R)"
    proof (rule entailsI)
      assume subht: "subset (Cons h t) rest"
      have hrest: "mem h rest"
        using h t rest subht by (rule subset_cons_headE)
      have subt: "subset t rest"
        using h t rest subht by (rule subset_cons_tailE)
      show "find_cut J rest (Cons h t) \<turnstile> R"
      proof (rule entailsI)
        assume fcht: "find_cut J rest (Cons h t)"
        have C0: "if Cons h t = Nil then False
                    else if hyp_of (list_hd (Cons h t)) = hyp_of J then
                      if mem (conc_of (list_hd (Cons h t)) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
                      then True
                      else find_cut J rest (list_tl (Cons h t))
                    else find_cut J rest (list_tl (Cons h t))"
          using fcht
          by (rule defI[OF find_cut_def[where J=J and rest=rest and ptr="Cons h t"]])
        have C: "if Cons h t = Nil then False
                   else if hyp_of h = hyp_of J then
                     if mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
                     then True
                     else find_cut J rest t
                   else find_cut J rest t"
          using C0
          by (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
        have ne: "\<not> (Cons h t = Nil)"
          using h t by simp
        have C1: "if hyp_of h = hyp_of J then
                    if mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
                    then True
                    else find_cut J rest t
                  else find_cut J rest t"
          using ne C by (rule notcond_thenE)
        have eqB: "(hyp_of h = hyp_of J) B"
          using h J by simp
        show R
        proof (rule cases_bool[where q="hyp_of h = hyp_of J"])
          show "(hyp_of h = hyp_of J) B"
            by (rule eqB)
        next
          assume eq: "hyp_of h = hyp_of J"
          have C2: "if mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
                    then True
                    else find_cut J rest t"
            using eq C1 by (rule cond_thenE)
          have L: "conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J N"
            using h J by simp
          have memB: "mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest B"
            by (rule mem_bool[OF L rest])
          show R
          proof (rule cases_bool[where q="mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest"])
            show "mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest B"
              by (rule memB)
          next
            assume m: "mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest"
            show R
              using h hrest eq m by (rule H)
          next
            assume nm: "\<not> mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest"
            have fct: "find_cut J rest t"
              using nm C2 by (rule notcond_thenE)
            have IR: "find_cut J rest t \<turnstile> R"
              using IH subt by (rule entailsE)
            show R
              using IR fct by (rule entailsE)
          qed
        next
          assume neq: "\<not> (hyp_of h = hyp_of J)"
          have fct: "find_cut J rest t"
            using neq C1 by (rule notcond_thenE)
          have IR: "find_cut J rest t \<turnstile> R"
            using IH subt by (rule entailsE)
          show R
            using IR fct by (rule entailsE)
        qed
      qed
    qed
  qed
  have IR: "find_cut J rest ptr \<turnstile> R"
    using main sub by (rule entailsE)
  show R
    using IR fc by (rule entailsE)
qed

lemma check_cut_sound:
  assumes J: "J N" and rest: "rest N"
      and chk: "check_cut J rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   sat_hyp (hyp_of K) A \<Longrightarrow> sat (conc_of K) A"
      and satG: "sat_hyp (hyp_of J) A"
  shows "sat (conc_of J) A"
proof -
  have fc: "find_cut J rest rest"
    using chk
    by (rule defI[OF check_cut_def[where J=J and rest=rest]])
  have sub: "subset rest rest"
    using rest by (rule subset_refl)
  show ?thesis
  proof (rule find_cutE[OF J rest rest sub fc])
    fix K
    assume K: "K N"
       and Km: "mem K rest"
       and Kh: "hyp_of K = hyp_of J"
       and Lm: "mem (conc_of K \<triangleright> hyp_of J \<tturnstile> conc_of J) rest"
    have hK: "hyp_of J = hyp_of K"
      using Kh by (rule eqSym)
    have satKh: "sat_hyp (hyp_of K) A"
      using hK satG
      by (rule eqSubst[where Q="\<lambda>G. sat_hyp G A"])
    have satK: "sat (conc_of K) A"
      using K Km satKh by (rule prev)
    have cK: "conc_of K N"
      using K by simp
    have hJ: "hyp_of J N"
      using J by simp
    have satCons: "sat_hyp (conc_of K \<triangleright> hyp_of J) A"
      using cK hJ satK satG by (rule sat_hyp_consI)
    let ?L = "conc_of K \<triangleright> hyp_of J \<tturnstile> conc_of J"
    have L: "?L N"
      using K J by simp
    have satLh: "sat_hyp (hyp_of ?L) A"
      using K J satCons by simp
    have satL: "sat (conc_of ?L) A"
      using L Lm satLh by (rule prev)
    show "sat (conc_of J) A"
      using K J satL by simp
  qed
qed

lemma find_eqE:
  assumes J: "J N" and rest: "rest N" and ptr: "ptr N"
      and sub: "subset ptr rest"
      and fe: "find_eq J rest ptr"
      and H: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   hyp_of K = hyp_of J \<Longrightarrow>
                   tag_F (conc_of K) = F_EQ \<Longrightarrow>
                   find_phi J
                     (cpx (load_F (conc_of K)))
                     (cpy (load_F (conc_of K))) rest \<Longrightarrow> R"
  shows R
proof -
  have main: "subset ptr rest \<turnstile> (find_eq J rest ptr \<turnstile> R)"
  proof (rule list_induct[OF ptr])
    show "subset Nil rest \<turnstile> (find_eq J rest Nil \<turnstile> R)"
    proof (rule entailsI)
      assume sub0: "subset Nil rest"
      show "find_eq J rest Nil \<turnstile> R"
      proof (rule entailsI)
        assume fe0: "find_eq J rest Nil"
        have C0: "if Nil = Nil then False
                    else if hyp_of (list_hd Nil) = hyp_of J \<and>
                            tag_F (conc_of (list_hd Nil)) = F_EQ then
                      if find_phi J
                           (cpx (load_F (conc_of (list_hd Nil))))
                           (cpy (load_F (conc_of (list_hd Nil)))) rest
                      then True
                      else find_eq J rest (list_tl Nil)
                    else find_eq J rest (list_tl Nil)"
          using fe0
          by (rule defI[OF find_eq_def[where J=J and rest=rest and ptr=Nil]])
        have F: "False"
          using C0 by simp
        show R
          by (rule exF[OF F not_false])
      qed
    qed
  next
    fix h t
    assume h: "h N"
       and t: "t N"
       and IH: "subset t rest \<turnstile> (find_eq J rest t \<turnstile> R)"
    show "subset (Cons h t) rest \<turnstile> (find_eq J rest (Cons h t) \<turnstile> R)"
    proof (rule entailsI)
      assume subht: "subset (Cons h t) rest"
      have hrest: "mem h rest"
        using h t rest subht by (rule subset_cons_headE)
      have subt: "subset t rest"
        using h t rest subht by (rule subset_cons_tailE)
      show "find_eq J rest (Cons h t) \<turnstile> R"
      proof (rule entailsI)
        assume feht: "find_eq J rest (Cons h t)"
        have C0: "if Cons h t = Nil then False
                    else if hyp_of (list_hd (Cons h t)) = hyp_of J \<and>
                            tag_F (conc_of (list_hd (Cons h t))) = F_EQ then
                      if find_phi J
                           (cpx (load_F (conc_of (list_hd (Cons h t)))))
                           (cpy (load_F (conc_of (list_hd (Cons h t))))) rest
                      then True
                      else find_eq J rest (list_tl (Cons h t))
                    else find_eq J rest (list_tl (Cons h t))"
          using feht
          by (rule defI[OF find_eq_def[where J=J and rest=rest and ptr="Cons h t"]])
        have C: "if Cons h t = Nil then False
                   else if hyp_of h = hyp_of J \<and>
                           tag_F (conc_of h) = F_EQ then
                     if find_phi J
                          (cpx (load_F (conc_of h)))
                          (cpy (load_F (conc_of h))) rest
                     then True
                     else find_eq J rest t
                   else find_eq J rest t"
          using C0
          by (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
        have ne: "\<not> (Cons h t = Nil)"
          using h t by simp
        have C1: "if hyp_of h = hyp_of J \<and>
                          tag_F (conc_of h) = F_EQ then
                    if find_phi J
                         (cpx (load_F (conc_of h)))
                         (cpy (load_F (conc_of h))) rest
                    then True
                    else find_eq J rest t
                  else find_eq J rest t"
          using ne C by (rule notcond_thenE)
        have ch: "conc_of h N"
          using h by simp
        have eqhB: "(hyp_of h = hyp_of J) B"
          using h J by simp
        have tgh: "tag_F (conc_of h) N"
          using ch by (rule tag_F_N)
        have feq: "F_EQ N"
          by simp
        have eqtgB: "(tag_F (conc_of h) = F_EQ) B"
          by (rule eqBool[OF tgh feq])
        have bothB: "(hyp_of h = hyp_of J \<and> tag_F (conc_of h) = F_EQ) B"
          using eqhB eqtgB by simp
        show R
        proof (rule cases_bool[where q="hyp_of h = hyp_of J \<and> tag_F (conc_of h) = F_EQ"])
          show "(hyp_of h = hyp_of J \<and> tag_F (conc_of h) = F_EQ) B"
            by (rule bothB)
        next
          assume both: "hyp_of h = hyp_of J \<and> tag_F (conc_of h) = F_EQ"
          have heq: "hyp_of h = hyp_of J"
            using both by (rule conjE1)
          have htg: "tag_F (conc_of h) = F_EQ"
            using both by (rule conjE2)
          have C2: "if find_phi J
                         (cpx (load_F (conc_of h)))
                         (cpy (load_F (conc_of h))) rest
                    then True
                    else find_eq J rest t"
            using both C1 by (rule cond_thenE)
          have lh: "load_F (conc_of h) N"
            using ch by (rule load_F_N)
          have ah: "cpx (load_F (conc_of h)) N"
            using lh by (rule cpx_terminates)
          have bh: "cpy (load_F (conc_of h)) N"
            using lh by (rule cpy_terminates)
          have fpB: "find_phi J
                       (cpx (load_F (conc_of h)))
                       (cpy (load_F (conc_of h))) rest B"
            by (rule find_phi_bool[OF J ah bh rest])
          show R
          proof (rule cases_bool[where q="find_phi J
                      (cpx (load_F (conc_of h)))
                      (cpy (load_F (conc_of h))) rest"])
            show "find_phi J
                    (cpx (load_F (conc_of h)))
                    (cpy (load_F (conc_of h))) rest B"
              by (rule fpB)
          next
            assume fp: "find_phi J
                          (cpx (load_F (conc_of h)))
                          (cpy (load_F (conc_of h))) rest"
            show R
              using h hrest heq htg fp by (rule H)
          next
            assume nfp: "\<not> find_phi J
                           (cpx (load_F (conc_of h)))
                           (cpy (load_F (conc_of h))) rest"
            have fet: "find_eq J rest t"
              using nfp C2 by (rule notcond_thenE)
            have IR: "find_eq J rest t \<turnstile> R"
              using IH subt by (rule entailsE)
            show R
              using IR fet by (rule entailsE)
          qed
        next
          assume nboth: "\<not> (hyp_of h = hyp_of J \<and> tag_F (conc_of h) = F_EQ)"
          have fet: "find_eq J rest t"
            using nboth C1 by (rule notcond_thenE)
          have IR: "find_eq J rest t \<turnstile> R"
            using IH subt by (rule entailsE)
          show R
            using IR fet by (rule entailsE)
        qed
      qed
    qed
  qed
  have IR: "find_eq J rest ptr \<turnstile> R"
    using main sub by (rule entailsE)
  show R
    using IR fe by (rule entailsE)
qed

lemma check_subst_sound:
  assumes J: "J N" and rest: "rest N"
      and chk: "check_subst J rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   sat_hyp (hyp_of K) A \<Longrightarrow> sat (conc_of K) A"
      and satG: "sat_hyp (hyp_of J) A"
  shows "sat (conc_of J) A"
proof -
  have fe: "find_eq J rest rest"
    using chk
    by (rule defI[OF check_subst_def[where J=J and rest=rest]])
  have sub: "subset rest rest"
    using rest by (rule subset_refl)
  show ?thesis
  proof (rule find_eqE[OF J rest rest sub fe])
    fix K
    assume K: "K N"
       and Km: "mem K rest"
       and Kh: "hyp_of K = hyp_of J"
       and Ktg: "tag_F (conc_of K) = F_EQ"
       and fp: "find_phi J
                  (cpx (load_F (conc_of K)))
                  (cpy (load_F (conc_of K))) rest"
    let ?a = "cpx (load_F (conc_of K))"
    let ?b = "cpy (load_F (conc_of K))"
    have cK: "conc_of K N"
      using K by simp
    have lK: "load_F (conc_of K) N"
      using cK by (rule load_F_N)
    have a: "?a N"
      using lK by (rule cpx_terminates)
    have b: "?b N"
      using lK by (rule cpy_terminates)
    have hK: "hyp_of J = hyp_of K"
      using Kh by (rule eqSym)
    have satKh: "sat_hyp (hyp_of K) A"
      using hK satG
      by (rule eqSubst[where Q="\<lambda>G. sat_hyp G A"])
    have satK: "sat (conc_of K) A"
      using K Km satKh by (rule prev)
    have ab: "eval ?a A = eval ?b A"
      using cK Ktg satK by (rule sat_formula_eqE)
    have sub': "subset rest rest"
      using rest by (rule subset_refl)
    show "sat (conc_of J) A"
    proof (rule find_phiE[OF J a b rest rest sub' fp])
      fix L
      assume L: "L N"
         and Lm: "mem L rest"
         and Lh: "hyp_of L = hyp_of J"
         and ct: "check_template (conc_of J) (conc_of L) ?a ?b
                    (rep_vars_F (conc_of J) (J + 1)) (J + 1)"
      have cJ: "conc_of J N"
        using J by simp
      have cL: "conc_of L N"
        using L by simp
      have i: "J + 1 N"
        using J by simp
      have p: "rep_vars_F (conc_of J) (J + 1) N"
        using cJ i by (rule rep_vars_F_N)
      have hL: "hyp_of J = hyp_of L"
        using Lh by (rule eqSym)
      have satLh: "sat_hyp (hyp_of L) A"
        using hL satG
        by (rule eqSubst[where Q="\<lambda>G. sat_hyp G A"])
      have satL: "sat (conc_of L) A"
        using L Lm satLh by (rule prev)
      show "sat (conc_of J) A"
      proof (rule check_templateE[OF cJ cL a b p i ct])
        fix q
        assume q: "q N"
           and qa: "subst_F q (J + 1) ?a = conc_of L"
           and qb: "subst_F q (J + 1) ?b = conc_of J"
        have tr: "\<And>R. R (eval ?a A) \<Longrightarrow> R (eval ?b A)"
        proof -
          fix R
          assume Ra: "R (eval ?a A)"
          show "R (eval ?b A)"
            using ab Ra by (rule eqSubst)
        qed
        show "sat (conc_of J) A"
          using q i a b cL cJ qa qb satL tr
          by (rule template_instance_sound)
      qed
    qed
  qed
qed

lemma check_ind_templateE:
  assumes f: "f N" and phi: "phi N"
      and a: "a N" and G: "G N"
      and p: "p N" and i: "i N"
      and rest: "rest N"
      and chk: "check_ind_template f phi a G p i rest"
      and H: "\<And>q. q N \<Longrightarrow> subst_F q i a = f \<Longrightarrow> subst_F q i (pack_T T_ZERO 0) = phi \<Longrightarrow>
          mem (pack_F F_EQ \<langle>pack_T T_VAR i, pack_T T_VAR i\<rangle> \<triangleright> q \<triangleright> G \<tturnstile> subst_F q i (pack_T T_SUC (pack_T T_VAR i))) rest \<Longrightarrow> R"
  shows R
proof -
  let ?z = "pack_T T_ZERO 0"
  let ?vi = "pack_T T_VAR i"
  let ?svi = "pack_T T_SUC ?vi"
  have zN: "?z N"
    by (rule pack_T_N[OF _ nat0], simp)
  have main:
    "check_ind_template f phi a G p i rest \<turnstile> R"
  proof (rule ind[OF p])
    show "check_ind_template f phi a G 0 i rest \<turnstile> R"
    proof (rule entailsI)
      assume chk0: "check_ind_template f phi a G 0 i rest"
      have C0:
        "if subst_F 0 i a = f \<and>subst_F 0 i ?z = phi \<and>
            mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G \<tturnstile> subst_F 0 i ?svi) rest
         then True
         else if 0 > 0 = 1
         then check_ind_template f phi a G (0 - 1) i rest
         else False"
        using chk0
        by (rule defI[OF check_ind_template_def[
          where f=f and phi=phi and a=a and G=G
            and p=0 and i=i and rest=rest]])
      have C: "if subst_F 0 i a = f \<and> subst_F 0 i ?z = phi \<and> mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G \<tturnstile> subst_F 0 i ?svi) rest
         then True
         else False"
        using C0 by simp
      have sa: "subst_F 0 i a N"
        by (rule subst_F_N[OF nat0 i a])
      have sz: "subst_F 0 i ?z N"
        by (rule subst_F_N[OF nat0 i zN])
      have sj:
        "(pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G \<tturnstile> subst_F 0 i ?svi) N"
        by (rule ind_jdg_N[OF nat0 G i])
      have eaB: "(subst_F 0 i a = f) B"
        by (rule eqBool[OF sa f])
      have ezB: "(subst_F 0 i ?z = phi) B"
        by (rule eqBool[OF sz phi])
      have emB:
        "mem
          (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G
           \<tturnstile> subst_F 0 i ?svi)
          rest B"
        by (rule mem_bool[OF sj rest])
      have allB:
        "(subst_F 0 i a = f \<and>
          subst_F 0 i ?z = phi \<and>
          mem
            (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G
             \<tturnstile> subst_F 0 i ?svi)
            rest) B"
        using eaB ezB emB by auto
      show R
      proof (rule cases_bool[
        where q="subst_F 0 i a = f \<and>
          subst_F 0 i ?z = phi \<and>
          mem
            (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G
             \<tturnstile> subst_F 0 i ?svi)
            rest"])
        show
          "(subst_F 0 i a = f \<and>
            subst_F 0 i ?z = phi \<and>
            mem
              (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G
               \<tturnstile> subst_F 0 i ?svi)
              rest) B"
          by (rule allB)
      next
        assume all:
          "subst_F 0 i a = f \<and>
           subst_F 0 i ?z = phi \<and>
           mem
             (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G
              \<tturnstile> subst_F 0 i ?svi)
             rest"
                have left:
          "subst_F 0 i a = f \<and>
           subst_F 0 i ?z = phi"
          using all by (rule conjE1)
        have qa: "subst_F 0 i a = f"
          using left by (rule conjE1)
        have qz: "subst_F 0 i ?z = phi"
          using left by (rule conjE2)
        have qm:
          "mem
            (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G
             \<tturnstile> subst_F 0 i ?svi)
            rest"
          using all by (rule conjE2)
        show R
          using nat0 qa qz qm by (rule H)
      next
        assume nall: "\<not>(subst_F 0 i a = f \<and> subst_F 0 i ?z = phi \<and> mem
               (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G
                \<tturnstile> subst_F 0 i ?svi)
               rest)"
        have F: "False"
          using nall C by (rule notcond_thenE)
        show R
          by (rule exF[OF F not_false])
      qed
    qed
  next
    fix k
    assume k: "k N"
       and IH: "check_ind_template f phi a G k i rest \<turnstile> R"
    show "check_ind_template f phi a G (S k) i rest \<turnstile> R"
    proof (rule entailsI)
      assume chks:
        "check_ind_template f phi a G (S k) i rest"
      have C0:
        "if subst_F (S k) i a = f \<and>
            subst_F (S k) i ?z = phi \<and>
            mem
              (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G
               \<tturnstile> subst_F (S k) i ?svi)
              rest
         then True
         else if S k > 0 = 1
         then check_ind_template
                f phi a G (S k - 1) i rest
         else False"
        using chks
        by (rule defI[OF check_ind_template_def[
          where f=f and phi=phi and a=a and G=G
            and p="S k" and i=i and rest=rest]])
      have sk: "S k N"
        using k by simp
      have gt: "S k > 0 = 1"
        using k by simp
      have sk1: "S k - 1 = k"
        using k by simp
      have sa: "subst_F (S k) i a N"
        by (rule subst_F_N[OF sk i a])
      have sz: "subst_F (S k) i ?z N"
        by (rule subst_F_N[OF sk i zN])
      have sj:
        "(pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G
          \<tturnstile> subst_F (S k) i ?svi) N"
        by (rule ind_jdg_N[OF sk G i])
      have eaB: "(subst_F (S k) i a = f) B"
        by (rule eqBool[OF sa f])
      have ezB: "(subst_F (S k) i ?z = phi) B"
        by (rule eqBool[OF sz phi])
      have emB: "mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G \<tturnstile> subst_F (S k) i ?svi) rest B"
        by (rule mem_bool[OF sj rest])
      have allB: "(subst_F (S k) i a = f \<and> subst_F (S k) i ?z = phi \<and> mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G \<tturnstile> subst_F (S k) i ?svi) rest) B"
        using eaB ezB emB by auto
      show R
      proof (rule cases_bool[
        where q="subst_F (S k) i a = f \<and>
          subst_F (S k) i ?z = phi \<and>
          mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G \<tturnstile> subst_F (S k) i ?svi) rest"])
        show
          "(subst_F (S k) i a = f \<and>
            subst_F (S k) i ?z = phi \<and>
            mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G \<tturnstile> subst_F (S k) i ?svi) rest) B"
          by (rule allB)
      next
        assume all:
          "subst_F (S k) i a = f \<and>
           subst_F (S k) i ?z = phi \<and>
           mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G \<tturnstile> subst_F (S k) i ?svi) rest"
        have left:
          "subst_F (S k) i a = f \<and>
           subst_F (S k) i ?z = phi"
          using all by (rule conjE1)
        have qa: "subst_F (S k) i a = f"
          using left by (rule conjE1)
        have qz: "subst_F (S k) i ?z = phi"
          using left by (rule conjE2)
        have qm:
          "mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G \<tturnstile> subst_F (S k) i ?svi) rest"
          using all by (rule conjE2)
        show R
          using sk qa qz qm by (rule H)
      next
        assume nall:
          "\<not>(subst_F (S k) i a = f \<and> subst_F (S k) i ?z = phi \<and> mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G \<tturnstile> subst_F (S k) i ?svi) rest)"
        have C1:
          "if S k > 0 = 1
           then check_ind_template
                  f phi a G (S k - 1) i rest
           else False"
          using nall C0 by (rule notcond_thenE)
        have chkp:
          "check_ind_template f phi a G (S k - 1) i rest"
          using gt C1 by (rule cond_thenE)
        have chkk:
          "check_ind_template f phi a G k i rest"
          using sk1 chkp
          by (rule eqSubst[
            where Q="\<lambda>q. check_ind_template f phi a G q i rest"])
        show R
          using IH chkk by (rule entailsE)
      qed
    qed
  qed
  show R
    using main chk by (rule entailsE)
qed

lemma find_ind_baseE:
  assumes J: "J N" and a: "a N"
      and rest: "rest N" and ptr: "ptr N"
      and sub: "subset ptr rest"
      and fib: "find_ind_base J a rest ptr"
      and H:
        "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
          hyp_of K = hyp_of J \<Longrightarrow>
          check_ind_template
            (conc_of J) (conc_of K) a (hyp_of J)
            (rep_vars_F (conc_of J) (J + 1))
            (J + 1) rest \<Longrightarrow> R"
  shows R
proof -
  have main:
    "subset ptr rest \<turnstile> (find_ind_base J a rest ptr \<turnstile> R)"
  proof (rule list_induct[OF ptr])
    show
      "subset Nil rest \<turnstile>
       (find_ind_base J a rest Nil \<turnstile> R)"
    proof (rule entailsI)
      assume sub0: "subset Nil rest"
      show "find_ind_base J a rest Nil \<turnstile> R"
      proof (rule entailsI)
        assume fib0: "find_ind_base J a rest Nil"
        have C0:
          "if Nil = Nil then False
           else if hyp_of (list_hd Nil) = hyp_of J then
             if check_ind_template
                  (conc_of J) (conc_of (list_hd Nil))
                  a (hyp_of J)
                  (rep_vars_F (conc_of J) (J + 1))
                  (J + 1) rest
             then True
             else find_ind_base J a rest (list_tl Nil)
           else find_ind_base J a rest (list_tl Nil)"
          using fib0
          by (rule defI[OF find_ind_base_def[
            where J=J and a=a and rest=rest and ptr=Nil]])
        have F: "False"
          using C0 by simp
        show R
          by (rule exF[OF F not_false])
      qed
    qed
  next
    fix h t
    assume h: "h N"
       and t: "t N"
       and IH:
         "subset t rest \<turnstile>
          (find_ind_base J a rest t \<turnstile> R)"
    show
      "subset (Cons h t) rest \<turnstile>
       (find_ind_base J a rest (Cons h t) \<turnstile> R)"
    proof (rule entailsI)
      assume subht: "subset (Cons h t) rest"
      have hrest: "mem h rest"
        using h t rest subht by (rule subset_cons_headE)
      have subt: "subset t rest"
        using h t rest subht by (rule subset_cons_tailE)
      show "find_ind_base J a rest (Cons h t) \<turnstile> R"
      proof (rule entailsI)
        assume fibht:
          "find_ind_base J a rest (Cons h t)"
        have C0:
          "if Cons h t = Nil then False
           else if
             hyp_of (list_hd (Cons h t)) = hyp_of J
           then
             if check_ind_template (conc_of J) (conc_of (list_hd (Cons h t)))
                  a (hyp_of J) (rep_vars_F (conc_of J) (J + 1)) (J + 1) rest
             then True
             else find_ind_base J a rest (list_tl (Cons h t))
           else find_ind_base J a rest
                  (list_tl (Cons h t))"
          using fibht
          by (rule defI[OF find_ind_base_def[
            where J=J and a=a and rest=rest
              and ptr="Cons h t"]])
        have C:
          "if Cons h t = Nil then False
           else if hyp_of h = hyp_of J then
             if check_ind_template
                  (conc_of J) (conc_of h) a (hyp_of J)
                  (rep_vars_F (conc_of J) (J + 1))
                  (J + 1) rest
             then True
             else find_ind_base J a rest t
           else find_ind_base J a rest t"
          using C0
          by (simp only:
            list_hd_cons[OF h t] list_tl_cons[OF h t])
        have ne: "\<not> Cons h t = Nil"
          using h t by simp
        have C1:
          "if hyp_of h = hyp_of J then
             if check_ind_template
                  (conc_of J) (conc_of h) a (hyp_of J)
                  (rep_vars_F (conc_of J) (J + 1))
                  (J + 1) rest
             then True
             else find_ind_base J a rest t
           else find_ind_base J a rest t"
          using ne C by (rule notcond_thenE)
        have cJ: "conc_of J N"
          using J by simp
        have ch: "conc_of h N"
          using h by simp
        have hJ: "hyp_of J N"
          using J by simp
        have i: "J + 1 N"
          using J by simp
        have p:
          "rep_vars_F (conc_of J) (J + 1) N"
          by (rule rep_vars_F_N[OF cJ i])
        have eqB: "(hyp_of h = hyp_of J) B"
          using h J by simp
        have ctB:
          "check_ind_template
            (conc_of J) (conc_of h) a (hyp_of J)
            (rep_vars_F (conc_of J) (J + 1))
            (J + 1) rest B"
          by (rule check_ind_template_bool[
            OF cJ ch a hJ p i rest])
        show R
        proof (rule cases_bool[
          where q="hyp_of h = hyp_of J"])
          show "(hyp_of h = hyp_of J) B"
            by (rule eqB)
        next
          assume heq: "hyp_of h = hyp_of J"
          have C2:
            "if check_ind_template
                 (conc_of J) (conc_of h) a (hyp_of J)
                 (rep_vars_F (conc_of J) (J + 1))
                 (J + 1) rest
             then True
             else find_ind_base J a rest t"
            using heq C1 by (rule cond_thenE)
          show R
          proof (rule cases_bool[
            where q="check_ind_template
              (conc_of J) (conc_of h) a (hyp_of J)
              (rep_vars_F (conc_of J) (J + 1))
              (J + 1) rest"])
            show
              "check_ind_template
                (conc_of J) (conc_of h) a (hyp_of J)
                (rep_vars_F (conc_of J) (J + 1))
                (J + 1) rest B"
              by (rule ctB)
          next
            assume ct:
              "check_ind_template
                (conc_of J) (conc_of h) a (hyp_of J)
                (rep_vars_F (conc_of J) (J + 1))
                (J + 1) rest"
            show R
              using h hrest heq ct by (rule H)
          next
            assume nct:
              "\<not> check_ind_template
                   (conc_of J) (conc_of h) a (hyp_of J)
                   (rep_vars_F (conc_of J) (J + 1))
                   (J + 1) rest"
            have fibt: "find_ind_base J a rest t"
              using nct C2 by (rule notcond_thenE)
            have IR: "find_ind_base J a rest t \<turnstile> R"
              using IH subt by (rule entailsE)
            show R
              using IR fibt by (rule entailsE)
          qed
        next
          assume nheq: "\<not> hyp_of h = hyp_of J"
          have fibt: "find_ind_base J a rest t"
            using nheq C1 by (rule notcond_thenE)
          have IR: "find_ind_base J a rest t \<turnstile> R"
            using IH subt by (rule entailsE)
          show R
            using IR fibt by (rule entailsE)
        qed
      qed
    qed
  qed
  have IR: "find_ind_base J a rest ptr \<turnstile> R"
    using main sub by (rule entailsE)
  show R
    using IR fib by (rule entailsE)
qed

lemma check_ind_sound:
  assumes J: "J N" and rest: "rest N"
      and chk: "check_ind J rest"
      and prev:
        "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
          sat_hyp (hyp_of K) A \<Longrightarrow> sat (conc_of K) A"
      and prevN:
        "\<And>K A2. A2 N \<Longrightarrow> K N \<Longrightarrow> mem K rest \<Longrightarrow>
          sat_hyp (hyp_of K) A2 \<Longrightarrow> sat (conc_of K) A2"
      and satG: "sat_hyp (hyp_of J) A"
      and AN: "A N"
  shows "sat (conc_of J) A"
proof -
  let ?f = "conc_of J"
  let ?G = "hyp_of J"
  let ?a = "cpx (load_F ?f)"
  let ?i = "J + 1"
  let ?p = "rep_vars_F ?f ?i"
  let ?z = "pack_T T_ZERO 0"
  let ?vi = "pack_T T_VAR ?i"
  let ?svi = "pack_T T_SUC ?vi"
  let ?eqaa = "pack_F F_EQ \<langle>?a, ?a\<rangle>"
  let ?Qa = "?G \<tturnstile> ?eqaa"
  have f: "?f N"
    using J by simp
  have G: "?G N"
    using J by simp
  have lf: "load_F ?f N"
    using f by (rule load_F_N)
  have a: "?a N"
    using lf by (rule cpx_terminates)
  have i: "?i N"
    using J by simp
  have p: "?p N"
    by (rule rep_vars_F_N[OF f i])
  have aa: "\<langle>?a, ?a\<rangle> N"
    using a by simp
  have eqaa: "?eqaa N"
    by (rule pack_F_N[OF _ aa], simp)
  have Qa: "?Qa N"
    using G eqaa by simp
  have memB: "mem ?Qa rest B"
    by (rule mem_bool[OF Qa rest])
  have freshB: "fresh_H ?i ?G B"
    by (rule fresh_H_bool[OF i G])
  have guardB:
    "(fresh_H ?i ?G \<and> mem ?Qa rest) B"
    using freshB memB by auto
  have C0:
    "if fresh_H ?i ?G \<and> mem ?Qa rest
     then find_ind_base J ?a rest rest
     else False"
    using chk
    by (rule defI[OF check_ind_def[
      where J=J and rest=rest]])
  have guard:
    "fresh_H ?i ?G \<and> mem ?Qa rest"
  proof (rule cases_bool[
    where q="fresh_H ?i ?G \<and> mem ?Qa rest"])
    show "(fresh_H ?i ?G \<and> mem ?Qa rest) B"
      by (rule guardB)
  next
    assume g: "fresh_H ?i ?G \<and> mem ?Qa rest"
    show "fresh_H ?i ?G \<and> mem ?Qa rest"
      by (rule g)
  next
    assume ng: "\<not>(fresh_H ?i ?G \<and> mem ?Qa rest)"
    have F: "False"
      using ng C0 by (rule notcond_thenE)
    show "fresh_H ?i ?G \<and> mem ?Qa rest"
      by (rule exF[OF F not_false])
  qed
  have fresh: "fresh_H ?i ?G"
    using guard by (rule conjE1)
  have mQa: "mem ?Qa rest"
    using guard by (rule conjE2)
  have fib: "find_ind_base J ?a rest rest"
    using guard C0 by (rule cond_thenE)
  have QaN: "?Qa N"
    using G eqaa by simp
  have QaG: "sat_hyp (hyp_of ?Qa) A"
    using G eqaa satG by simp
  have satQa0: "sat (conc_of ?Qa) A"
    using QaN mQa QaG
    by (rule prev[where K="?Qa"])
have satQa: "sat ?eqaa A"
  using G eqaa satQa0 by simp
  have tgEq: "tag_F ?eqaa = F_EQ"
    by (rule tag_pack_F[OF _ aa], simp)
  have ldEq: "load_F ?eqaa = \<langle>?a, ?a\<rangle>"
    by (rule load_pack_F[OF _ aa], simp)
  have evalEq0:
    "eval (cpx (load_F ?eqaa)) A =
     eval (cpy (load_F ?eqaa)) A"
    using eqaa tgEq satQa by (rule sat_formula_eqE)
  have evalEq: "eval ?a A = eval ?a A"
    using evalEq0 a by (simp add: ldEq)
  have an: "eval ?a A N"
    using evalEq by (rule eq_impl_term2)
  have sub: "subset rest rest"
    using rest by (rule subset_refl)
  show "sat ?f A"
  proof (rule find_ind_baseE[
    OF J a rest rest sub fib])
    fix K
    assume K: "K N"
       and Km: "mem K rest"
       and Kh: "hyp_of K = ?G"
       and ct: "check_ind_template ?f (conc_of K) ?a ?G ?p ?i rest"
    have cK: "conc_of K N"
      using K by simp
    have hK: "?G = hyp_of K"
      using Kh by (rule eqSym)
    have satKh: "sat_hyp (hyp_of K) A"
      using hK satG
      by (rule eqSubst[where Q="\<lambda>H. sat_hyp H A"])
    have satK: "sat (conc_of K) A"
      using K Km satKh by (rule prev)
    show "sat ?f A"
    proof (rule check_ind_templateE[
      OF f cK a G p i rest ct])
      fix q
      assume q: "q N"
         and qa: "subst_F q ?i ?a = ?f"
         and qz: "subst_F q ?i ?z = conc_of K"
         and qm: "mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> q \<triangleright> ?G \<tturnstile> subst_F q ?i ?svi) rest"
      have qz': "conc_of K = subst_F q ?i ?z"
        using qz by (rule eqSym)
      have base:
        "sat (subst_F q ?i ?z) A"
        using qz' satK by (rule eqSubst[where Q="\<lambda>r. sat r A"])
      have step:
        "\<And>m. m N \<Longrightarrow> sat_hyp (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> q \<triangleright> ?G) (asn_put A ?i m) \<Longrightarrow>
          sat (subst_F q ?i ?svi) (asn_put A ?i m)"
            proof -
        fix m
        assume m: "m N"
           and satStep:
             "sat_hyp
               (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> q \<triangleright> ?G)
               (asn_put A ?i m)"
        let ?H = "pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> q \<triangleright> ?G"
        let ?C = "subst_F q ?i ?svi"
        let ?K = "?H \<tturnstile> ?C"
        let ?Am = "asn_put A ?i m"
        have vi: "?vi N"
          by (rule pack_T_N[OF _ i], simp)
        have svi: "?svi N"
          by (rule pack_T_N[OF _ vi], simp)
        have vv: "\<langle>?vi, ?vi\<rangle> N"
          using vi by simp
        have eqv: "pack_F F_EQ \<langle>?vi, ?vi\<rangle> N"
          by (rule pack_F_N[OF _ vv], simp)
        have qG: "q \<triangleright> ?G N"
          using q G by simp
        have HN: "?H N"
          using eqv qG by simp
        have CN: "?C N"
          by (rule subst_F_N[OF q i svi])
        have KN: "?K N"
          using HN CN by simp
        have Am: "?Am N"
          using AN i m by (rule asn_put_N)
        have hp: "hyp_of ?K = ?H"
          by (rule cpx_proj[OF HN CN])
        have hp': "?H = hyp_of ?K"
          using hp by (rule eqSym)
        have satKh: "sat_hyp (hyp_of ?K) ?Am"
          using hp' satStep
          by (rule eqSubst[where Q="\<lambda>H. sat_hyp H ?Am"])
        have satK: "sat (conc_of ?K) ?Am"
        proof (rule prevN[where K="?K"])
          show "?Am N"
            by (rule Am)
        next
          show "?K N"
            by (rule KN)
        next
          show "?K \<in> rest"
            by (rule qm)
        next
          show "sat_hyp (hyp_of ?K) ?Am"
            by (rule satKh)
        qed
        have cp: "conc_of ?K = ?C"
          by (rule cpy_proj[OF HN CN])
        show "sat ?C ?Am"
          using cp satK
          by (rule eqSubst[where Q="\<lambda>f. sat f ?Am"])
      qed
      have sq: "sat (subst_F q ?i ?a) A"
        using q i a G fresh satG base step an AN
        by (rule nat_ind_sound_put)
      show "sat ?f A"
        using qa sq
        by (rule eqSubst[where Q="\<lambda>r. sat r A"])
    qed
  qed
qed

lemma subst_T_var_same:
  assumes t: "t N" and i: "i N" and s: "s N" and tg: "tag_T t = T_VAR" and ld: "load_T t = i"
  shows "subst_T t i s = s"
proof -
  have ss: "s = s"
    using s by simp
  have inner: "(if load_T t = i then s else t) = s"
    by (rule condI1Eq[OF ld s ss])
  show ?thesis
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI1Eq[OF tg s inner])
    done
qed

lemma subst_T_var_other:
  assumes t: "t N" and i: "i N" and s: "s N" and tg: "tag_T t = T_VAR" and ld: "\<not> load_T t = i"
  shows "subst_T t i s = t"
proof -
  have inner: "(if load_T t = i then s else t) = t"
    apply (rule condI2Eq[OF ld t])
    using t apply simp
    done
  show ?thesis
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI1Eq[OF tg t inner])
    done
qed

lemma eval_subst_T_var:
  assumes t: "t N" and i: "i N" and s: "s N" and A: "A N" and es: "eval s A N" and tg: "tag_T t = T_VAR"
  shows "eval (subst_T t i s) A = eval t (asn_put A i (eval s A))"
proof (rule cases_bool[where q="load_T t = i"])
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  show "(load_T t = i) B"
    by (rule eqBool[OF loadN i])
next
  assume li: "load_T t = i"
  have sub: "subst_T t i s = s"
    by (rule subst_T_var_same[OF t i s tg li])
  have nth_i: "nth i (asn_put A i (eval s A)) = eval s A"
    by (rule nth_put_eq[OF A i es])
  have nth_load: "nth (load_T t) (asn_put A i (eval s A)) = eval s A"
    using eqSym[OF li] nth_i by (rule eqSubst[where Q="\<lambda>z. nth z (asn_put A i (eval s A)) = eval s A"])
  have eval_put: "eval t (asn_put A i (eval s A)) = eval s A"
    apply (rule defE[OF eval_def[where t=t and A="asn_put A i (eval s A)"]])
    apply (rule condI1Eq[OF tg es nth_load])
    done
  have eval_refl: "eval s A = eval s A"
    using es by simp
  have eval_sub: "eval (subst_T t i s) A = eval s A"
    using eqSym[OF sub] eval_refl by (rule eqSubst[where Q="\<lambda>z. eval z A = eval s A"])
  show "eval (subst_T t i s) A = eval t (asn_put A i (eval s A))"
    using eval_sub eqSym[OF eval_put] by (rule eq_trans)
next
  assume li: "\<not> load_T t = i"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have putN: "asn_put A i (eval s A) N"
    by (rule asn_put_N[OF A i es])
  have nthA_N: "nth (load_T t) A N"
    by (rule nth_N'[OF A loadN])
  have nthPut_N: "nth (load_T t) (asn_put A i (eval s A)) N"
    by (rule nth_N'[OF putN loadN])
  have nth_same: "nth (load_T t) (asn_put A i (eval s A)) = nth (load_T t) A"
    by (rule nth_put_ne[OF A i es loadN li])
  have evalA: "eval t A = nth (load_T t) A"
    apply (rule defE[OF eval_def[where t=t and A=A]])
    apply (rule condI1Eq[OF tg nthA_N])
    apply (rule nthA_N[unfolded isNat_def])
    done
  have evalPut: "eval t (asn_put A i (eval s A)) = nth (load_T t) (asn_put A i (eval s A))"
    apply (rule defE[OF eval_def[where t=t and A="asn_put A i (eval s A)"]])
    apply (rule condI1Eq[OF tg nthPut_N])
    apply (rule nthPut_N[unfolded isNat_def])
    done
  have evalPutNthA: "eval t (asn_put A i (eval s A)) = nth (load_T t) A"
    using evalPut nth_same by (rule eq_trans)
  have evalPutA: "eval t (asn_put A i (eval s A)) = eval t A"
    using evalPutNthA eqSym[OF evalA] by (rule eq_trans)
  have evalA_N: "eval t A N"
    using eqSym[OF evalA] nthA_N by (rule eqSubst[where Q="\<lambda>z. z N"])
  have evalA_refl: "eval t A = eval t A"
    using evalA_N by simp
  have sub: "subst_T t i s = t"
    by (rule subst_T_var_other[OF t i s tg li])
  have eval_sub: "eval (subst_T t i s) A = eval t A"
    using eqSym[OF sub] evalA_refl by (rule eqSubst[where Q="\<lambda>z. eval z A = eval t A"])
  show "eval (subst_T t i s) A = eval t (asn_put A i (eval s A))"
    using eval_sub eqSym[OF evalPutA] by (rule eq_trans)
qed

lemma eval_subst_T_zero:
  assumes t: "t N" and i: "i N" and s: "s N" and A: "A N" and es: "eval s A N" and tg: "tag_T t = T_ZERO"
  shows "eval (subst_T t i s) A = eval t (asn_put A i (eval s A))"
proof -
  have zN: "pack_T T_ZERO 0 N"
    by (rule pack_T_N[OF _ nat0], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have sub: "subst_T t i s = pack_T T_ZERO 0"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar zN])
    apply (rule condI1Eq[OF tg zN])
    using zN by simp
  have lhs: "eval (subst_T t i s) A = 0"
    using eqSym[OF sub] eval_zero[where A=A] by (rule eqSubst[where Q="\<lambda>u. eval u A = 0"])
  have rhs: "eval t (asn_put A i (eval s A)) = 0"
    by (rule eval_zeroI[where Q="\<lambda>u. u = 0", OF t tg zeroRefl])
  show ?thesis
    using lhs eqSym[OF rhs] by (rule eq_trans)
qed

lemma eval_subst_T_sucD:
  assumes t: "t N" and i: "i N" and s: "s N" and A: "A N" and es: "eval s A N" and tg: "tag_T t = T_SUC"
      and hN: "eval (subst_T t i s) A N"
      and IH: "eval (subst_T (load_T t) i s) A N \<Longrightarrow> eval (subst_T (load_T t) i s) A = eval (load_T t) (asn_put A i (eval s A))"
  shows "eval (subst_T t i s) A = eval t (asn_put A i (eval s A))"
proof -
  let ?u = "subst_T (load_T t) i s"
  let ?B = "asn_put A i (eval s A)"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have uN: "?u N"
    by (rule subst_T_N[OF loadN i s])
  have packedN: "pack_T T_SUC ?u N"
    by (rule pack_T_N[OF _ uN], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have sub: "subst_T t i s = pack_T T_SUC ?u"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI2Eq[OF nzero packedN])
    apply (rule condI1Eq[OF tg packedN])
    using packedN by simp
  have packedEvalN: "eval (pack_T T_SUC ?u) A N"
    using sub hN by (rule eqSubst[where Q="\<lambda>z. eval z A N"])
  have tagPacked: "tag_T (pack_T T_SUC ?u) = T_SUC"
    by (rule tag_pack_T[OF _ uN], simp)
  have loadPacked: "load_T (pack_T T_SUC ?u) = ?u"
    by (rule load_pack_T[OF _ uN], simp)
  have sucPackedN: "S (eval (load_T (pack_T T_SUC ?u)) A) N"
    by (rule eval_sucD[where Q="\<lambda>z. z N", OF packedN tagPacked packedEvalN])
  have sucChildN: "S (eval ?u A) N"
    using loadPacked sucPackedN by (rule eqSubst[where Q="\<lambda>v. S (eval v A) N"])
  have childN: "eval ?u A N"
    by (rule natSI[OF sucChildN])
  have ih: "eval ?u A = eval (load_T t) ?B"
    by (rule IH[OF childN])
  have rhsChildN: "eval (load_T t) ?B N"
    by (rule eq_impl_term2[OF ih])
  have lhsPacked: "eval (pack_T T_SUC ?u) A = S (eval ?u A)"
    by (rule eval_suc[OF uN childN])
  have lhs: "eval (subst_T t i s) A = S (eval ?u A)"
    using eqSym[OF sub] lhsPacked by (rule eqSubst[where Q="\<lambda>z. eval z A = S (eval ?u A)"])
  have rhsSucN: "S (eval (load_T t) ?B) N"
    by (rule natS[OF rhsChildN])
  have rhs: "eval t ?B = S (eval (load_T t) ?B)"
    by (rule eval_sucI[where Q="\<lambda>z. z = S (eval (load_T t) ?B)", OF t tg rhsSucN[unfolded isNat_def]])
  have sucIH: "S (eval ?u A) = S (eval (load_T t) ?B)"
    by (rule sucCong[OF ih])
  have step: "eval (subst_T t i s) A = S (eval (load_T t) ?B)"
    using lhs sucIH by (rule eq_trans)
  show ?thesis
    using step eqSym[OF rhs] by (rule eq_trans)
qed

lemma eval_subst_T_predD:
  assumes t: "t N" and i: "i N" and s: "s N" and A: "A N" and es: "eval s A N" and tg: "tag_T t = T_PRED"
      and hN: "eval (subst_T t i s) A N"
      and IH: "eval (subst_T (load_T t) i s) A N \<Longrightarrow> eval (subst_T (load_T t) i s) A = eval (load_T t) (asn_put A i (eval s A))"
  shows "eval (subst_T t i s) A = eval t (asn_put A i (eval s A))"
proof -
  let ?u = "subst_T (load_T t) i s"
  let ?B = "asn_put A i (eval s A)"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have uN: "?u N"
    by (rule subst_T_N[OF loadN i s])
  have packedN: "pack_T T_PRED ?u N"
    by (rule pack_T_N[OF _ uN], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have sub: "subst_T t i s = pack_T T_PRED ?u"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI2Eq[OF nzero packedN])
    apply (rule condI2Eq[OF nsuc packedN])
    apply (rule condI1Eq[OF tg packedN])
    using packedN by simp
  have packedEvalN: "eval (pack_T T_PRED ?u) A N"
    using sub hN by (rule eqSubst[where Q="\<lambda>z. eval z A N"])
  have tagPacked: "tag_T (pack_T T_PRED ?u) = T_PRED"
    by (rule tag_pack_T[OF _ uN], simp)
  have loadPacked: "load_T (pack_T T_PRED ?u) = ?u"
    by (rule load_pack_T[OF _ uN], simp)
  have predPackedN: "P (eval (load_T (pack_T T_PRED ?u)) A) N"
    by (rule eval_predD[where Q="\<lambda>z. z N", OF packedN tagPacked packedEvalN])
  have predChildN: "P (eval ?u A) N"
    using loadPacked predPackedN by (rule eqSubst[where Q="\<lambda>v. P (eval v A) N"])
  have childN: "eval ?u A N"
    by (rule predTIE[OF predChildN])
  have ih: "eval ?u A = eval (load_T t) ?B"
    by (rule IH[OF childN])
  have rhsChildN: "eval (load_T t) ?B N"
    by (rule eq_impl_term2[OF ih])
  have childRefl: "eval ?u A = eval ?u A"
    using childN by simp
  have evalLoadPacked: "eval (load_T (pack_T T_PRED ?u)) A = eval ?u A"
    using eqSym[OF loadPacked] childRefl by (rule eqSubst[where Q="\<lambda>v. eval v A = eval ?u A"])
  have predLoadPacked: "P (eval (load_T (pack_T T_PRED ?u)) A) = P (eval ?u A)"
    by (rule predCong[OF evalLoadPacked])
  have lhsPacked: "eval (pack_T T_PRED ?u) A = P (eval ?u A)"
    by (rule eval_predI[where Q="\<lambda>z. z = P (eval ?u A)", OF packedN tagPacked predLoadPacked])
  have lhs: "eval (subst_T t i s) A = P (eval ?u A)"
    using eqSym[OF sub] lhsPacked by (rule eqSubst[where Q="\<lambda>z. eval z A = P (eval ?u A)"])
  have rhsPredN: "P (eval (load_T t) ?B) N"
    by (rule natP[OF rhsChildN])
  have rhs: "eval t ?B = P (eval (load_T t) ?B)"
    by (rule eval_predI[where Q="\<lambda>z. z = P (eval (load_T t) ?B)", OF t tg rhsPredN[unfolded isNat_def]])
  have predIH: "P (eval ?u A) = P (eval (load_T t) ?B)"
    by (rule predCong[OF ih])
  have step: "eval (subst_T t i s) A = P (eval (load_T t) ?B)"
    using lhs predIH by (rule eq_trans)
  show ?thesis
    using step eqSym[OF rhs] by (rule eq_trans)
qed

lemma eval_subst_T_ifzD:
  assumes t: "t N" and i: "i N" and s: "s N" and A: "A N" and es: "eval s A N" and tg: "tag_T t = T_IFZ" and hN: "eval (subst_T t i s) A N"
    and IHc: "eval (subst_T (hyp_of (load_T t)) i s) A N \<Longrightarrow> eval (subst_T (hyp_of (load_T t)) i s) A = eval (hyp_of (load_T t)) (asn_put A i (eval s A))"
    and IHa: "eval (subst_T (hyp_of (conc_of (load_T t))) i s) A N \<Longrightarrow> eval (subst_T (hyp_of (conc_of (load_T t))) i s) A = eval (hyp_of (conc_of (load_T t))) (asn_put A i (eval s A))"
    and IHb: "eval (subst_T (conc_of (conc_of (load_T t))) i s) A N \<Longrightarrow> eval (subst_T (conc_of (conc_of (load_T t))) i s) A = eval (conc_of (conc_of (load_T t))) (asn_put A i (eval s A))"
  shows "eval (subst_T t i s) A = eval t (asn_put A i (eval s A))"
proof -
  let ?c0 = "cpx (load_T t)"
  let ?a0 = "cpx (cpy (load_T t))"
  let ?b0 = "cpy (cpy (load_T t))"
  let ?c = "subst_T ?c0 i s"
  let ?a = "subst_T ?a0 i s"
  let ?b = "subst_T ?b0 i s"
  let ?B = "asn_put A i (eval s A)"
  let ?args = "\<langle>?a, ?b\<rangle>"
  let ?payload = "\<langle>?c, ?args\<rangle>"
  let ?p = "pack_T T_IFZ ?payload"
  have loadN: "load_T t N"
    using t by (rule load_T_N)
  have c0N: "cpx (load_T t) N"
    using loadN by (rule cpx_terminates)
  have tailN: "cpy (load_T t) N"
    using loadN by (rule cpy_terminates)
  have a0N: "cpx (cpy (load_T t)) N"
    using tailN by (rule cpx_terminates)
  have b0N: "cpy (cpy (load_T t)) N"
    using tailN by (rule cpy_terminates)
  have cN: "subst_T (cpx (load_T t)) i s N"
    by (rule subst_T_N[OF c0N i s])
  have aN: "subst_T (cpx (cpy (load_T t))) i s N"
    by (rule subst_T_N[OF a0N i s])
  have bN: "subst_T (cpy (cpy (load_T t))) i s N"
    by (rule subst_T_N[OF b0N i s])
  have argsN: "?args N"
    using aN bN by simp
  have payloadN: "?payload N"
    using cN argsN by simp
  have packedN: "?p N"
    by (rule pack_T_N[OF _ payloadN], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have npred: "\<not> tag_T t = T_PRED"
    using tg by simp
  have sub: "subst_T t i s = ?p"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI2Eq[OF nzero packedN])
    apply (rule condI2Eq[OF nsuc packedN])
    apply (rule condI2Eq[OF npred packedN])
    apply (rule condI1Eq[OF tg packedN])
    using packedN by simp
  have packedEvalN: "eval ?p A N"
    using sub hN by (rule eqSubst[where Q="\<lambda>z. eval z A N"])
  have tagPacked: "tag_T ?p = T_IFZ"
    by (rule tag_pack_T[OF _ payloadN], simp)
  have loadPacked: "load_T ?p = ?payload"
    by (rule load_pack_T[OF _ payloadN], simp)
  have rawN: "(if eval (cpx (load_T ?p)) A = 0 then eval (cpx (cpy (load_T ?p))) A else eval (cpy (cpy (load_T ?p))) A) N"
    by (rule eval_ifzD[where Q="\<lambda>z. z N", OF packedN tagPacked packedEvalN])
  have payloadC: "cpx ?payload = ?c"
    by (rule cpx_proj[OF cN argsN])
  have payloadArgs: "cpy ?payload = ?args"
    by (rule cpy_proj[OF cN argsN])
  have argsA: "cpx ?args = ?a"
    by (rule cpx_proj[OF aN bN])
  have argsB: "cpy ?args = ?b"
    by (rule cpy_proj[OF aN bN])
  have selectC: "cpx (load_T ?p) = ?c"
    using eqSym[OF loadPacked] payloadC by (rule eqSubst[where Q="\<lambda>z. cpx z = ?c"])
  have selectArgs: "cpy (load_T ?p) = ?args"
    using eqSym[OF loadPacked] payloadArgs by (rule eqSubst[where Q="\<lambda>z. cpy z = ?args"])
  have selectA: "cpx (cpy (load_T ?p)) = ?a"
    using eqSym[OF selectArgs] argsA by (rule eqSubst[where Q="\<lambda>z. cpx z = ?a"])
  have selectB: "cpy (cpy (load_T ?p)) = ?b"
    using eqSym[OF selectArgs] argsB by (rule eqSubst[where Q="\<lambda>z. cpy z = ?b"])
  have bodyN: "(if eval ?c A = 0 then eval ?a A else eval ?b A) N"
    using selectC selectA selectB rawN by simp
  have guardB: "(eval ?c A = 0) B"
    by (rule condE3[OF bodyN])
  have cEvalN: "eval ?c A N"
    by (rule conjE1[OF eqE[OF guardB]])
  have ihc: "eval (subst_T (hyp_of (load_T t)) i s) A = eval (hyp_of (load_T t)) (asn_put A i (eval s A))"
    by (rule IHc[OF cEvalN])
  show ?thesis
  proof (rule cases_bool[where q="eval ?c A = 0"])
    show "(eval ?c A = 0) B"
      by (rule guardB)
  next
    assume cz: "eval ?c A = 0"
    have aEvalN: "eval ?a A N"
      by (rule condE1[OF cz bodyN])
    have iha: "eval (subst_T (hyp_of (conc_of (load_T t))) i s) A = eval (hyp_of (conc_of (load_T t))) (asn_put A i (eval s A))"
      by (rule IHa[OF aEvalN])
    have aRefl: "eval ?a A = eval ?a A"
      using aEvalN by simp
    have condA: "(if eval ?c A = 0 then eval ?a A else eval ?b A) = eval ?a A"
      by (rule condI1Eq[OF cz aEvalN aRefl])
    have packedCondA0: "(if eval (cpx (load_T ?p)) A = 0 then eval ?a A else eval ?b A) = eval ?a A"
      using eqSym[OF selectC] condA by (rule eqSubst[where Q="\<lambda>z. (if eval z A = 0 then eval ?a A else eval ?b A) = eval ?a A"])
    have packedCondA1: "(if eval (cpx (load_T ?p)) A = 0 then eval (cpx (cpy (load_T ?p))) A else eval ?b A) = eval ?a A"
      using eqSym[OF selectA] packedCondA0 by (rule eqSubst[where Q="\<lambda>z. (if eval (cpx (load_T ?p)) A = 0 then eval z A else eval ?b A) = eval ?a A"])
    have packedCondA: "(if eval (cpx (load_T ?p)) A = 0 then eval (cpx (cpy (load_T ?p))) A else eval (cpy (cpy (load_T ?p))) A) = eval ?a A"
      using eqSym[OF selectB] packedCondA1 by (rule eqSubst[where Q="\<lambda>z. (if eval (cpx (load_T ?p)) A = 0 then eval (cpx (cpy (load_T ?p))) A else eval z A) = eval ?a A"])
    have packedA: "eval ?p A = eval ?a A"
      by (rule eval_ifzI[where Q="\<lambda>z. z = eval ?a A", OF packedN tagPacked packedCondA])
    have lhsA: "eval (subst_T t i s) A = eval (subst_T (hyp_of (conc_of (load_T t))) i s) A"
      using eqSym[OF sub] packedA by (rule eqSubst[where Q="\<lambda>z. eval z A = eval ?a A"])
    have rhsCzSym: "eval (hyp_of (load_T t)) (asn_put A i (eval s A)) = eval (subst_T (hyp_of (load_T t)) i s) A"
      by (rule eqSym[OF ihc])
    have rhsCz: "eval (hyp_of (load_T t)) (asn_put A i (eval s A)) = 0"
      using rhsCzSym cz by (rule eq_trans)
    have rhsAN: "eval (hyp_of (conc_of (load_T t))) (asn_put A i (eval s A)) N"
      using iha by (rule eq_impl_term2)
    have rhsARefl: "eval (hyp_of (conc_of (load_T t))) (asn_put A i (eval s A)) = eval (hyp_of (conc_of (load_T t))) (asn_put A i (eval s A))"
      using rhsAN by simp
    have rhsCondA: "(if eval (hyp_of (load_T t)) (asn_put A i (eval s A)) = 0 then eval (hyp_of (conc_of (load_T t))) (asn_put A i (eval s A)) else eval (conc_of (conc_of (load_T t))) (asn_put A i (eval s A))) = eval (hyp_of (conc_of (load_T t))) (asn_put A i (eval s A))"
      by (rule condI1Eq[OF rhsCz rhsAN rhsARefl])
    have rhsA: "eval t (asn_put A i (eval s A)) = eval (hyp_of (conc_of (load_T t))) (asn_put A i (eval s A))"
      by (rule eval_ifzI[where Q="\<lambda>z. z = eval (hyp_of (conc_of (load_T t))) (asn_put A i (eval s A))", OF t tg rhsCondA])
    have stepA: "eval (subst_T t i s) A = eval (hyp_of (conc_of (load_T t))) (asn_put A i (eval s A))"
      using lhsA iha by (rule eq_trans)
    show "eval (subst_T t i s) A = eval t (asn_put A i (eval s A))"
      using stepA eqSym[OF rhsA] by (rule eq_trans)
  next
    assume ncz: "\<not> eval ?c A = 0"
    have bEvalN: "eval ?b A N"
      by (rule condE2[OF ncz bodyN])
    have ihb: "eval (subst_T (conc_of (conc_of (load_T t))) i s) A = eval (conc_of (conc_of (load_T t))) (asn_put A i (eval s A))"
      by (rule IHb[OF bEvalN])
    have rhsNcz: "\<not> eval (hyp_of (load_T t)) (asn_put A i (eval s A)) = 0"
      by (rule eqSubst[where a="eval (subst_T (hyp_of (load_T t)) i s) A" and b="eval (hyp_of (load_T t)) (asn_put A i (eval s A))" and Q="\<lambda>z. \<not> z = 0", OF ihc ncz])
    have bRefl: "eval ?b A = eval ?b A"
      using bEvalN by simp
    have condB: "(if eval ?c A = 0 then eval ?a A else eval ?b A) = eval ?b A"
      by (rule condI2Eq[OF ncz bEvalN bRefl])
    have packedCondB0: "(if eval (cpx (load_T ?p)) A = 0 then eval ?a A else eval ?b A) = eval ?b A"
      by (rule eqSubst[where a="?c" and b="cpx (load_T ?p)" and Q="\<lambda>z. (if eval z A = 0 then eval ?a A else eval ?b A) = eval ?b A", OF eqSym[OF selectC] condB])
    have packedCondB1: "(if eval (cpx (load_T ?p)) A = 0 then eval (cpx (cpy (load_T ?p))) A else eval ?b A) = eval ?b A"
      by (rule eqSubst[where a="?a" and b="cpx (cpy (load_T ?p))" and Q="\<lambda>z. (if eval (cpx (load_T ?p)) A = 0 then eval z A else eval ?b A) = eval ?b A", OF eqSym[OF selectA] packedCondB0])
    have packedCondB: "(if eval (cpx (load_T ?p)) A = 0 then eval (cpx (cpy (load_T ?p))) A else eval (cpy (cpy (load_T ?p))) A) = eval ?b A"
      by (rule eqSubst[where a="?b" and b="cpy (cpy (load_T ?p))" and Q="\<lambda>z. (if eval (cpx (load_T ?p)) A = 0 then eval (cpx (cpy (load_T ?p))) A else eval z A) = eval ?b A", OF eqSym[OF selectB] packedCondB1])
    have packedB: "eval ?p A = eval ?b A"
      by (rule eval_ifzI[where Q="\<lambda>z. z = eval ?b A", OF packedN tagPacked packedCondB])
    have lhsB: "eval (subst_T t i s) A = eval ?b A"
      using eqSym[OF sub] packedB by (rule eqSubst[where Q="\<lambda>z. eval z A = eval ?b A"])
    have rhsBN: "eval (conc_of (conc_of (load_T t))) (asn_put A i (eval s A)) N"
      using ihb by (rule eq_impl_term2)
    have rhsBRefl: "eval (conc_of (conc_of (load_T t))) (asn_put A i (eval s A)) = eval (conc_of (conc_of (load_T t))) (asn_put A i (eval s A))"
      using rhsBN by simp
    have rhsCondB: "(if eval (hyp_of (load_T t)) (asn_put A i (eval s A)) = 0 then eval (hyp_of (conc_of (load_T t))) (asn_put A i (eval s A)) else eval (conc_of (conc_of (load_T t))) (asn_put A i (eval s A))) = eval (conc_of (conc_of (load_T t))) (asn_put A i (eval s A))"
      by (rule condI2Eq[OF rhsNcz rhsBN rhsBRefl])
    have rhsB: "eval t (asn_put A i (eval s A)) = eval (conc_of (conc_of (load_T t))) (asn_put A i (eval s A))"
      by (rule eval_ifzI[where Q="\<lambda>z. z = eval (conc_of (conc_of (load_T t))) (asn_put A i (eval s A))", OF t tg rhsCondB])
    have lhsB: "eval (subst_T t i s) A = eval (subst_T (conc_of (conc_of (load_T t))) i s) A"
      by (rule eqSubst[where a="?p" and b="subst_T t i s" and Q="\<lambda>z. eval z A = eval (subst_T (conc_of (conc_of (load_T t))) i s) A", OF eqSym[OF sub] packedB])
    have stepB: "eval (subst_T t i s) A = eval (conc_of (conc_of (load_T t))) (asn_put A i (eval s A))"
      apply (rule eq_trans[where b="eval (subst_T (conc_of (conc_of (load_T t))) i s) A"])
       apply (rule lhsB)
      apply (rule ihb)
      done
    show "eval (subst_T t i s) A = eval t (asn_put A i (eval s A))"
      using stepB eqSym[OF rhsB] by (rule eq_trans)
  qed
qed

lemma eval_binary_asn_cong:
  assumes xeq: "x = x'" and yeq: "y = y'" and eN: "eval d (x \<triangleright> (y \<triangleright> Nil)) N"
  shows "eval d (x \<triangleright> (y \<triangleright> Nil)) = eval d (x' \<triangleright> (y' \<triangleright> Nil))"
proof -
  have refl: "eval d (x \<triangleright> (y \<triangleright> Nil)) = eval d (x \<triangleright> (y \<triangleright> Nil))"
    using eN by simp
  have replaceY: "eval d (x \<triangleright> (y \<triangleright> Nil)) = eval d (x \<triangleright> (y' \<triangleright> Nil))"
    by (rule eqSubst[where a=y and b=y' and Q="\<lambda>z. eval d (x \<triangleright> (y \<triangleright> Nil)) = eval d (x \<triangleright> (z \<triangleright> Nil))", OF yeq refl])
  show ?thesis
    by (rule eqSubst[where a=x and b=x' and Q="\<lambda>z. eval d (x \<triangleright> (y \<triangleright> Nil)) = eval d (z \<triangleright> (y' \<triangleright> Nil))", OF xeq replaceY])
qed

lemma eval_subst_T_appD:
  assumes t: "t N" and i: "i N" and s: "s N" and A: "A N" and es: "eval s A N" and tg: "tag_T t = T_APP" and hN: "eval (subst_T t i s) A N"
      and IHx: "eval (subst_T (cpx (cpy (load_T t))) i s) A N \<Longrightarrow> eval (subst_T (cpx (cpy (load_T t))) i s) A = eval (cpx (cpy (load_T t))) (asn_put A i (eval s A))"
      and IHy: "eval (subst_T (cpy (cpy (load_T t))) i s) A N \<Longrightarrow> eval (subst_T (cpy (cpy (load_T t))) i s) A = eval (cpy (cpy (load_T t))) (asn_put A i (eval s A))"
  shows "eval (subst_T t i s) A = eval t (asn_put A i (eval s A))"
proof -
  let ?d = "cpx (load_T t)"
  let ?x_sub = "cpx (cpy (load_T t))"
  let ?y_sub = "cpy (cpy (load_T t))"
  let ?x = "subst_T ?x_sub i s"
  let ?y = "subst_T ?y_sub i s"
  let ?B = "asn_put A i (eval s A)"
  let ?args = "\<langle>?x, ?y\<rangle>"
  let ?payload = "\<langle>?d, ?args\<rangle>"
  let ?p = "pack_T T_APP ?payload"
  let ?bodyL = "eval (nth ?d dfns) ((eval ?x A) \<triangleright> ((eval ?y A) \<triangleright> Nil))"
  let ?bodyR = "eval (nth ?d dfns) ((eval ?x_sub ?B) \<triangleright> ((eval ?y_sub ?B) \<triangleright> Nil))"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have dN: "?d N"
    by (rule cpx_terminates[OF loadN])
  have tailN: "cpy (load_T t) N"
    by (rule cpy_terminates[OF loadN])
  have x_subN: "?x_sub N"
    by (rule cpx_terminates[OF tailN])
  have y_subN: "?y_sub N"
    by (rule cpy_terminates[OF tailN])
  have xN: "?x N"
    by (rule subst_T_N[OF x_subN i s])
  have yN: "?y N"
    by (rule subst_T_N[OF y_subN i s])
  have argsN: "?args N"
    using xN yN by simp
  have payloadN: "?payload N"
    using dN argsN by simp
  have packedN: "?p N"
    by (rule pack_T_N[OF _ payloadN], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have npred: "\<not> tag_T t = T_PRED"
    using tg by simp
  have nifz: "\<not> tag_T t = T_IFZ"
    using tg by simp
  have sub: "subst_T t i s = ?p"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI2Eq[OF nzero packedN])
    apply (rule condI2Eq[OF nsuc packedN])
    apply (rule condI2Eq[OF npred packedN])
    apply (rule condI2Eq[OF nifz packedN])
    using packedN by simp
  have packedEvalN: "eval ?p A N"
    by (rule eqSubst[where a="subst_T t i s" and b="?p" and Q="\<lambda>z. eval z A N", OF sub hN])
  have tagPacked: "tag_T ?p = T_APP"
    by (rule tag_pack_T[OF _ payloadN], simp)
  have loadPacked: "load_T ?p = ?payload"
    by (rule load_pack_T[OF _ payloadN], simp)
  have payloadD: "cpx ?payload = ?d"
    by (rule cpx_proj[OF dN argsN])
  have payloadArgs: "cpy ?payload = ?args"
    by (rule cpy_proj[OF dN argsN])
  have argsX: "cpx ?args = ?x"
    by (rule cpx_proj[OF xN yN])
  have argsY: "cpy ?args = ?y"
    by (rule cpy_proj[OF xN yN])
  have selectD: "cpx (load_T ?p) = ?d"
    by (rule eqSubst[where a="?payload" and b="load_T ?p" and Q="\<lambda>z. cpx z = ?d", OF eqSym[OF loadPacked] payloadD])
  have selectArgs: "cpy (load_T ?p) = ?args"
    by (rule eqSubst[where a="?payload" and b="load_T ?p" and Q="\<lambda>z. cpy z = ?args", OF eqSym[OF loadPacked] payloadArgs])
  have selectX: "cpx (cpy (load_T ?p)) = ?x"
    by (rule eqSubst[where a="?args" and b="cpy (load_T ?p)" and Q="\<lambda>z. cpx z = ?x", OF eqSym[OF selectArgs] argsX])
  have selectY: "cpy (cpy (load_T ?p)) = ?y"
    by (rule eqSubst[where a="?args" and b="cpy (load_T ?p)" and Q="\<lambda>z. cpy z = ?y", OF eqSym[OF selectArgs] argsY])
  have packedXEvalN: "eval (cpx (cpy (load_T ?p))) A N"
    by (rule eval_app_arg1N[OF packedN tagPacked packedEvalN])
  have packedYEvalN: "eval (cpy (cpy (load_T ?p))) A N"
    by (rule eval_app_arg2N[OF packedN tagPacked packedEvalN])
  have xEvalN: "eval ?x A N"
    by (rule eqSubst[where a="cpx (cpy (load_T ?p))" and b="?x" and Q="\<lambda>z. eval z A N", OF selectX packedXEvalN])
  have yEvalN: "eval ?y A N"
    by (rule eqSubst[where a="cpy (cpy (load_T ?p))" and b="?y" and Q="\<lambda>z. eval z A N", OF selectY packedYEvalN])
  have ihx: "eval ?x A = eval ?x_sub ?B"
    by (rule IHx[OF xEvalN])
  have ihy: "eval ?y A = eval ?y_sub ?B"
    by (rule IHy[OF yEvalN])
  have x_subEvalN: "eval ?x_sub ?B N"
    by (rule eq_impl_term2[OF ihx])
  have y_subEvalN: "eval ?y_sub ?B N"
    by (rule eq_impl_term2[OF ihy])
  have packedRaw: "eval ?p A = eval (nth (cpx (load_T ?p)) dfns) ((eval (cpx (cpy (load_T ?p))) A) \<triangleright> ((eval (cpy (cpy (load_T ?p))) A) \<triangleright> Nil))"
    by (rule eval_app_val[OF packedN tagPacked packedEvalN])
  have packedD: "eval ?p A = eval (nth ?d dfns) ((eval (cpx (cpy (load_T ?p))) A) \<triangleright> ((eval (cpy (cpy (load_T ?p))) A) \<triangleright> Nil))"
    by (rule eqSubst[where a="cpx (load_T ?p)" and b="?d" and Q="\<lambda>z. eval ?p A = eval (nth z dfns) ((eval (cpx (cpy (load_T ?p))) A) \<triangleright> ((eval (cpy (cpy (load_T ?p))) A) \<triangleright> Nil))", OF selectD packedRaw])
  have packedX: "eval ?p A = eval (nth ?d dfns) ((eval ?x A) \<triangleright> ((eval (cpy (cpy (load_T ?p))) A) \<triangleright> Nil))"
    by (rule eqSubst[where a="cpx (cpy (load_T ?p))" and b="?x" and Q="\<lambda>z. eval ?p A = eval (nth ?d dfns) ((eval z A) \<triangleright> ((eval (cpy (cpy (load_T ?p))) A) \<triangleright> Nil))", OF selectX packedD])
  have packedVal: "eval ?p A = ?bodyL"
    by (rule eqSubst[where a="cpy (cpy (load_T ?p))" and b="?y" and Q="\<lambda>z. eval ?p A = eval (nth ?d dfns) ((eval ?x A) \<triangleright> ((eval z A) \<triangleright> Nil))", OF selectY packedX])
  have bodyLN: "?bodyL N"
    by (rule eq_impl_term2[OF packedVal])
  have bodyCong: "?bodyL = ?bodyR"
    by (rule eval_binary_asn_cong[OF ihx ihy bodyLN])
  have bodyRN: "?bodyR N"
    by (rule eq_impl_term2[OF bodyCong])
  have lhsBodyL: "eval (subst_T t i s) A = ?bodyL"
    by (rule eqSubst[where a="?p" and b="subst_T t i s" and Q="\<lambda>z. eval z A = ?bodyL", OF eqSym[OF sub] packedVal])
  have lhsBodyR: "eval (subst_T t i s) A = ?bodyR"
    apply (rule eq_trans[where b="?bodyL"])
    apply (rule lhsBodyL)
    apply (rule bodyCong)
    done
  have gx: "eval ?x_sub ?B = eval ?x_sub ?B"
    by (rule x_subEvalN[unfolded isNat_def])
  have gy: "eval ?y_sub ?B = eval ?y_sub ?B"
    by (rule y_subEvalN[unfolded isNat_def])
  have bodyRRefl: "?bodyR = ?bodyR"
    by (rule bodyRN[unfolded isNat_def])
  have innerEq: "(if eval ?y_sub ?B = eval ?y_sub ?B then ?bodyR else 0) = ?bodyR"
    by (rule condI1Eq[OF gy bodyRN bodyRRefl])
  have innerN: "(if eval ?y_sub ?B = eval ?y_sub ?B then ?bodyR else 0) N"
    by (rule eq_impl_term[OF innerEq])
  have outerEq: "(if eval ?x_sub ?B = eval ?x_sub ?B then (if eval ?y_sub ?B = eval ?y_sub ?B then ?bodyR else 0) else 0) = ?bodyR"
    by (rule condI1Eq[OF gx bodyRN innerEq])
  have rhs: "eval t ?B = ?bodyR"
    by (rule eval_appI[where Q="\<lambda>z. z = ?bodyR", OF t tg outerEq])
  show ?thesis
    using lhsBodyR eqSym[OF rhs] by (rule eq_trans)
qed

lemma eval_app_defaultI:
  assumes t: "t N" and nvar: "\<not> tag_T t = T_VAR" and nzero: "\<not> tag_T t = T_ZERO" and nsuc: "\<not> tag_T t = T_SUC" and npred: "\<not> tag_T t = T_PRED" and nifz: "\<not> tag_T t = T_IFZ"
      and H: "Q (if eval (hyp_of (conc_of (load_T t))) A = eval (hyp_of (conc_of (load_T t))) A then (if eval (conc_of (conc_of (load_T t))) A = eval (conc_of (conc_of (load_T t))) A then eval (nth (hyp_of (load_T t)) dfns) (eval (hyp_of (conc_of (load_T t))) A \<triangleright> eval (conc_of (conc_of (load_T t))) A \<triangleright> Nil) else 0) else 0)"
  shows "Q (eval t A)"
proof -
  show ?thesis
    apply (rule defE[OF eval_def[where t=t and A=A]])
    apply (rule cond_elseQ_I[where Q=Q, OF nvar])
    apply (rule cond_elseQ_I[where Q=Q, OF nzero])
    apply (rule cond_elseQ_I[where Q=Q, OF nsuc])
    apply (rule cond_elseQ_I[where Q=Q, OF npred])
    apply (rule cond_elseQ_I[where Q=Q, OF nifz])
    apply (rule H)
    done
qed

lemma eval_subst_T_app_defaultD:
  assumes t: "t N" and i: "i N" and s: "s N" and A: "A N" and es: "eval s A N"
      and nvar: "\<not> tag_T t = T_VAR" and nzero: "\<not> tag_T t = T_ZERO" and nsuc: "\<not> tag_T t = T_SUC"
      and npred: "\<not> tag_T t = T_PRED" and nifz: "\<not> tag_T t = T_IFZ" and hN: "eval (subst_T t i s) A N"
      and IHx: "eval (subst_T (hyp_of (conc_of (load_T t))) i s) A N \<Longrightarrow> eval (subst_T (hyp_of (conc_of (load_T t))) i s) A = eval (hyp_of (conc_of (load_T t))) (asn_put A i (eval s A))"
      and IHy: "eval (subst_T (conc_of (conc_of (load_T t))) i s) A N \<Longrightarrow> eval (subst_T (conc_of (conc_of (load_T t))) i s) A = eval (conc_of (conc_of (load_T t))) (asn_put A i (eval s A))"
  shows "eval (subst_T t i s) A = eval t (asn_put A i (eval s A))"
proof -
   let ?d = "cpx (load_T t)"
  let ?x_sub = "cpx (cpy (load_T t))"
  let ?y_sub = "cpy (cpy (load_T t))"
  let ?x = "subst_T ?x_sub i s"
  let ?y = "subst_T ?y_sub i s"
  let ?B = "asn_put A i (eval s A)"
  let ?args = "\<langle>?x, ?y\<rangle>"
  let ?payload = "\<langle>?d, ?args\<rangle>"
  let ?p = "pack_T T_APP ?payload"
  let ?bodyL = "eval (nth ?d dfns) ((eval ?x A) \<triangleright> ((eval ?y A) \<triangleright> Nil))"
  let ?bodyR = "eval (nth ?d dfns) ((eval ?x_sub ?B) \<triangleright> ((eval ?y_sub ?B) \<triangleright> Nil))"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have dN: "?d N"
    by (rule cpx_terminates[OF loadN])
  have tailN: "cpy (load_T t) N"
    by (rule cpy_terminates[OF loadN])
  have x_subN: "?x_sub N"
    by (rule cpx_terminates[OF tailN])
  have y_subN: "?y_sub N"
    by (rule cpy_terminates[OF tailN])
  have xN: "?x N"
    by (rule subst_T_N[OF x_subN i s])
  have yN: "?y N"
    by (rule subst_T_N[OF y_subN i s])
  have argsN: "?args N"
    using xN yN by simp
  have payloadN: "?payload N"
    using dN argsN by simp
  have packedN: "?p N"
    by (rule pack_T_N[OF _ payloadN], simp)
  have sub: "subst_T t i s = ?p"
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=s]])
    apply (rule condI2Eq[OF nvar packedN])
    apply (rule condI2Eq[OF nzero packedN])
    apply (rule condI2Eq[OF nsuc packedN])
    apply (rule condI2Eq[OF npred packedN])
    apply (rule condI2Eq[OF nifz packedN])
    using packedN by simp
  have packedEvalN: "eval ?p A N"
    by (rule eqSubst[where a="subst_T t i s" and b="?p" and Q="\<lambda>z. eval z A N", OF sub hN])
  have tagPacked: "tag_T ?p = T_APP"
    by (rule tag_pack_T[OF _ payloadN], simp)
  have loadPacked: "load_T ?p = ?payload"
    by (rule load_pack_T[OF _ payloadN], simp)
  have payloadD: "cpx ?payload = ?d"
    by (rule cpx_proj[OF dN argsN])
  have payloadArgs: "cpy ?payload = ?args"
    by (rule cpy_proj[OF dN argsN])
  have argsX: "cpx ?args = ?x"
    by (rule cpx_proj[OF xN yN])
  have argsY: "cpy ?args = ?y"
    by (rule cpy_proj[OF xN yN])
  have selectD: "cpx (load_T ?p) = ?d"
    by (rule eqSubst[where a="?payload" and b="load_T ?p" and Q="\<lambda>z. cpx z = ?d", OF eqSym[OF loadPacked] payloadD])
  have selectArgs: "cpy (load_T ?p) = ?args"
    by (rule eqSubst[where a="?payload" and b="load_T ?p" and Q="\<lambda>z. cpy z = ?args", OF eqSym[OF loadPacked] payloadArgs])
  have selectX: "cpx (cpy (load_T ?p)) = ?x"
    by (rule eqSubst[where a="?args" and b="cpy (load_T ?p)" and Q="\<lambda>z. cpx z = ?x", OF eqSym[OF selectArgs] argsX])
  have selectY: "cpy (cpy (load_T ?p)) = ?y"
    by (rule eqSubst[where a="?args" and b="cpy (load_T ?p)" and Q="\<lambda>z. cpy z = ?y", OF eqSym[OF selectArgs] argsY])
  have packedXEvalN: "eval (cpx (cpy (load_T ?p))) A N"
    by (rule eval_app_arg1N[OF packedN tagPacked packedEvalN])
  have packedYEvalN: "eval (cpy (cpy (load_T ?p))) A N"
    by (rule eval_app_arg2N[OF packedN tagPacked packedEvalN])
  have xEvalN: "eval ?x A N"
    by (rule eqSubst[where a="cpx (cpy (load_T ?p))" and b="?x" and Q="\<lambda>z. eval z A N", OF selectX packedXEvalN])
  have yEvalN: "eval ?y A N"
    by (rule eqSubst[where a="cpy (cpy (load_T ?p))" and b="?y" and Q="\<lambda>z. eval z A N", OF selectY packedYEvalN])
  have ihx: "eval ?x A = eval ?x_sub ?B"
    by (rule IHx[OF xEvalN])
  have ihy: "eval ?y A = eval ?y_sub ?B"
    by (rule IHy[OF yEvalN])
  have x_subEvalN: "eval ?x_sub ?B N"
    by (rule eq_impl_term2[OF ihx])
  have y_subEvalN: "eval ?y_sub ?B N"
    by (rule eq_impl_term2[OF ihy])
  have packedRaw: "eval ?p A = eval (nth (cpx (load_T ?p)) dfns) ((eval (cpx (cpy (load_T ?p))) A) \<triangleright> ((eval (cpy (cpy (load_T ?p))) A) \<triangleright> Nil))"
    by (rule eval_app_val[OF packedN tagPacked packedEvalN])
  have packedD: "eval ?p A = eval (nth ?d dfns) ((eval (cpx (cpy (load_T ?p))) A) \<triangleright> ((eval (cpy (cpy (load_T ?p))) A) \<triangleright> Nil))"
    by (rule eqSubst[where a="cpx (load_T ?p)" and b="?d" and Q="\<lambda>z. eval ?p A = eval (nth z dfns) ((eval (cpx (cpy (load_T ?p))) A) \<triangleright> ((eval (cpy (cpy (load_T ?p))) A) \<triangleright> Nil))", OF selectD packedRaw])
  have packedX: "eval ?p A = eval (nth ?d dfns) ((eval ?x A) \<triangleright> ((eval (cpy (cpy (load_T ?p))) A) \<triangleright> Nil))"
    by (rule eqSubst[where a="cpx (cpy (load_T ?p))" and b="?x" and Q="\<lambda>z. eval ?p A = eval (nth ?d dfns) ((eval z A) \<triangleright> ((eval (cpy (cpy (load_T ?p))) A) \<triangleright> Nil))", OF selectX packedD])
  have packedVal: "eval ?p A = ?bodyL"
    by (rule eqSubst[where a="cpy (cpy (load_T ?p))" and b="?y" and Q="\<lambda>z. eval ?p A = eval (nth ?d dfns) ((eval ?x A) \<triangleright> ((eval z A) \<triangleright> Nil))", OF selectY packedX])
  have bodyLN: "?bodyL N"
    by (rule eq_impl_term2[OF packedVal])
  have bodyCong: "?bodyL = ?bodyR"
    by (rule eval_binary_asn_cong[OF ihx ihy bodyLN])
  have bodyRN: "?bodyR N"
    by (rule eq_impl_term2[OF bodyCong])
  have lhsBodyL: "eval (subst_T t i s) A = ?bodyL"
    by (rule eqSubst[where a="?p" and b="subst_T t i s" and Q="\<lambda>z. eval z A = ?bodyL", OF eqSym[OF sub] packedVal])
  have lhsBodyR: "eval (subst_T t i s) A = ?bodyR"
    apply (rule eq_trans[where b="?bodyL"])
     apply (rule lhsBodyL)
    apply (rule bodyCong)
    done
  have gx: "eval ?x_sub ?B = eval ?x_sub ?B"
    by (rule x_subEvalN[unfolded isNat_def])
  have gy: "eval ?y_sub ?B = eval ?y_sub ?B"
    by (rule y_subEvalN[unfolded isNat_def])
  have bodyRRefl: "?bodyR = ?bodyR"
    by (rule bodyRN[unfolded isNat_def])
  have innerEq: "(if eval ?y_sub ?B = eval ?y_sub ?B then ?bodyR else 0) = ?bodyR"
    by (rule condI1Eq[OF gy bodyRN bodyRRefl])
  have innerN: "(if eval ?y_sub ?B = eval ?y_sub ?B then ?bodyR else 0) N"
    by (rule eq_impl_term[OF innerEq])
  have outerEq: "(if eval ?x_sub ?B = eval ?x_sub ?B then (if eval ?y_sub ?B = eval ?y_sub ?B then ?bodyR else 0) else 0) = ?bodyR"
    by (rule condI1Eq[OF gx bodyRN innerEq])
  have rhs: "eval t ?B = ?bodyR"
    by (rule eval_app_defaultI[where Q="\<lambda>z. z = ?bodyR", OF t nvar nzero nsuc npred nifz outerEq])
  show ?thesis
    using lhsBodyR eqSym[OF rhs] by (rule eq_trans)
qed

lemma check_app_sound:
  assumes J: "J N" and rest: "rest N"
      and chk: "check_app J rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   sat_hyp (hyp_of K) A \<Longrightarrow> sat (conc_of K) A"
      and satG: "sat_hyp (hyp_of J) A"
  shows "sat (conc_of J) A"


lemma find_structE:
  assumes J: "J N" and G: "G N" and rest: "rest N" and ptr: "ptr N"
      and sub: "subset ptr rest"
      and fs: "find_struct J G ptr"
      and H: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   conc_of K = conc_of J \<Longrightarrow>
                   subset (hyp_of K) G \<Longrightarrow> R"
  shows R
proof -
  have main: "subset ptr rest \<turnstile> (find_struct J G ptr \<turnstile> R)"
  proof (rule list_induct[OF ptr])
    show "subset Nil rest \<turnstile> (find_struct J G Nil \<turnstile> R)"
    proof (rule entailsI)
      assume sub0: "subset Nil rest"
      show "find_struct J G Nil \<turnstile> R"
      proof (rule entailsI)
        assume fs0: "find_struct J G Nil"
        have C0: "if Nil = Nil then False
                    else if conc_of (list_hd Nil) = conc_of J \<and>
                            subset (hyp_of (list_hd Nil)) G then True
                    else find_struct J G (list_tl Nil)"
          using fs0
          by (rule defI[OF find_struct_def[where J=J and G=G and ptr=Nil]])
        have F: "False" using C0 by simp
        show R by (rule exF[OF F not_false])
      qed
    qed
  next
    fix h t
    assume h: "h N" and t: "t N"
       and IH: "subset t rest \<turnstile> (find_struct J G t \<turnstile> R)"
    show "subset (Cons h t) rest \<turnstile> (find_struct J G (Cons h t) \<turnstile> R)"
    proof (rule entailsI)
      assume subht: "subset (Cons h t) rest"
      have hrest: "mem h rest"
        using h t rest subht by (rule subset_cons_headE)
      have subt: "subset t rest"
        using h t rest subht by (rule subset_cons_tailE)
      show "find_struct J G (Cons h t) \<turnstile> R"
      proof (rule entailsI)
        assume fsht: "find_struct J G (Cons h t)"
        have C0: "if Cons h t = Nil then False
                    else if conc_of (list_hd (Cons h t)) = conc_of J \<and>
                            subset (hyp_of (list_hd (Cons h t))) G then True
                    else find_struct J G (list_tl (Cons h t))"
          using fsht
          by (rule defI[OF find_struct_def[where J=J and G=G and ptr="Cons h t"]])
        have C: "if Cons h t = Nil then False
                   else if conc_of h = conc_of J \<and> subset (hyp_of h) G then True
                   else find_struct J G t"
          using C0
          by (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
        have ne: "\<not> (Cons h t = Nil)" using h t by simp
        have C1: "if conc_of h = conc_of J \<and> subset (hyp_of h) G then True
                  else find_struct J G t"
          using ne C by (rule notcond_thenE)
        have ch: "conc_of h N" using h by simp
        have cJ: "conc_of J N" using J by simp
        have hh: "hyp_of h N" using h by simp
        have eqcB: "(conc_of h = conc_of J) B" by (rule eqBool[OF ch cJ])
        have subBd: "(subset (hyp_of h) G) B" by (rule subset_bool[OF hh G])
        have bothB: "(conc_of h = conc_of J \<and> subset (hyp_of h) G) B"
          using eqcB subBd by simp
        show R
        proof (rule cases_bool[where q="conc_of h = conc_of J \<and> subset (hyp_of h) G"])
          show "(conc_of h = conc_of J \<and> subset (hyp_of h) G) B" by (rule bothB)
        next
          assume both: "conc_of h = conc_of J \<and> subset (hyp_of h) G"
          have hceq: "conc_of h = conc_of J" using both by (rule conjE1)
          have hsub: "subset (hyp_of h) G" using both by (rule conjE2)
          show R using h hrest hceq hsub by (rule H)
        next
          assume nboth: "\<not> (conc_of h = conc_of J \<and> subset (hyp_of h) G)"
          have fst: "find_struct J G t" using nboth C1 by (rule notcond_thenE)
          have IR: "find_struct J G t \<turnstile> R" using IH subt by (rule entailsE)
          show R using IR fst by (rule entailsE)
        qed
      qed
    qed
  qed
  have IR: "find_struct J G ptr \<turnstile> R" using main sub by (rule entailsE)
  show R using IR fs by (rule entailsE)
qed

lemma check_struct_sound:
  assumes J: "J N" and rest: "rest N"
      and chk: "check_struct J rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   sat_hyp (hyp_of K) A \<Longrightarrow> sat (conc_of K) A"
      and satG: "sat_hyp (hyp_of J) A"
  shows "sat (conc_of J) A"
proof -
  have hJ: "hyp_of J N" using J by simp
  have fs: "find_struct J (hyp_of J) rest"
    using chk by (rule defI[OF check_struct_def[where J=J and rest=rest]])
  have sub: "subset rest rest" using rest by (rule subset_refl)
  show ?thesis
  proof (rule find_structE[OF J hJ rest rest sub fs])
    fix K
    assume K: "K N"
       and Km: "mem K rest"
       and Kc: "conc_of K = conc_of J"
       and Ksub: "subset (hyp_of K) (hyp_of J)"
    have hK: "hyp_of K N" using K by simp
    have satKh: "sat_hyp (hyp_of K) A"
      by (rule sat_hyp_subset[OF Ksub hK hJ satG])
    have satK: "sat (conc_of K) A"
      using K Km satKh by (rule prev)
    show "sat (conc_of J) A"
      using Kc satK by (rule eqSubst[where Q = "\<lambda>c. sat c A"])
  qed
qed

lemma eq_prem:
  assumes hJ: "hyp_of J N" and rest: "rest N"
      and a: "a N" and b: "b N"
      and m: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>a, b\<rangle>) rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   sat_hyp (hyp_of K) A \<Longrightarrow> sat (conc_of K) A"
      and satG: "sat_hyp (hyp_of J) A"
  shows "eval a A = eval b A"
proof -
  have ab: "\<langle>a, b\<rangle> N" using a b by simp
  have X: "pack_F F_EQ \<langle>a, b\<rangle> N" by (rule pack_F_N[OF _ ab], simp)
  have KN: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>a, b\<rangle>) N" using hJ X by simp
  have hK: "hyp_of (hyp_of J \<tturnstile> pack_F F_EQ \<langle>a, b\<rangle>) = hyp_of J"
    by (rule cpx_proj[OF hJ X])
  have cK: "conc_of (hyp_of J \<tturnstile> pack_F F_EQ \<langle>a, b\<rangle>) = pack_F F_EQ \<langle>a, b\<rangle>"
    by (rule cpy_proj[OF hJ X])
  have sK: "sat_hyp (hyp_of (hyp_of J \<tturnstile> pack_F F_EQ \<langle>a, b\<rangle>)) A"
    using hK satG by simp
  have s0: "sat (conc_of (hyp_of J \<tturnstile> pack_F F_EQ \<langle>a, b\<rangle>)) A"
    using KN m sK by (rule prev)
  have s: "sat (pack_F F_EQ \<langle>a, b\<rangle>) A" using cK s0 by simp
  have tgX: "tag_F (pack_F F_EQ \<langle>a, b\<rangle>) = F_EQ"
    by (rule tag_pack_F[OF _ ab], simp)
  have ldX: "load_F (pack_F F_EQ \<langle>a, b\<rangle>) = \<langle>a, b\<rangle>"
    by (rule load_pack_F[OF _ ab], simp)
  have E: "eval (cpx (load_F (pack_F F_EQ \<langle>a, b\<rangle>))) A
         = eval (cpy (load_F (pack_F F_EQ \<langle>a, b\<rangle>))) A"
    by (rule sat_formula_eqE[OF X tgX s])
  show ?thesis
    using E ldX a b apply simp
    apply (rule eq_impl_term2)
    apply simp
    done
qed

lemma sat_formula_eqI:
  assumes tg: "tag_F f = F_EQ"
      and eq: "eval (cpx (load_F f)) A = eval (cpy (load_F f)) A"
  shows "sat f A"
proof -
  have eqB: "(eval (cpx (load_F f)) A = eval (cpy (load_F f)) A) B"
    by (rule eqBool[OF eq_impl_term[OF eq] eq_impl_term2[OF eq]])
  have iff: "(if tag_F f = 0 then eval (cpx (load_F f)) A = eval (cpy (load_F f)) A
              else eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A)
             \<longleftrightarrow> (eval (cpx (load_F f)) A = eval (cpy (load_F f)) A)"
    by (rule condI1B[OF tg eqB])
  have imp: "(eval (cpx (load_F f)) A = eval (cpy (load_F f)) A)
             \<longrightarrow> (if tag_F f = 0 then eval (cpx (load_F f)) A = eval (cpy (load_F f)) A
                  else eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A)"
    by (rule iffE2[OF iff])
  have goal_if: "if tag_F f = 0 then eval (cpx (load_F f)) A = eval (cpy (load_F f)) A
                 else eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A"
    by (rule implE[OF imp eq])
  show "sat f A" unfolding sat_def by (rule goal_if)
qed

lemma neq_prem:
  assumes hJ: "hyp_of J N" and rest: "rest N"
      and a: "a N" and b: "b N"
      and m: "mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>a, b\<rangle>) rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   sat_hyp (hyp_of K) A \<Longrightarrow> sat (conc_of K) A"
      and satG: "sat_hyp (hyp_of J) A"
  shows "eval a A \<noteq> eval b A"
proof -
  have ab: "\<langle>a, b\<rangle> N" using a b by simp
  have X: "pack_F F_NEQ \<langle>a, b\<rangle> N" by (rule pack_F_N[OF _ ab], simp)
  have KN: "(hyp_of J \<tturnstile> pack_F F_NEQ \<langle>a, b\<rangle>) N" using hJ X by simp
  have hK: "hyp_of (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>a, b\<rangle>) = hyp_of J"
    by (rule cpx_proj[OF hJ X])
  have cK: "conc_of (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>a, b\<rangle>) = pack_F F_NEQ \<langle>a, b\<rangle>"
    by (rule cpy_proj[OF hJ X])
  have sK: "sat_hyp (hyp_of (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>a, b\<rangle>)) A"
    using hK satG by simp
  have s0: "sat (conc_of (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>a, b\<rangle>)) A"
    using KN m sK by (rule prev)
  have s: "sat (pack_F F_NEQ \<langle>a, b\<rangle>) A" using cK s0 by simp
  have tgX: "tag_F (pack_F F_NEQ \<langle>a, b\<rangle>) = F_NEQ"
    by (rule tag_pack_F[OF _ ab], simp)
  have ntg: "\<not> tag_F (pack_F F_NEQ \<langle>a, b\<rangle>) = F_EQ"
    using tgX by simp
  have ldX: "load_F (pack_F F_NEQ \<langle>a, b\<rangle>) = \<langle>a, b\<rangle>"
    by (rule load_pack_F[OF _ ab], simp)
  have E: "eval (cpx (load_F (pack_F F_NEQ \<langle>a, b\<rangle>))) A
         \<noteq> eval (cpy (load_F (pack_F F_NEQ \<langle>a, b\<rangle>))) A"
    by (rule sat_formula_neqE[OF X ntg s])
  have ldXs: "\<langle>a, b\<rangle> = load_F (pack_F F_NEQ \<langle>a, b\<rangle>)" using ldX by (rule eqSym)
  have px: "cpx (load_F (pack_F F_NEQ \<langle>a, b\<rangle>)) = a"
    using ldXs cpx_proj[OF a b] by (rule eqSubst[where Q = "\<lambda>t. cpx t = a"])
  have py: "cpy (load_F (pack_F F_NEQ \<langle>a, b\<rangle>)) = b"
    using ldXs cpy_proj[OF a b] by (rule eqSubst[where Q = "\<lambda>t. cpy t = b"])
  have E1: "eval a A \<noteq> eval (cpy (load_F (pack_F F_NEQ \<langle>a, b\<rangle>))) A"
    using px E
    by (rule eqSubst[where Q = "\<lambda>t. eval t A \<noteq> eval (cpy (load_F (pack_F F_NEQ \<langle>a, b\<rangle>))) A"])
  show "eval a A \<noteq> eval b A"
    using py E1 by (rule eqSubst[where Q = "\<lambda>t. eval a A \<noteq> eval t A"])
qed

lemma check_eq_rules_sound:
  assumes J: "J N" and rest: "rest N"
      and tg: "tag_F (conc_of J) = F_EQ"
      and chk: "check_eq_rules (hyp_of J) (cpx (load_F (conc_of J)))
                  (cpy (load_F (conc_of J))) (tag_T (cpx (load_F (conc_of J))))
                  (tag_T (cpy (load_F (conc_of J)))) rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   sat_hyp (hyp_of K) A \<Longrightarrow> sat (conc_of K) A"
      and satG: "sat_hyp (hyp_of J) A"
  shows "sat (conc_of J) A"
proof -
  have cJ: "conc_of J N" using J by simp
  have hJ: "hyp_of J N" using J by simp
  have lcJ: "load_F (conc_of J) N" using cJ by (rule load_F_N)
  have aN: "cpx (load_F (conc_of J)) N" using lcJ by (rule cpx_terminates)
  have bN: "cpy (load_F (conc_of J)) N" using lcJ by (rule cpy_terminates)
  have tgA: "tag_T (cpx (load_F (conc_of J))) N" using aN by (rule tag_T_N)
  have tgB: "tag_T (cpy (load_F (conc_of J))) N" using bN by (rule tag_T_N)
  have ztzN: "pack_T T_ZERO 0 N" by (rule pack_T_N[OF _ nat0], simp)
  have Ll: "load_T (cpx (load_F (conc_of J))) N" using aN by (rule load_T_N)
  have Lr: "load_T (cpy (load_F (conc_of J))) N" using bN by (rule load_T_N)
  have LLl: "load_T (load_T (cpx (load_F (conc_of J)))) N" using Ll by (rule load_T_N)
  have cxLl: "cpx (load_T (cpx (load_F (conc_of J)))) N" using Ll by (rule cpx_terminates)
  have cyLl: "cpy (load_T (cpx (load_F (conc_of J)))) N" using Ll by (rule cpy_terminates)
  have cycyLl: "cpy (cpy (load_T (cpx (load_F (conc_of J))))) N"
    using cyLl by (rule cpy_terminates)
  have cxcyLl: "cpx (cpy (load_T (cpx (load_F (conc_of J))))) N"
    using cyLl by (rule cpx_terminates)
  have sucl: "pack_T T_SUC (cpx (load_F (conc_of J))) N" by (rule pack_T_N[OF _ aN], simp)
  have sucr: "pack_T T_SUC (cpy (load_F (conc_of J))) N" by (rule pack_T_N[OF _ bN], simp)
  have tgLL: "tag_T (load_T (cpx (load_F (conc_of J)))) N" using Ll by (rule tag_T_N)
  have sucN: "T_SUC N" by simp
  have predN: "T_PRED N" by simp
  have ifzN: "T_IFZ N" by simp

  (*booleanness of each guard*)
  have e_lz: "(cpx (load_F (conc_of J)) = pack_T T_ZERO 0) B" by (rule eqBool[OF aN ztzN])
  have e_rz: "(cpy (load_F (conc_of J)) = pack_T T_ZERO 0) B" by (rule eqBool[OF bN ztzN])
  have g1B: "(cpx (load_F (conc_of J)) = pack_T T_ZERO 0 \<and>
              cpy (load_F (conc_of J)) = pack_T T_ZERO 0) B"
    using e_lz e_rz by auto

  have pr_ba: "\<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle> N" using bN aN by simp
  have pf2: "pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle> N"
    by (rule pack_F_N[OF _ pr_ba], simp)
  have j2: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) N"
    using hJ pf2 by simp
  have g2B: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest B"
    by (rule mem_bool[OF j2 rest])

  have pr_LlLr: "\<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle> N"
    using Ll Lr by simp
  have pf3: "pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle> N"
    by (rule pack_F_N[OF _ pr_LlLr], simp)
  have j3: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) N"
    using hJ pf3 by simp
  have m3B: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest B"
    by (rule mem_bool[OF j3 rest])
  have e_tgLs: "(tag_T (cpx (load_F (conc_of J))) = T_SUC) B" by (rule eqBool[OF tgA sucN])
  have e_tgRs: "(tag_T (cpy (load_F (conc_of J))) = T_SUC) B" by (rule eqBool[OF tgB sucN])
  have g3B: "(tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
              mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest) B"
    using e_tgLs e_tgRs m3B by auto

  have pr_ss: "\<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle> N"
    using sucl sucr by simp
  have pf4: "pack_F F_EQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle> N"
    by (rule pack_F_N[OF _ pr_ss], simp)
  have j4: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) N"
    using hJ pf4 by simp
  have g4B: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest B"
    by (rule mem_bool[OF j4 rest])

  have pr_bb: "\<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle> N" using bN by simp
  have pfbb: "pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle> N"
    by (rule pack_F_N[OF _ pr_bb], simp)
  have jbb: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) N"
    using hJ pfbb by simp
  have mbbB: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest B"
    by (rule mem_bool[OF jbb rest])

  have e_tgLp: "(tag_T (cpx (load_F (conc_of J))) = T_PRED) B" by (rule eqBool[OF tgA predN])
  have e_tgLLs: "(tag_T (load_T (cpx (load_F (conc_of J)))) = T_SUC) B" by (rule eqBool[OF tgLL sucN])
  have e_LL_r: "(load_T (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J))) B"
    by (rule eqBool[OF LLl bN])
  have g5B: "(tag_T (cpx (load_F (conc_of J))) = T_PRED \<and>
              tag_T (load_T (cpx (load_F (conc_of J)))) = T_SUC \<and>
              load_T (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J)) \<and>
              mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest) B"
    using e_tgLp e_tgLLs e_LL_r mbbB by auto

  have pr_cxZ: "\<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle> N"
    using cxLl ztzN by simp
  have pf_neq_cxZ: "pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle> N"
    by (rule pack_F_N[OF _ pr_cxZ], simp)
  have j_neq_cxZ: "(hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) N"
    using hJ pf_neq_cxZ by simp
  have m6aB: "mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest B"
    by (rule mem_bool[OF j_neq_cxZ rest])
  have pf_eq_cxZ: "pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle> N"
    by (rule pack_F_N[OF _ pr_cxZ], simp)
  have j_eq_cxZ: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) N"
    using hJ pf_eq_cxZ by simp
  have m7aB: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest B"
    by (rule mem_bool[OF j_eq_cxZ rest])

  have e_tgLi: "(tag_T (cpx (load_F (conc_of J))) = T_IFZ) B" by (rule eqBool[OF tgA ifzN])
  have e_r_cycy: "(cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J)))))) B"
    by (rule eqBool[OF bN cycyLl])
  have g6B: "(tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and>
              cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
              mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
              mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest) B"
    using e_tgLi e_r_cycy m6aB mbbB by auto

  have e_r_cxcy: "(cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J)))))) B"
    by (rule eqBool[OF bN cxcyLl])
  have g7B: "(tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and>
              cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
              mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
              mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest) B"
    using e_tgLi e_r_cxcy m7aB mbbB by auto

  (*unfold the checker into its if cases*)
  have R0:
    "if cpx (load_F (conc_of J)) = pack_T T_ZERO 0 \<and> cpy (load_F (conc_of J)) = pack_T T_ZERO 0 then True
     else if mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest then True
     else if tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
             mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest then True
     else if mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest then True
     else if tag_T (cpx (load_F (conc_of J))) = T_PRED \<and> tag_T (load_T (cpx (load_F (conc_of J)))) = T_SUC \<and>
             load_T (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J)) \<and>
             mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
     else if tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
             mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
             mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
     else if tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
             mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
             mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
     else False"
    using chk by (rule defI[OF check_eq_rules_def])

  have main: "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
  proof (rule cases_bool[where q = "cpx (load_F (conc_of J)) = pack_T T_ZERO 0 \<and> cpy (load_F (conc_of J)) = pack_T T_ZERO 0"])
    show "(cpx (load_F (conc_of J)) = pack_T T_ZERO 0 \<and> cpy (load_F (conc_of J)) = pack_T T_ZERO 0) B"
      by (rule g1B)
  next
    assume g1: "cpx (load_F (conc_of J)) = pack_T T_ZERO 0 \<and> cpy (load_F (conc_of J)) = pack_T T_ZERO 0"
    have l0: "cpx (load_F (conc_of J)) = pack_T T_ZERO 0" using g1 by (rule conjE1)
    have r0: "cpy (load_F (conc_of J)) = pack_T T_ZERO 0" using g1 by (rule conjE2)
    have l0S: "pack_T T_ZERO 0 = cpx (load_F (conc_of J))" using l0 by (rule eqSym)
    have lz: "eval (cpx (load_F (conc_of J))) A = 0"
      using l0S eval_zero by (rule eqSubst[where Q = "\<lambda>t. eval t A = 0"])
    have r0S: "pack_T T_ZERO 0 = cpy (load_F (conc_of J))" using r0 by (rule eqSym)
    have rz: "eval (cpy (load_F (conc_of J))) A = 0"
      using r0S eval_zero by (rule eqSubst[where Q = "\<lambda>t. eval t A = 0"])
    have rz': "0 = eval (cpy (load_F (conc_of J))) A" using rz by (rule eqSym)
    show "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
      using lz rz' by (rule eq_trans)
  next
    assume n1: "\<not> (cpx (load_F (conc_of J)) = pack_T T_ZERO 0 \<and> cpy (load_F (conc_of J)) = pack_T T_ZERO 0)"
    have R1:
      "if mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest then True
       else if tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
               mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest then True
       else if mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest then True
       else if tag_T (cpx (load_F (conc_of J))) = T_PRED \<and> tag_T (load_T (cpx (load_F (conc_of J)))) = T_SUC \<and>
               load_T (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J)) \<and>
               mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
       else if tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
               mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
               mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
       else if tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
               mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
               mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
       else False"
      using n1 R0 by (rule notcond_thenE)
    show "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
    proof (rule cases_bool[where q = "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest"])
      show "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest B"
        by (rule g2B)
    next
      assume g2: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest"
      have e: "eval (cpy (load_F (conc_of J))) A = eval (cpx (load_F (conc_of J))) A"
        by (rule eq_prem[OF hJ rest bN aN g2 prev satG])
      show "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
        using e by (rule eqSym)
    next
      assume n2: "\<not> mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest"
      have R2:
        "if tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
             mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest then True
         else if mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest then True
         else if tag_T (cpx (load_F (conc_of J))) = T_PRED \<and> tag_T (load_T (cpx (load_F (conc_of J)))) = T_SUC \<and>
                 load_T (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J)) \<and>
                 mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
         else if tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                 mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                 mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
         else if tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                 mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                 mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
         else False"
        using n2 R1 by (rule notcond_thenE)
      show "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
      proof (rule cases_bool[where q = "tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
             mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest"])
        show "(tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
             mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest) B"
          by (rule g3B)
      next
        assume g3: "tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
             mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest"
        have g3l: "tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC"
          using g3 by (rule conjE1)
        have m3: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest"
          using g3 by (rule conjE2)
        have c3a: "tag_T (cpx (load_F (conc_of J))) = T_SUC" using g3l by (rule conjE1)
        have c3b: "tag_T (cpy (load_F (conc_of J))) = T_SUC" using g3l by (rule conjE2)
        have eLoad: "eval (load_T (cpx (load_F (conc_of J)))) A = eval (load_T (cpy (load_F (conc_of J)))) A"
          by (rule eq_prem[OF hJ rest Ll Lr m3 prev satG])
        have eSuc: "S (eval (load_T (cpx (load_F (conc_of J)))) A) = S (eval (load_T (cpy (load_F (conc_of J)))) A)"
          by (rule sucCong[OF eLoad])
        have e1: "eval (cpx (load_F (conc_of J))) A = S (eval (load_T (cpy (load_F (conc_of J)))) A)"
          apply (rule eval_sucI[where Q = "\<lambda>v. v = S (eval (load_T (cpy (load_F (conc_of J)))) A)"])
            apply (rule aN)
           apply (rule c3a)
          apply (rule eSuc)
          done
        show "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
          apply (rule eval_sucI[where Q = "\<lambda>v. eval (cpx (load_F (conc_of J))) A = v"])
            apply (rule bN)
           apply (rule c3b)
          apply (rule e1)
          done
      next
        assume n3: "\<not> (tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
             mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest)"
        have R3:
          "if mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest then True
           else if tag_T (cpx (load_F (conc_of J))) = T_PRED \<and> tag_T (load_T (cpx (load_F (conc_of J)))) = T_SUC \<and>
                   load_T (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J)) \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
           else if tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
           else if tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
           else False"
          using n3 R2 by (rule notcond_thenE)
        show "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
        proof (rule cases_bool[where q = "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest"])
          show "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest B"
            by (rule g4B)
        next
          assume g4: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest"
          have eSS: "eval (pack_T T_SUC (cpx (load_F (conc_of J)))) A = eval (pack_T T_SUC (cpy (load_F (conc_of J)))) A"
            by (rule eq_prem[OF hJ rest sucl sucr g4 prev satG])
          have tg_tsl: "tag_T (pack_T T_SUC (cpx (load_F (conc_of J)))) = T_SUC"
            by (rule tag_pack_T[OF _ aN], simp)
          have ld_tsl: "load_T (pack_T T_SUC (cpx (load_F (conc_of J)))) = cpx (load_F (conc_of J))"
            by (rule load_pack_T[OF _ aN], simp)
          have tg_tsr: "tag_T (pack_T T_SUC (cpy (load_F (conc_of J)))) = T_SUC"
            by (rule tag_pack_T[OF _ bN], simp)
          have ld_tsr: "load_T (pack_T T_SUC (cpy (load_F (conc_of J)))) = cpy (load_F (conc_of J))"
            by (rule load_pack_T[OF _ bN], simp)
          have sL: "S (eval (load_T (pack_T T_SUC (cpx (load_F (conc_of J))))) A) = eval (pack_T T_SUC (cpy (load_F (conc_of J)))) A"
            apply (rule eval_sucD[where Q = "\<lambda>v. v = eval (pack_T T_SUC (cpy (load_F (conc_of J)))) A"])
              apply (rule sucl)
             apply (rule tg_tsl)
            apply (rule eSS)
            done
          have sL': "S (eval (cpx (load_F (conc_of J))) A) = eval (pack_T T_SUC (cpy (load_F (conc_of J)))) A"
            using ld_tsl sL
            by (rule eqSubst[where Q = "\<lambda>t. S (eval t A) = eval (pack_T T_SUC (cpy (load_F (conc_of J)))) A"])
          have sR: "S (eval (cpx (load_F (conc_of J))) A) = S (eval (load_T (pack_T T_SUC (cpy (load_F (conc_of J))))) A)"
            apply (rule eval_sucD[where Q = "\<lambda>v. S (eval (cpx (load_F (conc_of J))) A) = v"])
              apply (rule sucr)
             apply (rule tg_tsr)
            apply (rule sL')
            done
          have sR': "S (eval (cpx (load_F (conc_of J))) A) = S (eval (cpy (load_F (conc_of J))) A)"
            using ld_tsr sR
            by (rule eqSubst[where Q = "\<lambda>t. S (eval (cpx (load_F (conc_of J))) A) = S (eval t A)"])
          show "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
            using sR' by (rule sucInj)
        next
          assume n4: "\<not> mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest"
          have R4:
            "if tag_T (cpx (load_F (conc_of J))) = T_PRED \<and> tag_T (load_T (cpx (load_F (conc_of J)))) = T_SUC \<and>
                 load_T (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J)) \<and>
                 mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
             else if tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
             else if tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
             else False"
            using n4 R3 by (rule notcond_thenE)
          show "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
          proof (rule cases_bool[where q = "tag_T (cpx (load_F (conc_of J))) = T_PRED \<and> tag_T (load_T (cpx (load_F (conc_of J)))) = T_SUC \<and>
                 load_T (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J)) \<and>
                 mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest"])
            show "(tag_T (cpx (load_F (conc_of J))) = T_PRED \<and> tag_T (load_T (cpx (load_F (conc_of J)))) = T_SUC \<and>
                 load_T (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J)) \<and>
                 mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest) B"
              by (rule g5B)
          next
            assume g5: "tag_T (cpx (load_F (conc_of J))) = T_PRED \<and> tag_T (load_T (cpx (load_F (conc_of J)))) = T_SUC \<and>
                 load_T (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J)) \<and>
                 mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest"
            have g5l: "(tag_T (cpx (load_F (conc_of J))) = T_PRED \<and> tag_T (load_T (cpx (load_F (conc_of J)))) = T_SUC) \<and>
                 load_T (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J))"
              using g5 by (rule conjE1)
            have c5m: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest"
              using g5 by (rule conjE2)
            have g5ll: "tag_T (cpx (load_F (conc_of J))) = T_PRED \<and> tag_T (load_T (cpx (load_F (conc_of J)))) = T_SUC"
              using g5l by (rule conjE1)
            have c5c: "load_T (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J))"
              using g5l by (rule conjE2)
            have c5a: "tag_T (cpx (load_F (conc_of J))) = T_PRED" using g5ll by (rule conjE1)
            have c5b: "tag_T (load_T (cpx (load_F (conc_of J)))) = T_SUC" using g5ll by (rule conjE2)
            have erefl: "eval (cpy (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
              by (rule eq_prem[OF hJ rest bN bN c5m prev satG])
            have erhsN: "eval (cpy (load_F (conc_of J))) A N" by (rule eq_impl_term[OF erefl])
            have c5cS: "cpy (load_F (conc_of J)) = load_T (load_T (cpx (load_F (conc_of J))))"
              using c5c by (rule eqSym)
            have innerEq: "eval (load_T (load_T (cpx (load_F (conc_of J))))) A = eval (cpy (load_F (conc_of J))) A"
              using c5cS erefl by (rule eqSubst[where Q = "\<lambda>t. eval t A = eval (cpy (load_F (conc_of J))) A"])
            have inner: "eval (load_T (cpx (load_F (conc_of J)))) A = S (eval (cpy (load_F (conc_of J))) A)"
              apply (rule eval_sucI[where Q = "\<lambda>v. v = S (eval (cpy (load_F (conc_of J))) A)"])
                apply (rule Ll)
               apply (rule c5b)
              apply (rule sucCong[OF innerEq])
              done
            have outer: "eval (cpx (load_F (conc_of J))) A = P (S (eval (cpy (load_F (conc_of J))) A))"
              apply (rule eval_predI[where Q = "\<lambda>v. v = P (S (eval (cpy (load_F (conc_of J))) A))"])
                apply (rule aN)
               apply (rule c5a)
              apply (rule predCong[OF inner])
              done
            have psi: "P (S (eval (cpy (load_F (conc_of J))) A)) = eval (cpy (load_F (conc_of J))) A"
              by (rule predSucInv[OF erhsN])
            show "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
              using outer psi by (rule eq_trans)
          next
            assume n5: "\<not> (tag_T (cpx (load_F (conc_of J))) = T_PRED \<and> tag_T (load_T (cpx (load_F (conc_of J)))) = T_SUC \<and>
                 load_T (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J)) \<and>
                 mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest)"
            have R5:
              "if tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
               else if tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                       mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                       mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
               else False"
              using n5 R4 by (rule notcond_thenE)
            show "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
            proof (rule cases_bool[where q = "tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest"])
              show "(tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest) B"
                by (rule g6B)
            next
              assume g6: "tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest"
              have g6l: "(tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and>
                     cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J)))))) \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest"
                using g6 by (rule conjE1)
              have c6m2: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest"
                using g6 by (rule conjE2)
              have g6ll: "tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and>
                     cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J)))))"
                using g6l by (rule conjE1)
              have c6m1: "mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest"
                using g6l by (rule conjE2)
              have c6a: "tag_T (cpx (load_F (conc_of J))) = T_IFZ" using g6ll by (rule conjE1)
              have c6b: "cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J)))))"
                using g6ll by (rule conjE2)
              have neqc: "eval (cpx (load_T (cpx (load_F (conc_of J))))) A \<noteq> eval (pack_T T_ZERO 0) A"
                by (rule neq_prem[OF hJ rest cxLl ztzN c6m1 prev satG])
              have neqc0: "\<not> (eval (cpx (load_T (cpx (load_F (conc_of J))))) A = 0)"
                using eval_zero neqc[unfolded neq_def]
                by (rule eqSubst[where Q = "\<lambda>t. \<not> (eval (cpx (load_T (cpx (load_F (conc_of J))))) A = t)"])
              have erefl: "eval (cpy (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
                by (rule eq_prem[OF hJ rest bN bN c6m2 prev satG])
              have hb: "eval (cpy (cpy (load_T (cpx (load_F (conc_of J)))))) A = eval (cpy (load_F (conc_of J))) A"
                using c6b erefl by (rule eqSubst[where Q = "\<lambda>t. eval t A = eval (cpy (load_F (conc_of J))) A"])
              have bbN: "eval (cpy (cpy (load_T (cpx (load_F (conc_of J)))))) A N"
                by (rule eq_impl_term[OF hb])
              have ifred: "(if eval (cpx (load_T (cpx (load_F (conc_of J))))) A = 0
                            then eval (cpx (cpy (load_T (cpx (load_F (conc_of J)))))) A
                            else eval (cpy (cpy (load_T (cpx (load_F (conc_of J)))))) A)
                           = eval (cpy (cpy (load_T (cpx (load_F (conc_of J)))))) A"
                by (rule condI2[OF neqc0 bbN])
              have ifeq: "(if eval (cpx (load_T (cpx (load_F (conc_of J))))) A = 0
                            then eval (cpx (cpy (load_T (cpx (load_F (conc_of J)))))) A
                            else eval (cpy (cpy (load_T (cpx (load_F (conc_of J)))))) A)
                          = eval (cpy (load_F (conc_of J))) A"
                using ifred hb by (rule eq_trans)
              show "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
                apply (rule eval_ifzI[where Q = "\<lambda>v. v = eval (cpy (load_F (conc_of J))) A"])
                  apply (rule aN)
                 apply (rule c6a)
                apply (rule ifeq)
                done
            next
              assume n6: "\<not> (tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpy (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                   mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest)"
              have R6:
                "if tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest then True
                 else False"
                using n6 R5 by (rule notcond_thenE)
              show "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
              proof (rule cases_bool[where q = "tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest"])
                show "(tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest) B"
                  by (rule g7B)
              next
                assume g7: "tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest"
                have g7l: "(tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and>
                       cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J)))))) \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest"
                  using g7 by (rule conjE1)
                have c7m2: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest"
                  using g7 by (rule conjE2)
                have g7ll: "tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and>
                       cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J)))))"
                  using g7l by (rule conjE1)
                have c7m1: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest"
                  using g7l by (rule conjE2)
                have c7a: "tag_T (cpx (load_F (conc_of J))) = T_IFZ" using g7ll by (rule conjE1)
                have c7b: "cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J)))))"
                  using g7ll by (rule conjE2)
                have eqc: "eval (cpx (load_T (cpx (load_F (conc_of J))))) A = eval (pack_T T_ZERO 0) A"
                  by (rule eq_prem[OF hJ rest cxLl ztzN c7m1 prev satG])
                have eqc0: "eval (cpx (load_T (cpx (load_F (conc_of J))))) A = 0"
                  using eqc eval_zero by (rule eq_trans)
                have erefl: "eval (cpy (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
                  by (rule eq_prem[OF hJ rest bN bN c7m2 prev satG])
                have ha: "eval (cpx (cpy (load_T (cpx (load_F (conc_of J)))))) A = eval (cpy (load_F (conc_of J))) A"
                  using c7b erefl by (rule eqSubst[where Q = "\<lambda>t. eval t A = eval (cpy (load_F (conc_of J))) A"])
                have aaN: "eval (cpx (cpy (load_T (cpx (load_F (conc_of J)))))) A N"
                  by (rule eq_impl_term[OF ha])
                have ifred: "(if eval (cpx (load_T (cpx (load_F (conc_of J))))) A = 0
                              then eval (cpx (cpy (load_T (cpx (load_F (conc_of J)))))) A
                              else eval (cpy (cpy (load_T (cpx (load_F (conc_of J)))))) A)
                             = eval (cpx (cpy (load_T (cpx (load_F (conc_of J)))))) A"
                  by (rule condI1[OF eqc0 aaN])
                have ifeq: "(if eval (cpx (load_T (cpx (load_F (conc_of J))))) A = 0
                              then eval (cpx (cpy (load_T (cpx (load_F (conc_of J)))))) A
                              else eval (cpy (cpy (load_T (cpx (load_F (conc_of J)))))) A)
                            = eval (cpy (load_F (conc_of J))) A"
                  using ifred ha by (rule eq_trans)
                show "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
                  apply (rule eval_ifzI[where Q = "\<lambda>v. v = eval (cpy (load_F (conc_of J))) A"])
                    apply (rule aN)
                   apply (rule c7a)
                  apply (rule ifeq)
                  done
              next
                assume n7: "\<not> (tag_T (cpx (load_F (conc_of J))) = T_IFZ \<and> cpy (load_F (conc_of J)) = cpx (cpy (load_T (cpx (load_F (conc_of J))))) \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_T (cpx (load_F (conc_of J)))), pack_T T_ZERO 0\<rangle>) rest \<and>
                     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpy (load_F (conc_of J)), cpy (load_F (conc_of J))\<rangle>) rest)"
                have R7: "False" using n7 R6 by (rule notcond_thenE)
                have contra: "S(zero) = zero" by (rule R7[unfolded False_def])
                show "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
                  by (rule exF[OF contra sucNonZero[OF nat0, unfolded neq_def]])
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  show "sat (conc_of J) A" by (rule sat_formula_eqI[OF tg main])
qed

lemma sat_formula_neqI:
  assumes tg: "\<not> tag_F f = F_EQ"
      and neq: "eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A"
  shows "sat f A"
proof -
  have neqB: "(eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A) B"
    by (rule neq_bool[OF neq_impl_term[OF neq] neq_impl_term2[OF neq]])
  have iff: "(if tag_F f = 0 then eval (cpx (load_F f)) A = eval (cpy (load_F f)) A
              else eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A)
             \<longleftrightarrow> (eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A)"
    by (rule condI2B[OF tg neqB])
  have imp: "(eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A)
             \<longrightarrow> (if tag_F f = 0 then eval (cpx (load_F f)) A = eval (cpy (load_F f)) A
                  else eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A)"
    by (rule iffE2[OF iff])
  have goal_if: "if tag_F f = 0 then eval (cpx (load_F f)) A = eval (cpy (load_F f)) A
                 else eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A"
    by (rule implE[OF imp neq])
  show "sat f A" unfolding sat_def by (rule goal_if)
qed

lemma check_neq_rules_sound:
  assumes J: "J N" and rest: "rest N"
      and tg: "\<not> tag_F (conc_of J) = F_EQ"
      and chk: "check_neq_rules (hyp_of J) (cpx (load_F (conc_of J)))
                  (cpy (load_F (conc_of J))) (tag_T (cpx (load_F (conc_of J))))
                  (tag_T (cpy (load_F (conc_of J)))) rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   sat_hyp (hyp_of K) A \<Longrightarrow> sat (conc_of K) A"
      and satG: "sat_hyp (hyp_of J) A"
  shows "sat (conc_of J) A"
proof -
  have cJ: "conc_of J N" using J by simp
  have hJ: "hyp_of J N" using J by simp
  have lcJ: "load_F (conc_of J) N" using cJ by (rule load_F_N)
  have aN: "cpx (load_F (conc_of J)) N" using lcJ by (rule cpx_terminates)
  have bN: "cpy (load_F (conc_of J)) N" using lcJ by (rule cpy_terminates)
  have tgA: "tag_T (cpx (load_F (conc_of J))) N" using aN by (rule tag_T_N)
  have tgB: "tag_T (cpy (load_F (conc_of J))) N" using bN by (rule tag_T_N)
  have ztzN: "pack_T T_ZERO 0 N" by (rule pack_T_N[OF _ nat0], simp)
  have Ll: "load_T (cpx (load_F (conc_of J))) N" using aN by (rule load_T_N)
  have Lr: "load_T (cpy (load_F (conc_of J))) N" using bN by (rule load_T_N)
  have sucl: "pack_T T_SUC (cpx (load_F (conc_of J))) N" by (rule pack_T_N[OF _ aN], simp)
  have sucr: "pack_T T_SUC (cpy (load_F (conc_of J))) N" by (rule pack_T_N[OF _ bN], simp)
  have sucN: "T_SUC N" by simp

  have pr_rl: "\<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle> N" using bN aN by simp
  have pf1: "pack_F F_NEQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle> N"
    by (rule pack_F_N[OF _ pr_rl], simp)
  have j1: "(hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) N"
    using hJ pf1 by simp
  have g1B: "mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest B"
    by (rule mem_bool[OF j1 rest])

  have pr_ll: "\<langle>load_T (cpx (load_F (conc_of J))), load_T (cpx (load_F (conc_of J)))\<rangle> N" using Ll by simp
  have pf2: "pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpx (load_F (conc_of J)))\<rangle> N"
    by (rule pack_F_N[OF _ pr_ll], simp)
  have j2: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpx (load_F (conc_of J)))\<rangle>) N"
    using hJ pf2 by simp
  have m2B: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpx (load_F (conc_of J)))\<rangle>) rest B"
    by (rule mem_bool[OF j2 rest])
  have e_tgLs: "(tag_T (cpx (load_F (conc_of J))) = T_SUC) B" by (rule eqBool[OF tgA sucN])
  have e_rz: "(cpy (load_F (conc_of J)) = pack_T T_ZERO 0) B" by (rule eqBool[OF bN ztzN])
  have g2B: "(tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> cpy (load_F (conc_of J)) = pack_T T_ZERO 0 \<and>
              mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpx (load_F (conc_of J)))\<rangle>) rest) B"
    using e_tgLs e_rz m2B by auto

  have pr_lr: "\<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle> N" using Ll Lr by simp
  have pf3: "pack_F F_NEQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle> N"
    by (rule pack_F_N[OF _ pr_lr], simp)
  have j3: "(hyp_of J \<tturnstile> pack_F F_NEQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) N"
    using hJ pf3 by simp
  have m3B: "mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest B"
    by (rule mem_bool[OF j3 rest])
  have e_tgRs: "(tag_T (cpy (load_F (conc_of J))) = T_SUC) B" by (rule eqBool[OF tgB sucN])
  have g3B: "(tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
              mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest) B"
    using e_tgLs e_tgRs m3B by auto

  have pr_ss: "\<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle> N"
    using sucl sucr by simp
  have pf4: "pack_F F_NEQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle> N"
    by (rule pack_F_N[OF _ pr_ss], simp)
  have j4: "(hyp_of J \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) N"
    using hJ pf4 by simp
  have g4B: "mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest B"
    by (rule mem_bool[OF j4 rest])

  have R0:
    "if mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest then True
     else if tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> cpy (load_F (conc_of J)) = pack_T T_ZERO 0 \<and>
             mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpx (load_F (conc_of J)))\<rangle>) rest then True
     else if tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
             mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest then True
     else if mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest then True
     else False"
    using chk by (rule defI[OF check_neq_rules_def])

  have main: "eval (cpx (load_F (conc_of J))) A \<noteq> eval (cpy (load_F (conc_of J))) A"
  proof (rule cases_bool[where q = "mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest"])
    show "mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest B"
      by (rule g1B)
  next
    assume g1: "mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest"
    have n1neq: "eval (cpy (load_F (conc_of J))) A \<noteq> eval (cpx (load_F (conc_of J))) A"
      by (rule neq_prem[OF hJ rest bN aN g1 prev satG])
    have g1yN: "eval (cpy (load_F (conc_of J))) A N" by (rule neq_impl_term[OF n1neq])
    have g1xN: "eval (cpx (load_F (conc_of J))) A N" by (rule neq_impl_term2[OF n1neq])
    show "eval (cpx (load_F (conc_of J))) A \<noteq> eval (cpy (load_F (conc_of J))) A"
      by (rule neq_sym[OF g1yN g1xN n1neq])
  next
    assume nn1: "\<not> mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>cpy (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest"
    have R1:
      "if tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> cpy (load_F (conc_of J)) = pack_T T_ZERO 0 \<and>
              mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpx (load_F (conc_of J)))\<rangle>) rest then True
       else if tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
               mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest then True
       else if mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest then True
       else False"
      using nn1 R0 by (rule notcond_thenE)
    show "eval (cpx (load_F (conc_of J))) A \<noteq> eval (cpy (load_F (conc_of J))) A"
    proof (rule cases_bool[where q = "tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> cpy (load_F (conc_of J)) = pack_T T_ZERO 0 \<and>
              mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpx (load_F (conc_of J)))\<rangle>) rest"])
      show "(tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> cpy (load_F (conc_of J)) = pack_T T_ZERO 0 \<and>
              mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpx (load_F (conc_of J)))\<rangle>) rest) B"
        by (rule g2B)
    next
      assume g2: "tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> cpy (load_F (conc_of J)) = pack_T T_ZERO 0 \<and>
              mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpx (load_F (conc_of J)))\<rangle>) rest"
      have g2l: "tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> cpy (load_F (conc_of J)) = pack_T T_ZERO 0"
        using g2 by (rule conjE1)
      have c2m: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpx (load_F (conc_of J)))\<rangle>) rest"
        using g2 by (rule conjE2)
      have c2a: "tag_T (cpx (load_F (conc_of J))) = T_SUC" using g2l by (rule conjE1)
      have c2r: "cpy (load_F (conc_of J)) = pack_T T_ZERO 0" using g2l by (rule conjE2)
      have refl2: "eval (load_T (cpx (load_F (conc_of J)))) A = eval (load_T (cpx (load_F (conc_of J)))) A"
        by (rule eq_prem[OF hJ rest Ll Ll c2m prev satG])
      have laN: "eval (load_T (cpx (load_F (conc_of J)))) A N" by (rule eq_impl_term[OF refl2])
      have snz1: "eval (cpx (load_F (conc_of J))) A \<noteq> 0"
        apply (rule eval_sucI[where Q = "\<lambda>v. v \<noteq> 0"])
          apply (rule aN)
         apply (rule c2a)
        apply (rule sucNonZero[OF laN])
        done
      have c2rS: "pack_T T_ZERO 0 = cpy (load_F (conc_of J))" using c2r by (rule eqSym)
      have rhsE: "eval (cpy (load_F (conc_of J))) A = 0"
        using c2rS eval_zero by (rule eqSubst[where Q = "\<lambda>t. eval t A = 0"])
      have rhsES: "0 = eval (cpy (load_F (conc_of J))) A" using rhsE by (rule eqSym)
      show "eval (cpx (load_F (conc_of J))) A \<noteq> eval (cpy (load_F (conc_of J))) A"
        using rhsES snz1 by (rule eqSubst[where Q = "\<lambda>t. eval (cpx (load_F (conc_of J))) A \<noteq> t"])
    next
      assume nn2: "\<not> (tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> cpy (load_F (conc_of J)) = pack_T T_ZERO 0 \<and>
              mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpx (load_F (conc_of J)))\<rangle>) rest)"
      have R2:
        "if tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
               mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest then True
         else if mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest then True
         else False"
        using nn2 R1 by (rule notcond_thenE)
      show "eval (cpx (load_F (conc_of J))) A \<noteq> eval (cpy (load_F (conc_of J))) A"
      proof (rule cases_bool[where q = "tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
               mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest"])
        show "(tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
               mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest) B"
          by (rule g3B)
      next
        assume g3: "tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
               mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest"
        have g3l: "tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC"
          using g3 by (rule conjE1)
        have c3m: "mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest"
          using g3 by (rule conjE2)
        have c3a: "tag_T (cpx (load_F (conc_of J))) = T_SUC" using g3l by (rule conjE1)
        have c3b: "tag_T (cpy (load_F (conc_of J))) = T_SUC" using g3l by (rule conjE2)
        have nLL: "eval (load_T (cpx (load_F (conc_of J)))) A \<noteq> eval (load_T (cpy (load_F (conc_of J)))) A"
          by (rule neq_prem[OF hJ rest Ll Lr c3m prev satG])
        have llN: "eval (load_T (cpx (load_F (conc_of J)))) A N" by (rule neq_impl_term[OF nLL])
        have lrN: "eval (load_T (cpy (load_F (conc_of J)))) A N" by (rule neq_impl_term2[OF nLL])
        have nSS: "S (eval (load_T (cpx (load_F (conc_of J)))) A) \<noteq> S (eval (load_T (cpy (load_F (conc_of J)))) A)"
          by (rule neq_monotone_suc[OF llN lrN nLL[unfolded neq_def], folded neq_def])
        have m1: "eval (cpx (load_F (conc_of J))) A \<noteq> S (eval (load_T (cpy (load_F (conc_of J)))) A)"
          apply (rule eval_sucI[where Q = "\<lambda>v. v \<noteq> S (eval (load_T (cpy (load_F (conc_of J)))) A)"])
            apply (rule aN)
           apply (rule c3a)
          apply (rule nSS)
          done
        show "eval (cpx (load_F (conc_of J))) A \<noteq> eval (cpy (load_F (conc_of J))) A"
          apply (rule eval_sucI[where Q = "\<lambda>v. eval (cpx (load_F (conc_of J))) A \<noteq> v"])
            apply (rule bN)
           apply (rule c3b)
          apply (rule m1)
          done
      next
        assume nn3: "\<not> (tag_T (cpx (load_F (conc_of J))) = T_SUC \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC \<and>
               mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>load_T (cpx (load_F (conc_of J))), load_T (cpy (load_F (conc_of J)))\<rangle>) rest)"
        have R3:
          "if mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest then True
           else False"
          using nn3 R2 by (rule notcond_thenE)
        show "eval (cpx (load_F (conc_of J))) A \<noteq> eval (cpy (load_F (conc_of J))) A"
        proof (rule cases_bool[where q = "mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest"])
          show "mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest B"
            by (rule g4B)
        next
          assume g4: "mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest"
          have neqSS0: "eval (pack_T T_SUC (cpx (load_F (conc_of J)))) A \<noteq> eval (pack_T T_SUC (cpy (load_F (conc_of J)))) A"
            by (rule neq_prem[OF hJ rest sucl sucr g4 prev satG])
          have tg_tsl: "tag_T (pack_T T_SUC (cpx (load_F (conc_of J)))) = T_SUC"
            by (rule tag_pack_T[OF _ aN], simp)
          have ld_tsl: "load_T (pack_T T_SUC (cpx (load_F (conc_of J)))) = cpx (load_F (conc_of J))"
            by (rule load_pack_T[OF _ aN], simp)
          have tg_tsr: "tag_T (pack_T T_SUC (cpy (load_F (conc_of J)))) = T_SUC"
            by (rule tag_pack_T[OF _ bN], simp)
          have ld_tsr: "load_T (pack_T T_SUC (cpy (load_F (conc_of J)))) = cpy (load_F (conc_of J))"
            by (rule load_pack_T[OF _ bN], simp)
          have sD: "S (eval (load_T (pack_T T_SUC (cpx (load_F (conc_of J))))) A) \<noteq> eval (pack_T T_SUC (cpy (load_F (conc_of J)))) A"
            apply (rule eval_sucD[where Q = "\<lambda>v. v \<noteq> eval (pack_T T_SUC (cpy (load_F (conc_of J)))) A"])
              apply (rule sucl)
             apply (rule tg_tsl)
            apply (rule neqSS0)
            done
          have sD': "S (eval (cpx (load_F (conc_of J))) A) \<noteq> eval (pack_T T_SUC (cpy (load_F (conc_of J)))) A"
            using ld_tsl sD
            by (rule eqSubst[where Q = "\<lambda>t. S (eval t A) \<noteq> eval (pack_T T_SUC (cpy (load_F (conc_of J)))) A"])
          have sD2: "S (eval (cpx (load_F (conc_of J))) A) \<noteq> S (eval (load_T (pack_T T_SUC (cpy (load_F (conc_of J))))) A)"
            apply (rule eval_sucD[where Q = "\<lambda>v. S (eval (cpx (load_F (conc_of J))) A) \<noteq> v"])
              apply (rule sucr)
             apply (rule tg_tsr)
            apply (rule sD')
            done
          have nSS: "S (eval (cpx (load_F (conc_of J))) A) \<noteq> S (eval (cpy (load_F (conc_of J))) A)"
            using ld_tsr sD2
            by (rule eqSubst[where Q = "\<lambda>t. S (eval (cpx (load_F (conc_of J))) A) \<noteq> S (eval t A)"])
          have sllN: "S (eval (cpx (load_F (conc_of J))) A) N" by (rule neq_impl_term[OF nSS])
          have srrN: "S (eval (cpy (load_F (conc_of J))) A) N" by (rule neq_impl_term2[OF nSS])
          have elhsN: "eval (cpx (load_F (conc_of J))) A N" by (rule natSI[OF sllN])
          have erhsN: "eval (cpy (load_F (conc_of J))) A N" by (rule natSI[OF srrN])
          show "eval (cpx (load_F (conc_of J))) A \<noteq> eval (cpy (load_F (conc_of J))) A"
          proof (rule cases_bool[where q = "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"])
            show "(eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A) B"
              by (rule eqBool[OF elhsN erhsN])
          next
            assume h: "eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A"
            have hs: "S (eval (cpx (load_F (conc_of J))) A) = S (eval (cpy (load_F (conc_of J))) A)"
              by (rule sucCong[OF h])
            show "eval (cpx (load_F (conc_of J))) A \<noteq> eval (cpy (load_F (conc_of J))) A"
              by (rule exF[OF hs nSS[unfolded neq_def]])
          next
            assume h: "\<not> (eval (cpx (load_F (conc_of J))) A = eval (cpy (load_F (conc_of J))) A)"
            show "eval (cpx (load_F (conc_of J))) A \<noteq> eval (cpy (load_F (conc_of J))) A"
              unfolding neq_def by (rule h)
          qed
        next
          assume nn4: "\<not> mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC (cpx (load_F (conc_of J))), pack_T T_SUC (cpy (load_F (conc_of J)))\<rangle>) rest"
          have R4: "False" using nn4 R3 by (rule notcond_thenE)
          have contra: "S(zero) = zero" by (rule R4[unfolded False_def])
          show "eval (cpx (load_F (conc_of J))) A \<noteq> eval (cpy (load_F (conc_of J))) A"
            by (rule exF[OF contra sucNonZero[OF nat0, unfolded neq_def]])
        qed
      qed
    qed
  qed
  show "sat (conc_of J) A" by (rule sat_formula_neqI[OF tg main])
qed

lemma valid_step_sound:
  assumes J: "J N" and rest: "rest N"
      and vs: "valid_step J rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   sat_hyp (hyp_of K) A \<Longrightarrow> sat (conc_of K) A"
      and prevN: "\<And>K A2. A2 N \<Longrightarrow> K N \<Longrightarrow> mem K rest \<Longrightarrow>
                    sat_hyp (hyp_of K) A2 \<Longrightarrow> sat (conc_of K) A2"
      and satG: "sat_hyp (hyp_of J) A"
      and AN: "A N"
  shows "sat (conc_of J) A"
proof -
  have cJ: "conc_of J N"
    using J by simp
  have hJ: "hyp_of J N"
    using J by simp
  have feqN: "F_EQ N"
    by simp
  have R0:
    "if mem (conc_of J) (hyp_of J) then True
     else if check_cut J rest then True
     else if check_subst J rest then True
     else if check_ind J rest then True
     else if check_app J rest then True
     else if check_struct J rest then True
     else if tag_F (conc_of J) = F_EQ then
       check_eq_rules (hyp_of J) (cpx (load_F (conc_of J)))
         (cpy (load_F (conc_of J)))
         (tag_T (cpx (load_F (conc_of J))))
         (tag_T (cpy (load_F (conc_of J)))) rest
     else
       check_neq_rules (hyp_of J) (cpx (load_F (conc_of J)))
         (cpy (load_F (conc_of J)))
         (tag_T (cpx (load_F (conc_of J))))
         (tag_T (cpy (load_F (conc_of J)))) rest"
    using vs by (rule defI[OF valid_step_def])
  show ?thesis
  proof (rule cases_bool[where q="mem (conc_of J) (hyp_of J)"])
    show "mem (conc_of J) (hyp_of J) B"
      by (rule mem_bool[OF cJ hJ])
  next
    assume g0: "mem (conc_of J) (hyp_of J)"
    show ?thesis
      by (rule sat_hyp_mem[OF cJ g0 satG])
  next
    assume n0: "\<not> mem (conc_of J) (hyp_of J)"
    have R1:
      "if check_cut J rest then True
       else if check_subst J rest then True
       else if check_ind J rest then True
       else if check_app J rest then True
       else if check_struct J rest then True
       else if tag_F (conc_of J) = F_EQ then
         check_eq_rules (hyp_of J) (cpx (load_F (conc_of J)))
           (cpy (load_F (conc_of J)))
           (tag_T (cpx (load_F (conc_of J))))
           (tag_T (cpy (load_F (conc_of J)))) rest
       else
         check_neq_rules (hyp_of J) (cpx (load_F (conc_of J)))
           (cpy (load_F (conc_of J)))
           (tag_T (cpx (load_F (conc_of J))))
           (tag_T (cpy (load_F (conc_of J)))) rest"
      using n0 R0 by (rule notcond_thenE)
    show ?thesis
    proof (rule cases_bool[where q="check_cut J rest"])
      show "check_cut J rest B"
        by (rule check_cut_bool[OF J rest])
    next
      assume g1: "check_cut J rest"
      show ?thesis
        by (rule check_cut_sound[OF J rest g1 prev satG])
    next
      assume n1: "\<not> check_cut J rest"
      have R2:
        "if check_subst J rest then True
         else if check_ind J rest then True
         else if check_app J rest then True
         else if check_struct J rest then True
         else if tag_F (conc_of J) = F_EQ then
           check_eq_rules (hyp_of J) (cpx (load_F (conc_of J)))
             (cpy (load_F (conc_of J)))
             (tag_T (cpx (load_F (conc_of J))))
             (tag_T (cpy (load_F (conc_of J)))) rest
         else
           check_neq_rules (hyp_of J) (cpx (load_F (conc_of J)))
             (cpy (load_F (conc_of J)))
             (tag_T (cpx (load_F (conc_of J))))
             (tag_T (cpy (load_F (conc_of J)))) rest"
        using n1 R1 by (rule notcond_thenE)
      show ?thesis
      proof (rule cases_bool[where q="check_subst J rest"])
        show "check_subst J rest B"
          by (rule check_subst_bool[OF J rest])
      next
        assume g2: "check_subst J rest"
        show ?thesis
          by (rule check_subst_sound[OF J rest g2 prev satG])
      next
        assume n2: "\<not> check_subst J rest"
        have R3:
          "if check_ind J rest then True
           else if check_app J rest then True
           else if check_struct J rest then True
           else if tag_F (conc_of J) = F_EQ then
             check_eq_rules (hyp_of J) (cpx (load_F (conc_of J)))
               (cpy (load_F (conc_of J)))
               (tag_T (cpx (load_F (conc_of J))))
               (tag_T (cpy (load_F (conc_of J)))) rest
           else
             check_neq_rules (hyp_of J) (cpx (load_F (conc_of J)))
               (cpy (load_F (conc_of J)))
               (tag_T (cpx (load_F (conc_of J))))
               (tag_T (cpy (load_F (conc_of J)))) rest"
          using n2 R2 by (rule notcond_thenE)
        show ?thesis
        proof (rule cases_bool[where q="check_ind J rest"])
          show "check_ind J rest B"
            by (rule check_ind_bool[OF J rest])
        next
          assume g3: "check_ind J rest"
          show ?thesis
            by (rule check_ind_sound[OF J rest g3 prev prevN satG AN])
        next
          assume n3: "\<not> check_ind J rest"
          have R4:
            "if check_app J rest then True
             else if check_struct J rest then True
             else if tag_F (conc_of J) = F_EQ then
               check_eq_rules (hyp_of J) (cpx (load_F (conc_of J)))
                 (cpy (load_F (conc_of J)))
                 (tag_T (cpx (load_F (conc_of J))))
                 (tag_T (cpy (load_F (conc_of J)))) rest
             else
               check_neq_rules (hyp_of J) (cpx (load_F (conc_of J)))
                 (cpy (load_F (conc_of J)))
                 (tag_T (cpx (load_F (conc_of J))))
                 (tag_T (cpy (load_F (conc_of J)))) rest"
            using n3 R3 by (rule notcond_thenE)
          show ?thesis
          proof (rule cases_bool[where q="check_app J rest"])
            show "check_app J rest B"
              by (rule check_app_bool[OF J rest])
          next
            assume g4: "check_app J rest"
            show ?thesis
              by (rule check_app_sound[OF J rest g4 prev satG])
          next
            assume n4: "\<not> check_app J rest"
            have R5:
              "if check_struct J rest then True
               else if tag_F (conc_of J) = F_EQ then
                 check_eq_rules (hyp_of J) (cpx (load_F (conc_of J)))
                   (cpy (load_F (conc_of J)))
                   (tag_T (cpx (load_F (conc_of J))))
                   (tag_T (cpy (load_F (conc_of J)))) rest
               else
                 check_neq_rules (hyp_of J) (cpx (load_F (conc_of J)))
                   (cpy (load_F (conc_of J)))
                   (tag_T (cpx (load_F (conc_of J))))
                   (tag_T (cpy (load_F (conc_of J)))) rest"
              using n4 R4 by (rule notcond_thenE)
            show ?thesis
            proof (rule cases_bool[where q="check_struct J rest"])
              show "check_struct J rest B"
                by (rule check_struct_bool[OF J rest])
            next
              assume g5: "check_struct J rest"
              show ?thesis
                by (rule check_struct_sound[OF J rest g5 prev satG])
            next
              assume n5: "\<not> check_struct J rest"
              have R6:
                "if tag_F (conc_of J) = F_EQ then
                   check_eq_rules (hyp_of J) (cpx (load_F (conc_of J)))
                     (cpy (load_F (conc_of J)))
                     (tag_T (cpx (load_F (conc_of J))))
                     (tag_T (cpy (load_F (conc_of J)))) rest
                 else
                   check_neq_rules (hyp_of J) (cpx (load_F (conc_of J)))
                     (cpy (load_F (conc_of J)))
                     (tag_T (cpx (load_F (conc_of J))))
                     (tag_T (cpy (load_F (conc_of J)))) rest"
                using n5 R5 by (rule notcond_thenE)
              show ?thesis
              proof (rule cases_bool[where q="tag_F (conc_of J) = F_EQ"])
                show "(tag_F (conc_of J) = F_EQ) B"
                  by (rule eqBool[OF tag_F_N[OF cJ] feqN])
              next
                assume g6: "tag_F (conc_of J) = F_EQ"
                have C6:
                  "check_eq_rules (hyp_of J)
                     (cpx (load_F (conc_of J)))
                     (cpy (load_F (conc_of J)))
                     (tag_T (cpx (load_F (conc_of J))))
                     (tag_T (cpy (load_F (conc_of J)))) rest"
                  using g6 R6 by (rule cond_thenE)
                show ?thesis
                  by (rule check_eq_rules_sound[OF J rest g6 C6 prev satG])
              next
                assume n6: "\<not> tag_F (conc_of J) = F_EQ"
                have C6:
                  "check_neq_rules (hyp_of J)
                     (cpx (load_F (conc_of J)))
                     (cpy (load_F (conc_of J)))
                     (tag_T (cpx (load_F (conc_of J))))
                     (tag_T (cpy (load_F (conc_of J)))) rest"
                  using n6 R6 by (rule notcond_thenE)
                show ?thesis
                  by (rule check_neq_rules_sound[OF J rest n6 C6 prev satG])
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma check_list_sound_N:
  assumes pf: "pf N"
  shows "\<And>J A. A N \<Longrightarrow> check_list pf \<Longrightarrow> J N \<Longrightarrow> mem J pf \<Longrightarrow>
                sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
proof (rule check_list_induct_N[OF pf])
  show "\<And>J A. A N \<Longrightarrow> check_list Nil \<Longrightarrow> J N \<Longrightarrow> mem J Nil \<Longrightarrow>
               sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
  proof -
    fix J A
    assume A: "A N"
       and chk: "check_list Nil"
       and J: "J N"
       and m: "mem J Nil"
       and satG: "sat_hyp (hyp_of J) A"
    show "sat (conc_of J) A"
      by (rule exF[OF m mem_nil])
  qed
next
  fix h t
  assume h: "h N"
     and t: "t N"
     and IH:
       "\<And>J A. A N \<Longrightarrow> check_list t \<Longrightarrow> J N \<Longrightarrow> mem J t \<Longrightarrow>
          sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
  show "\<And>J A. A N \<Longrightarrow> check_list (Cons h t) \<Longrightarrow> J N \<Longrightarrow>
               mem J (Cons h t) \<Longrightarrow>
               sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
  proof -
    fix J A
    assume A: "A N"
       and cl: "check_list (Cons h t)"
       and J: "J N"
       and mJ: "mem J (Cons h t)"
       and satG: "sat_hyp (hyp_of J) A"
    have hne: "\<not> Cons h t = Nil"
      using h t by simp
    have R0:
      "if Cons h t = Nil then True
       else if valid_step (list_hd (Cons h t)) (list_tl (Cons h t))
       then check_list (list_tl (Cons h t))
       else False"
      using cl
      by (rule defI[OF check_list_def[where pf="Cons h t"]])
    have R:
      "if Cons h t = Nil then True
       else if valid_step h t then check_list t else False"
      using R0
      by (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
    have R1: "if valid_step h t then check_list t else False"
      using hne R by (rule notcond_thenE)
    show "sat (conc_of J) A"
    proof (rule cases_bool[where q="valid_step h t"])
      show "valid_step h t B"
        by (rule valid_step_bool[OF h t])
    next
      assume vs: "valid_step h t"
      have clt: "check_list t"
        using vs R1 by (rule cond_thenE)
      have mJ': "if h = J then True else mem J t"
        using mJ h t J
        by (simp add: mem_cons[OF h t J])
      show "sat (conc_of J) A"
      proof (rule cases_bool[where q="h = J"])
        show "(h = J) B"
          by (rule eqBool[OF h J])
      next
        assume hJ: "h = J"
        have Jh: "J = h"
          using hJ by (rule eqSym)
        have satGh: "sat_hyp (hyp_of h) A"
          using Jh satG
          by (rule eqSubst[where Q="\<lambda>z. sat_hyp (hyp_of z) A"])
        have sh: "sat (conc_of h) A"
        proof (rule valid_step_sound[OF h t vs])
          fix K
          assume K: "K N"
             and mK: "mem K t"
             and satK: "sat_hyp (hyp_of K) A"
          show "sat (conc_of K) A"
            using A clt K mK satK by (rule IH)
        next
          fix K A2
          assume A2: "A2 N"
             and K: "K N"
             and mK: "mem K t"
             and satK: "sat_hyp (hyp_of K) A2"
          show "sat (conc_of K) A2"
            using A2 clt K mK satK by (rule IH)
        next
          show "sat_hyp (hyp_of h) A"
            by (rule satGh)
        next
          show "A N"
            by (rule A)
        qed
        show "sat (conc_of J) A"
          using hJ sh
          by (rule eqSubst[where Q="\<lambda>z. sat (conc_of z) A"])
      next
        assume nhJ: "\<not> h = J"
        have mJt: "mem J t"
          using nhJ mJ' by (rule notcond_thenE)
        show "sat (conc_of J) A"
          using A clt J mJt satG by (rule IH)
      qed
    next
      assume nvs: "\<not> valid_step h t"
      have F: "False"
        using nvs R1 by (rule notcond_thenE)
      show "sat (conc_of J) A"
        by (rule exF[OF F not_false])
    qed
  qed
qed

lemma soundness_bridge:
  assumes vp: "is_valid_proof p J"
      and satG: "sat_hyp (hyp_of J) A"
      and AN: "A N"
  shows "sat (conc_of J) A"
proof -
  have vpB: "is_valid_proof p J B"
    using vp by simp
  have RB:
    "(if p = Nil then False
      else if list_hd p = J then check_list p else False) B"
    using vpB by (rule defI[OF is_valid_proof_def])
  have pnilB: "(p = Nil) B"
    by (rule condE3B[OF RB])
  have PN: "(p N) \<and> (Nil N)"
    by (rule eqE[OF pnilB])
  have p: "p N"
    using PN by (rule conjE1)
  have R:
    "if p = Nil then False
     else if list_hd p = J then check_list p else False"
    using vp by (rule defI[OF is_valid_proof_def])
  show ?thesis
  proof (rule cases_bool[where q="p = Nil"])
    show "(p = Nil) B" by (rule pnilB)
  next
    assume pe: "p = Nil"
    have F: "False" using pe R by (rule cond_thenE)
    show ?thesis by (rule exF[OF F not_false])
  next
    assume pne: "\<not> p = Nil"
    have inner: "if list_hd p = J then check_list p else False"
      using pne R by (rule notcond_thenE)
    have innerB: "(if list_hd p = J then check_list p else False) B"
      using inner by simp
    have hJB: "(list_hd p = J) B"
      by (rule condE3B[OF innerB])
    have HN: "(list_hd p N) \<and> (J N)"
      by (rule eqE[OF hJB])
    have hN: "list_hd p N"
      using HN by (rule conjE1)
    have JN: "J N"
      using HN by (rule conjE2)
    show ?thesis
    proof (rule cases_bool[where q="list_hd p = J"])
      show "(list_hd p = J) B" by (rule hJB)
    next
      assume hJ: "list_hd p = J"
      have cp: "check_list p"
        using hJ inner by (rule cond_thenE)
      have tpN: "list_tl p N"
        by (rule list_tl_nat[OF p])
      have rec: "list_hd p \<triangleright> list_tl p = p"
        by (rule cons_reconstr[OF p pne])
      have mh0: "list_hd p \<in> (list_hd p \<triangleright> list_tl p)"
        by (rule mem_cons_head[OF hN tpN])
      have mh: "list_hd p \<in> p"
        using rec mh0 by (rule eqSubst[where Q="\<lambda>L. list_hd p \<in> L"])
      have mJ: "J \<in> p"
        using hJ mh by (rule eqSubst[where Q="\<lambda>x. x \<in> p"])
      show ?thesis
        using p AN cp JN mJ satG by (rule check_list_sound_N)
    next
      assume nhJ: "\<not> list_hd p = J"
      have F: "False" using nhJ inner by (rule notcond_thenE)
      show ?thesis by (rule exF[OF F not_false])
    qed
  qed
qed


(* OLD interpretation (functional eval), retained inside the dead block for reference: *)
sublocale consistent mk_eq mk_neq dfns is_valid_proof eval sat sat_hyp
proof (unfold_locales)
  show "\<And>a b.   a N \<Longrightarrow> b N \<Longrightarrow> mk_eq a b N"                         
    by (rule mk_eq_N')
  show "\<And>a b.   a N \<Longrightarrow> b N \<Longrightarrow> mk_neq a b N"                        
    by (rule mk_neq_N')
  show "\<And>p J.   p N \<Longrightarrow> J N \<Longrightarrow> is_valid_proof p J B"                
    by (rule proof_is_bool)
  show "\<And>A.     sat_hyp Nil A"                                          
    by (rule sat_hyp_nil')
  show "\<And>a b A. a N \<Longrightarrow> b N \<Longrightarrow> sat (mk_eq a b) A \<Longrightarrow> eval a A = eval b A"   
    by (rule sat_eqE')
  show "\<And>a b A. a N \<Longrightarrow> b N \<Longrightarrow> sat (mk_neq a b) A \<Longrightarrow> eval a A \<noteq> eval b A"  
    by (rule sat_neqE')
  show "\<And>p J A. is_valid_proof p J \<Longrightarrow> sat_hyp (hyp_of J) A \<Longrightarrow> A N \<Longrightarrow> sat (conc_of J) A"
    by (rule soundness_bridge)
qed

end
===== end DEAD CODE (bga_full) ===== *)

locale bga_fuller = bga_fuel_subst_semantics + bga_proof_check

begin 

lemma app_tryE:
  assumes J: "J N" and d: "d N" and x: "x N" and y: "y N" and rest: "rest N"
      and app: "app_try J d x y rest"
      and H: "dfn_is d 2 (nth d dfns) \<Longrightarrow>
        mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) rest \<Longrightarrow>
        mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) rest \<Longrightarrow>
        find_phi J (subst_body (nth d dfns) x y)
          (pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>) rest \<Longrightarrow> R"
  shows R
proof -
  have facts:
    "dfn_is d 2 (nth d dfns) \<and>
     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) rest \<and>
     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) rest \<and>
     find_phi J (subst_body (nth d dfns) x y)
       (pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>) rest"
    using app by (rule defI[OF app_try_def[where J=J and d=d and x=x and y=y and rest=rest]])
  have firstThree:
    "dfn_is d 2 (nth d dfns) \<and>
     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) rest \<and>
     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) rest"
    by (rule conjE1[OF facts])
  have fp:
    "find_phi J (subst_body (nth d dfns) x y)
      (pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>) rest"
    by (rule conjE2[OF facts])
  have firstTwo:
    "dfn_is d 2 (nth d dfns) \<and>
     mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) rest"
    by (rule conjE1[OF firstThree])
  have my: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) rest"
    by (rule conjE2[OF firstThree])
  have di: "dfn_is d 2 (nth d dfns)"
    by (rule conjE1[OF firstTwo])
  have mx: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) rest"
    by (rule conjE2[OF firstTwo])
  show R
    by (rule H[OF di mx my fp])
qed

lemma app_try_argsE:
  assumes J: "J N" and rest: "rest N" and d: "d N" and x: "x N" and y: "y N" and A: "A N"
      and app: "app_try J d x y rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
        sat_hyp_fuel (hyp_of K) A \<Longrightarrow> sat_fuel (conc_of K) A"
      and satG: "sat_hyp_fuel (hyp_of J) A"
      and H: "\<And>vx vy. vx N \<Longrightarrow> vy N \<Longrightarrow>
        dfn_is d 2 (nth d dfns) \<Longrightarrow>
        evals x A vx \<Longrightarrow> evals y A vy \<Longrightarrow>
        find_phi J (subst_body (nth d dfns) x y)
          (pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>) rest \<Longrightarrow> R"
  shows R
proof (rule app_tryE[OF J d x y rest app])
  assume di: "dfn_is d 2 (nth d dfns)"
      and mx: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) rest"
      and my: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) rest"
      and fp: "find_phi J (subst_body (nth d dfns) x y)
        (pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>) rest"
  let ?fx = "pack_F F_EQ \<langle>x, x\<rangle>"
  let ?fy = "pack_F F_EQ \<langle>y, y\<rangle>"
  let ?Kx = "hyp_of J \<tturnstile> ?fx"
  let ?Ky = "hyp_of J \<tturnstile> ?fy"
  have hJN: "hyp_of J N"
    using J by simp
  have xxN: "\<langle>x, x\<rangle> N"
    using x by simp
  have yyN: "\<langle>y, y\<rangle> N"
    using y by simp
  have feqN: "F_EQ N"
    by simp
  have fxN: "?fx N"
    by (rule pack_F_N[OF feqN xxN])
  have fyN: "?fy N"
    by (rule pack_F_N[OF feqN yyN])
  have KxN: "?Kx N"
    using hJN fxN by simp
  have KyN: "?Ky N"
    using hJN fyN by simp
  have hypKx: "hyp_of ?Kx = hyp_of J"
    by (rule cpx_proj[OF hJN fxN])
  have hypKy: "hyp_of ?Ky = hyp_of J"
    by (rule cpx_proj[OF hJN fyN])
  have concKx: "conc_of ?Kx = ?fx"
    by (rule cpy_proj[OF hJN fxN])
  have concKy: "conc_of ?Ky = ?fy"
    by (rule cpy_proj[OF hJN fyN])
  have satHypX: "sat_hyp_fuel (hyp_of ?Kx) A"
    using eqSym[OF hypKx] satG
    by (rule eqSubst[where Q="\<lambda>G. sat_hyp_fuel G A"])
  have satHypY: "sat_hyp_fuel (hyp_of ?Ky) A"
    using eqSym[OF hypKy] satG
    by (rule eqSubst[where Q="\<lambda>G. sat_hyp_fuel G A"])
  have satConcX: "sat_fuel (conc_of ?Kx) A"
    by (rule prev[OF KxN mx satHypX])
  have satConcY: "sat_fuel (conc_of ?Ky) A"
    by (rule prev[OF KyN my satHypY])
  have satX: "sat_fuel ?fx A"
    using concKx satConcX
    by (rule eqSubst[where Q="\<lambda>f. sat_fuel f A"])
  have satY: "sat_fuel ?fy A"
    using concKy satConcY
    by (rule eqSubst[where Q="\<lambda>f. sat_fuel f A"])
  show R
  proof (rule sat_fuel_reflE[OF x satX])
    fix vx
    assume vx: "vx N" and evx: "evals x A vx"
    show R
    proof (rule sat_fuel_reflE[OF y satY])
      fix vy
      assume vy: "vy N" and evy: "evals y A vy"
      show R
        by (rule H[OF vx vy di evx evy fp])
    qed
  qed
qed

lemma template_instance_sound_fuel:
  assumes p: "p N" and i: "i N" and a: "a N" and b: "b N"
      and phi: "phi N" and f: "f N" and A: "A N" and v: "v N"
      and pa: "subst_F p i a = phi"
      and pb: "subst_F p i b = f"
      and sphi: "sat_fuel phi A"
      and eva: "evals a A v"
      and evb: "evals b A v"
  shows "sat_fuel f A"
proof -
  have spa: "sat_fuel (subst_F p i a) A"
    using eqSym[OF pa] sphi
    by (rule eqSubst[where Q="\<lambda>q. sat_fuel q A"])
  have up: "sat_fuel p (asn_put A i v)"
    by (rule sat_fuel_subst_FD[OF p i a A v eva spa])
  have spb: "sat_fuel (subst_F p i b) A"
    by (rule sat_fuel_subst_FI[OF p i b A v evb up])
  show ?thesis
    using pb spb
    by (rule eqSubst[where Q="\<lambda>q. sat_fuel q A"])
qed

lemma check_template_bool [auto]:
  assumes f: "f N" and phi: "phi N" and a: "a N" and b: "b N" and i: "i N" and p: "p N"
  shows "check_template f phi a b p i B"
proof (rule ind[OF p])
  show "check_template f phi a b 0 i B"
    apply (rule defE[OF check_template_def[where p=0]], insert f phi a b i)
    apply simp
    apply (rule condTB[OF _ true_bool false_bool])
    using subst_F_N[OF nat0 i a] subst_F_N[OF nat0 i b] phi f by auto
next
  fix k assume k: "k N" and IH: "check_template f phi a b k i B"
  show "check_template f phi a b (S k) i B"
    apply (rule defE[OF check_template_def[where p="S k"]], insert f phi a b i k IH)
    apply simp
    apply (rule condTB[OF _ true_bool IH])
    using subst_F_N[OF natS[OF k] i a] subst_F_N[OF natS[OF k] i b] phi f by auto
qed

lemma rep_vars_T_N:
  assumes t: "t N" and i: "i N"
  shows "rep_vars_T t i N"
proof (rule strong_induction[where a=t])
  show "t N" by (rule t)
next
  show "rep_vars_T 0 i N"
  proof -
    have pN: "pack_T T_VAR i N"
      apply (rule pack_T_N) 
       apply simp 
      apply (rule i) 
      done
    have g1: "\<not> (tag_T 0 = T_VAR)" 
      by (simp add: tag_T_zero)
    have g2: "tag_T 0 = T_ZERO"    
      by (rule tag_T_zero)
    have red: "rep_vars_T 0 i = pack_T T_VAR i"
      apply (rule defE[OF rep_vars_T_def[where t=0 and i=i]])
      apply (rule condI2Eq[OF g1 pN])
      apply (rule condI1Eq[OF g2 pN])
      using pN apply simp
      done
    show "rep_vars_T 0 i N" 
      using red pN by simp
  qed
next
  fix x assume x: "x N" and IH: "\<And>y. y N \<Longrightarrow> y \<le> x = 1 \<Longrightarrow> rep_vars_T y i N"
  
  have sxN:  "S x N"          
    by (rule natS[OF x])
  have sxnz: "S x \<noteq> 0"        
    by (rule sucNonZero[OF x])
  have L:    "load_T (S x) N" 
    by (rule load_T_N[OF sxN])
  
  have Lx:   "load_T (S x) \<le> x = 1"
    by (rule le_suc_implies_leq[OF decrease_T[OF sxN sxnz] L x])
    
  have cxL:  "cpx (load_T (S x)) N" 
    by (rule cpx_terminates[OF L])
  have cyL:  "cpy (load_T (S x)) N" 
    by (rule cpy_terminates[OF L])
  
  have cxLx: "cpx (load_T (S x)) \<le> x = 1"
    by (rule leq_trans[OF cxL L x cpx_mono[OF L] Lx])
  have cyLx: "cpy (load_T (S x)) \<le> x = 1"
    by (rule leq_trans[OF cyL L x cpy_mono[OF L] Lx])
    
  have cxcyL: "cpx (cpy (load_T (S x))) N" 
    by (rule cpx_terminates[OF cyL])
  have cycyL: "cpy (cpy (load_T (S x))) N" 
    by (rule cpy_terminates[OF cyL])
  
  have cxcyLx: "cpx (cpy (load_T (S x))) \<le> x = 1"
    by (rule leq_trans[OF cxcyL cyL x cpx_mono[OF cyL] cyLx])
  have cycyLx: "cpy (cpy (load_T (S x))) \<le> x = 1"
    by (rule leq_trans[OF cycyL cyL x cpy_mono[OF cyL] cyLx])
    
  have r0: "rep_vars_T (load_T (S x)) i N"             by (rule IH[OF L Lx])
  have r1: "rep_vars_T (cpx (load_T (S x))) i N"       by (rule IH[OF cxL cxLx])
  have r2: "rep_vars_T (cpx (cpy (load_T (S x)))) i N" by (rule IH[OF cxcyL cxcyLx])
  have r3: "rep_vars_T (cpy (cpy (load_T (S x)))) i N" by (rule IH[OF cycyL cycyLx])

  (* Guards *)
  have tgN:   "tag_T (S x) N"             
    by (rule tag_T_N[OF sxN])
  have gVAR:  "(tag_T (S x) = T_VAR) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gZERO: "(tag_T (S x) = T_ZERO) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gSUC:  "(tag_T (S x) = T_SUC) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gPRED: "(tag_T (S x) = T_PRED) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gIFZ:  "(tag_T (S x) = T_IFZ) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done

  (* Branches *)
  have A1N: "pack_T T_VAR i N"
    apply (rule pack_T_N) 
     apply simp
    apply (rule i) 
    done
  have A2N: "pack_T T_VAR i N" 
    by (rule A1N)
    
  have A3N: "pack_T T_SUC (rep_vars_T (load_T (S x)) i) N"
    apply (rule pack_T_N) 
     apply simp 
    apply (rule r0) 
    done
    
  have A4N: "pack_T T_PRED (rep_vars_T (load_T (S x)) i) N"
    apply (rule pack_T_N) 
     apply simp 
    apply (rule r0) 
    done
    
  have A5N: "pack_T T_IFZ \<langle>rep_vars_T (cpx (load_T (S x))) i, \<langle>rep_vars_T (cpx (cpy (load_T (S x)))) i, rep_vars_T (cpy (cpy (load_T (S x)))) i\<rangle>\<rangle> N"
    apply (rule pack_T_N)
    apply simp
    apply (rule r1)
    apply (rule r2)
    apply (rule r3)
    done
    
  have A6N: "pack_T T_APP \<langle>cpx (load_T (S x)), \<langle>rep_vars_T (cpx (cpy (load_T (S x)))) i, rep_vars_T (cpy (cpy (load_T (S x)))) i\<rangle>\<rangle> N"
    apply (rule pack_T_N)
    apply simp
    apply (rule L)
    apply (rule r2)
    apply (rule r3)
    done

  show "rep_vars_T (S x) i N"
    apply (rule defE[OF rep_vars_T_def[where t="S x" and i=i]])
    apply (rule condT[OF gVAR A1N])
    apply (rule condT[OF gZERO A2N])
    apply (rule condT[OF gSUC A3N])
    apply (rule condT[OF gPRED A4N])
    apply (rule condT[OF gIFZ A5N])
    apply (rule A6N)
    done
qed



lemma rep_vars_F_N:
  assumes f: "f N" and i: "i N"
  shows "rep_vars_F f i N"
proof -
  have Lf: "load_F f N" 
    by (rule load_F_N[OF f])
  have cx: "cpx (load_F f) N" 
    by (rule cpx_terminates[OF Lf])
  have cy: "cpy (load_F f) N" 
    by (rule cpy_terminates[OF Lf])
  
  have r_cx: "rep_vars_T (cpx (load_F f)) i N" 
    by (rule rep_vars_T_N[OF cx i])
  have r_cy: "rep_vars_T (cpy (load_F f)) i N" 
    by (rule rep_vars_T_N[OF cy i])
  
  have tgN: "tag_F f N" 
    by (rule tag_F_N[OF f])
  have gEQ: "(tag_F f = F_EQ) B" 
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  
  have A1N: "pack_F F_EQ \<langle>rep_vars_T (cpx (load_F f)) i, rep_vars_T (cpy (load_F f)) i\<rangle> N"
    apply (rule pack_F_N)
    apply simp
    apply (rule r_cx)
    apply (rule r_cy)
    done
    
  have A2N: "pack_F F_NEQ \<langle>rep_vars_T (cpx (load_F f)) i, rep_vars_T (cpy (load_F f)) i\<rangle> N"
    apply (rule pack_F_N)
    apply simp
    apply (rule r_cx)
    apply (rule r_cy)
    done

  show "rep_vars_F f i N"
    apply (rule defE[OF rep_vars_F_def[where f=f and i=i]])
    apply (rule condT[OF gEQ A1N])
    apply (rule A2N)
    done
qed

lemma find_phi_bool [auto]:
  assumes J: "J N" and a: "a N" and b: "b N" and ptr: "ptr N"
  shows "find_phi J a b ptr B"
proof (rule list_induct[OF ptr])
  show "find_phi J a b Nil B"
    apply (rule defE[OF find_phi_def[where J=J and a=a and b=b and ptr=Nil]])
    apply simp
    done
next
  fix h t assume h: "h N" and t: "t N" and IH: "find_phi J a b t B"
  show "find_phi J a b (Cons h t) B"
  proof -
    have htN: "h \<triangleright> t N" 
      using h t by simp
    have g1: "(h \<triangleright> t = \<emptyset>) B" 
      apply (rule eqBool[OF htN]) 
      apply simp 
      done

    have eq1: "(hyp_of h = hyp_of J) B" 
      using h J by simp
    
    have cy_J: "conc_of J N" 
      using J by simp
    have cy_h: "conc_of h N" 
      using h by simp
    have SJ: "S J N" 
      using J by simp
    
    have rep: "rep_vars_F (conc_of J) (S J) N" 
      by (rule rep_vars_F_N[OF cy_J SJ])
    
    have eq2: "check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (S J)) (S J) B"
      apply (rule check_template_bool)
      apply (rule cy_J)
      apply (rule cy_h)
      apply (rule a)
        apply (rule b)
      apply (rule SJ)
      apply (rule rep)
      done
      
    have g2: "(hyp_of h = hyp_of J \<and> check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (S J)) (S J)) B"
      using eq1 eq2 by simp

    show "find_phi J a b (h \<triangleright> t) B"
      apply (rule defE[OF find_phi_def[where J=J and a=a and b=b and ptr="h \<triangleright> t"]])
      apply (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t] one_plus_suc[OF J])
      apply (rule condTB[OF g1 false_bool])
      apply (rule condTB[OF g2 true_bool IH])
      done
  qed
qed

lemma app_try_bool [auto]:
  assumes J: "J N" and d: "d N" and x: "x N" and y: "y N" and r: "rest N"
      and dr: "d < len dfns = 1"
  shows "app_try J d x y rest B"
proof (rule defE[OF app_try_def[where J=J and d=d and x=x and y=y and rest=rest]])
  have hj:  "hyp_of J N"             
    using J by simp
  have xx:  "\<langle>x, x\<rangle> N"              
    using x by simp
  have yy:  "\<langle>y, y\<rangle> N"              
    using y by simp
  have pfx: "pack_F F_EQ \<langle>x, x\<rangle> N"  
    by (rule pack_F_N[OF _ xx], simp)
  have pfy: "pack_F F_EQ \<langle>y, y\<rangle> N"  
    by (rule pack_F_N[OF _ yy], simp)
  have jxx: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) N" 
    using hj pfx by simp
  have jyy: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) N" 
    using hj pfy by simp
  have ndf: "nth d dfns N"
    using dfns_N dr 
    apply (rule nth_in_range_N)
    done
  have di: "dfn_is d 2 (nth d dfns) B"
    by (rule dfn_is_bool[OF d _ ndf], simp)
  have sb:  "subst_body (nth d dfns) x y N" 
    by (rule subst_body_N[OF ndf x y])
  have dxy: "\<langle>d, \<langle>x, y\<rangle>\<rangle> N"                 
    using d x y by simp
  have pT:  "pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle> N"    
    by (rule pack_T_N[OF _ dxy], simp)
  have m1: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) rest B" 
    by (rule mem_bool[OF jxx r])
  have m2: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) rest B" 
    by (rule mem_bool[OF jyy r])
  have fp: "find_phi J (subst_body (nth d dfns) x y) (pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>) rest B"
           by (rule find_phi_bool[OF J sb pT r])
  show "dfn_is d T_SUC (nth d dfns) \<and> (hyp_of J \<tturnstile> pack_F F_EQ (x \<tturnstile> x)) \<in> rest \<and>
    (hyp_of J \<tturnstile> pack_F F_EQ (y \<tturnstile> y)) \<in> rest \<and> find_phi J (subst_body (nth d dfns) x y) (pack_T T_APP (d \<tturnstile> (x \<tturnstile> y))) rest B "
    using di m1 m2 fp by simp
qed

lemma app_y_bool [auto]:
  assumes J: "J N" and d: "d N" and x: "x N" and y: "y N" and r: "rest N"
      and dr: "d < len dfns = 1"
  shows "app_y J d x y rest B"
proof (rule ind[OF y])
  show "app_y J d x 0 rest B"
    apply (rule defE[OF app_y_def[where y=0]], insert J d x r)
    apply simp
    apply (rule condTB[OF _ true_bool false_bool])
    apply (rule app_try_bool[OF J d x nat0 r dr])
    done
next
  fix k assume k: "k N" and IH: "app_y J d x k rest B"
  have skN: "S k N" 
    by (rule natS[OF k])
  have oneN: "(1::num) N" 
    by simp
  have grN: "(S k > 0) N"
    by (unfold greater_def, rule sub_terminates[OF oneN leq_terminates[OF skN nat0]])
  have g2B: "(S k > 0 = 1) B" 
    by (rule eqBool[OF grN oneN])
  have sk1: "S k - 1 = k" 
    using k by simp
  have RECB: "app_y J d x (S k - 1) rest B" 
    using IH sk1 by simp
  have innerB: "(if S k > 0 = 1 then app_y J d x (S k - 1) rest else False) B"
    by (rule condTB[OF g2B RECB false_bool])
  have gB: "app_try J d x (S k) rest B" 
    by (rule app_try_bool[OF J d x skN r dr])
  show "app_y J d x (S k) rest B"
    apply (rule defE[OF app_y_def[where y="S k"]])
    apply (rule condTB[OF gB true_bool innerB])
    done
qed

lemma app_yE:
  assumes J: "J N" and d: "d N" and x: "x N" and y: "y N" and rest: "rest N"
      and dr: "d < len dfns = 1" and ay: "app_y J d x y rest"
      and H: "\<And>z. z N \<Longrightarrow> app_try J d x z rest \<Longrightarrow> R"
  shows R
proof -
  have main: "app_y J d x y rest \<turnstile> R"
  proof (rule ind[OF y])
    show "app_y J d x 0 rest \<turnstile> R"
    proof (rule entailsI)
      assume ay0: "app_y J d x 0 rest"
      have C:
        "if app_try J d x 0 rest then True
         else if 0 > 0 = 1 then app_y J d x (0 - 1) rest
         else False"
        using ay0
        by (rule defI[OF app_y_def[where J=J and d=d and x=x and y=0 and rest=rest]])
      have tryB: "app_try J d x 0 rest B"
        by (rule app_try_bool[OF J d x nat0 rest dr])
      show R
      proof (rule cases_bool[where q="app_try J d x 0 rest"])
        show "app_try J d x 0 rest B"
          by (rule tryB)
      next
        assume app: "app_try J d x 0 rest"
        show R
          by (rule H[OF nat0 app])
      next
        assume napp: "\<not> app_try J d x 0 rest"
        have tail:
          "if 0 > 0 = 1 then app_y J d x (0 - 1) rest
           else False"
          using napp C by (rule notcond_thenE)
        have bot: "False"
          using tail by simp
        show R
          by (rule exF[OF bot not_false])
      qed
    qed
  next
    fix k
    assume k: "k N" and IH: "app_y J d x k rest \<turnstile> R"
    show "app_y J d x (S k) rest \<turnstile> R"
    proof (rule entailsI)
      assume ayS: "app_y J d x (S k) rest"
      have sk: "S k N"
        by (rule natS[OF k])
      have C:
        "if app_try J d x (S k) rest then True
         else if S k > 0 = 1 then app_y J d x (S k - 1) rest
         else False"
        using ayS
        by (rule defI[OF app_y_def[where J=J and d=d and x=x and y="S k" and rest=rest]])
      have tryB: "app_try J d x (S k) rest B"
        by (rule app_try_bool[OF J d x sk rest dr])
      show R
      proof (rule cases_bool[where q="app_try J d x (S k) rest"])
        show "app_try J d x (S k) rest B"
          by (rule tryB)
      next
        assume app: "app_try J d x (S k) rest"
        show R
          by (rule H[OF sk app])
      next
        assume napp: "\<not> app_try J d x (S k) rest"
        have recCond:
          "if S k > 0 = 1 then app_y J d x (S k - 1) rest
           else False"
          using napp C by (rule notcond_thenE)
        have gt: "S k > 0 = 1"
          using k by simp
        have rec: "app_y J d x (S k - 1) rest"
          using gt recCond by (rule cond_thenE)
        have recK: "app_y J d x k rest"
          using k rec by simp
        show R
          using IH recK by (rule entailsE)
      qed
    qed
  qed
  show R
    using main ay by (rule entailsE)
qed

lemma app_xE:
  assumes J: "J N" and d: "d N" and x: "x N" and rest: "rest N"
      and dr: "d < len dfns = 1" and ax: "app_x J d x rest"
      and H: "\<And>u v. u N \<Longrightarrow> v N \<Longrightarrow>
        app_try J d u v rest \<Longrightarrow> R"
  shows R
proof -
  have cJ: "conc_of J N"
    using J by simp
  have main: "app_x J d x rest \<turnstile> R"
  proof (rule ind[OF x])
    show "app_x J d 0 rest \<turnstile> R"
    proof (rule entailsI)
      assume ax0: "app_x J d 0 rest"
      have C:
        "if app_y J d 0 (conc_of J) rest then True
         else if 0 > 0 = 1 then app_x J d (0 - 1) rest
         else False"
        using ax0
        by (rule defI[OF app_x_def[where J=J and d=d and x=0 and rest=rest]])
      have ayB: "app_y J d 0 (conc_of J) rest B"
        by (rule app_y_bool[OF J d nat0 cJ rest dr])
      show R
      proof (rule cases_bool[where q="app_y J d 0 (conc_of J) rest"])
        show "app_y J d 0 (conc_of J) rest B"
          by (rule ayB)
      next
        assume ay: "app_y J d 0 (conc_of J) rest"
        show R
        proof (rule app_yE[OF J d nat0 cJ rest dr ay])
          fix v
          assume v: "v N" and app: "app_try J d 0 v rest"
          show R
            by (rule H[OF nat0 v app])
        qed
      next
        assume nay: "\<not> app_y J d 0 (conc_of J) rest"
        have tail:
          "if 0 > 0 = 1 then app_x J d (0 - 1) rest
           else False"
          using nay C by (rule notcond_thenE)
        have bot: "False"
          using tail by simp
        show R
          by (rule exF[OF bot not_false])
      qed
    qed
  next
    fix k
    assume k: "k N" and IH: "app_x J d k rest \<turnstile> R"
    show "app_x J d (S k) rest \<turnstile> R"
    proof (rule entailsI)
      assume axS: "app_x J d (S k) rest"
      have sk: "S k N"
        by (rule natS[OF k])
      have C:
        "if app_y J d (S k) (conc_of J) rest then True
         else if S k > 0 = 1 then app_x J d (S k - 1) rest
         else False"
        using axS
        by (rule defI[OF app_x_def[where J=J and d=d and x="S k" and rest=rest]])
      have ayB: "app_y J d (S k) (conc_of J) rest B"
        by (rule app_y_bool[OF J d sk cJ rest dr])
      show R
      proof (rule cases_bool[where q="app_y J d (S k) (conc_of J) rest"])
        show "app_y J d (S k) (conc_of J) rest B"
          by (rule ayB)
      next
        assume ay: "app_y J d (S k) (conc_of J) rest"
        show R
        proof (rule app_yE[OF J d sk cJ rest dr ay])
          fix v
          assume v: "v N" and app: "app_try J d (S k) v rest"
          show R
            by (rule H[OF sk v app])
        qed
      next
        assume nay: "\<not> app_y J d (S k) (conc_of J) rest"
        have recCond:
          "if S k > 0 = 1 then app_x J d (S k - 1) rest
           else False"
          using nay C by (rule notcond_thenE)
        have gt: "S k > 0 = 1"
          using k by simp
        have rec: "app_x J d (S k - 1) rest"
          using gt recCond by (rule cond_thenE)
        have recK: "app_x J d k rest"
          using k rec by simp
        show R
          using IH recK by (rule entailsE)
      qed
    qed
  qed
  show R
    using main ax by (rule entailsE)
qed

lemma app_x_bool [auto]:
  assumes J: "J N" and d: "d N" and x: "x N" and r: "rest N"
      and dr: "d < len dfns = 1"
  shows "app_x J d x rest B"
proof -
  have cJ: "conc_of J N" 
    using J by simp
  show ?thesis
  proof (rule ind[OF x])
    show "app_x J d 0 rest B"
      apply (rule defE[OF app_x_def[where x=0]], insert J d r)
      apply simp
      apply (rule condTB[OF _ true_bool false_bool])
      apply (rule app_y_bool[OF J d nat0 cJ r dr])
      done
  next
    fix k assume k: "k N" and IH: "app_x J d k rest B"
    have skN: "S k N" 
      by (rule natS[OF k])
    have oneN: "(1::num) N" 
      by simp
    have grN: "(S k > 0) N"
      by (unfold greater_def, rule sub_terminates[OF oneN leq_terminates[OF skN nat0]])
    have g2B: "(S k > 0 = 1) B" 
      by (rule eqBool[OF grN oneN])
    have sk1: "S k - 1 = k" 
      using k by simp
    have RECB: "app_x J d (S k - 1) rest B" 
      using IH sk1 by simp
    have innerB: "(if S k > 0 = 1 then app_x J d (S k - 1) rest else False) B"
      by (rule condTB[OF g2B RECB false_bool])
    have gB: "app_y J d (S k) (conc_of J) rest B" 
      by (rule app_y_bool[OF J d skN cJ r dr])
    show "app_x J d (S k) rest B"
      apply (rule defE[OF app_x_def[where x="S k"]])
      apply (rule condTB[OF gB true_bool innerB])
      done
  qed
qed

lemma app_d_bool [auto]:
  assumes J: "J N" and d: "d N" and r: "rest N"
  shows "app_d J d rest B"
proof -
  have ldN: "len dfns N" 
    by (rule len_nat[OF dfns_N])
  have oneN: "(1::num) N" 
    by simp
  have cJ: "conc_of J N" 
    using J by simp
  show ?thesis
  proof (rule ind[OF d])
    have g0: "(0 < len dfns = 1) B" 
      by (rule eqBool[OF less_terminates[OF nat0 ldN] oneN])
    have then0: "0 < len dfns = 1 \<Longrightarrow>
                 (if app_x J 0 (conc_of J) rest then True else False) B"
    proof -
      assume hh: "0 < len dfns = 1"
      have ax: "app_x J 0 (conc_of J) rest B" 
        by (rule app_x_bool[OF J nat0 cJ r hh])
      show "(if app_x J 0 (conc_of J) rest then True else False) B"
        by (rule condTB[OF ax true_bool false_bool])
    qed
    show "app_d J 0 rest B"
      apply (rule defE[OF app_d_def[where d=0]])
      apply simp
      apply (rule condTB'[OF g0 then0])
       apply assumption
      apply (rule false_bool)
      done
  next
    fix k assume k: "k N" and IH: "app_d J k rest B"
    have skN: "S k N" 
      by (rule natS[OF k])
    have grN: "(S k > 0) N"
      by (unfold greater_def, rule sub_terminates[OF oneN leq_terminates[OF skN nat0]])
    have g2B: "(S k > 0 = 1) B" 
      by (rule eqBool[OF grN oneN])
    have sk1: "S k - 1 = k" 
      using k by simp
    have RECB: "app_d J (S k - 1) rest B" 
      using IH sk1 by simp
    have innerB: "(if S k > 0 = 1 then app_d J (S k - 1) rest else False) B"
      by (rule condTB[OF g2B RECB false_bool])
    have gS: "(S k < len dfns = 1) B" 
      by (rule eqBool[OF less_terminates[OF skN ldN] oneN])
    have thenS: "S k < len dfns = 1 \<Longrightarrow>
                 (if app_x J (S k) (conc_of J) rest then True
                  else if S k > 0 = 1 then app_d J (S k - 1) rest else False) B"
    proof -
      assume hh: "S k < len dfns = 1"
      have ax: "app_x J (S k) (conc_of J) rest B" 
        by (rule app_x_bool[OF J skN cJ r hh])
      show "(if app_x J (S k) (conc_of J) rest then True
             else if S k > 0 = 1 then app_d J (S k - 1) rest else False) B"
        by (rule condTB[OF ax true_bool innerB])
    qed
    show "app_d J (S k) rest B"
      apply (rule defE[OF app_d_def[where d="S k"]])
      apply (rule condTB'[OF gS thenS])
       apply assumption
      apply (rule innerB)
      done
  qed
qed

lemma app_dE:
  assumes J: "J N" and d: "d N" and rest: "rest N"
      and ad: "app_d J d rest"
      and H: "\<And>e u v. e N \<Longrightarrow> u N \<Longrightarrow> v N \<Longrightarrow>
        app_try J e u v rest \<Longrightarrow> R"
  shows R
proof -
  have cJ: "conc_of J N"
    using J by simp
  have ldN: "len dfns N"
    by (rule len_nat[OF dfns_N])
  have oneN: "(1::num) N"
    by simp
  have main: "app_d J d rest \<turnstile> R"
  proof (rule ind[OF d])
    show "app_d J 0 rest \<turnstile> R"
    proof (rule entailsI)
      assume ad0: "app_d J 0 rest"
      have C:
        "if 0 < len dfns = 1 then
           (if app_x J 0 (conc_of J) rest then True
            else if 0 > 0 = 1 then app_d J (0 - 1) rest else False)
         else
           (if 0 > 0 = 1 then app_d J (0 - 1) rest else False)"
        using ad0
        by (rule defI[OF app_d_def[where J=J and d=0 and rest=rest]])
      have rangeB: "(0 < len dfns = 1) B"
        by (rule eqBool[OF less_terminates[OF nat0 ldN] oneN])
      show R
      proof (rule cases_bool[where q="0 < len dfns = 1"])
        show "(0 < len dfns = 1) B"
          by (rule rangeB)
      next
        assume dr: "0 < len dfns = 1"
        have inner:
          "if app_x J 0 (conc_of J) rest then True
           else if 0 > 0 = 1 then app_d J (0 - 1) rest else False"
          using dr C by (rule cond_thenE)
        have axB: "app_x J 0 (conc_of J) rest B"
          by (rule app_x_bool[OF J nat0 cJ rest dr])
        show R
        proof (rule cases_bool[where q="app_x J 0 (conc_of J) rest"])
          show "app_x J 0 (conc_of J) rest B"
            by (rule axB)
        next
          assume ax: "app_x J 0 (conc_of J) rest"
          show R
          proof (rule app_xE[OF J nat0 cJ rest dr ax])
            fix u v
            assume u: "u N" and v: "v N" and app: "app_try J 0 u v rest"
            show R
              by (rule H[OF nat0 u v app])
          qed
        next
          assume nax: "\<not> app_x J 0 (conc_of J) rest"
          have tail:
            "if 0 > 0 = 1 then app_d J (0 - 1) rest else False"
            using nax inner by (rule notcond_thenE)
          have bot: "False"
            using tail by simp
          show R
            by (rule exF[OF bot not_false])
        qed
      next
        assume ndr: "\<not> 0 < len dfns = 1"
        have tail:
          "if 0 > 0 = 1 then app_d J (0 - 1) rest else False"
          using ndr C by (rule notcond_thenE)
        have bot: "False"
          using tail by simp
        show R
          by (rule exF[OF bot not_false])
      qed
    qed
  next
    fix k
    assume k: "k N" and IH: "app_d J k rest \<turnstile> R"
    show "app_d J (S k) rest \<turnstile> R"
    proof (rule entailsI)
      assume adS: "app_d J (S k) rest"
      have sk: "S k N"
        by (rule natS[OF k])
      have C:
        "if S k < len dfns = 1 then
           (if app_x J (S k) (conc_of J) rest then True
            else if S k > 0 = 1 then app_d J (S k - 1) rest else False)
         else
           (if S k > 0 = 1 then app_d J (S k - 1) rest else False)"
        using adS
        by (rule defI[OF app_d_def[where J=J and d="S k" and rest=rest]])
      have rangeB: "(S k < len dfns = 1) B"
        by (rule eqBool[OF less_terminates[OF sk ldN] oneN])
      have gt: "S k > 0 = 1"
        using k by simp
      show R
      proof (rule cases_bool[where q="S k < len dfns = 1"])
        show "(S k < len dfns = 1) B"
          by (rule rangeB)
      next
        assume dr: "S k < len dfns = 1"
        have inner:
          "if app_x J (S k) (conc_of J) rest then True
           else if S k > 0 = 1 then app_d J (S k - 1) rest else False"
          using dr C by (rule cond_thenE)
        have axB: "app_x J (S k) (conc_of J) rest B"
          by (rule app_x_bool[OF J sk cJ rest dr])
        show R
        proof (rule cases_bool[where q="app_x J (S k) (conc_of J) rest"])
          show "app_x J (S k) (conc_of J) rest B"
            by (rule axB)
        next
          assume ax: "app_x J (S k) (conc_of J) rest"
          show R
          proof (rule app_xE[OF J sk cJ rest dr ax])
            fix u v
            assume u: "u N" and v: "v N"
                and app: "app_try J (S k) u v rest"
            show R
              by (rule H[OF sk u v app])
          qed
        next
          assume nax: "\<not> app_x J (S k) (conc_of J) rest"
          have recCond:
            "if S k > 0 = 1 then app_d J (S k - 1) rest else False"
            using nax inner by (rule notcond_thenE)
          have rec: "app_d J (S k - 1) rest"
            using gt recCond by (rule cond_thenE)
          have recK: "app_d J k rest"
            using k rec by simp
          show R
            using IH recK by (rule entailsE)
        qed
      next
        assume ndr: "\<not> S k < len dfns = 1"
        have recCond:
          "if S k > 0 = 1 then app_d J (S k - 1) rest else False"
          using ndr C by (rule notcond_thenE)
        have rec: "app_d J (S k - 1) rest"
          using gt recCond by (rule cond_thenE)
        have recK: "app_d J k rest"
          using k rec by simp
        show R
          using IH recK by (rule entailsE)
      qed
    qed
  qed
  show R
    using main ad by (rule entailsE)
qed

lemma check_appE:
  assumes J: "J N" and rest: "rest N" and chk: "check_app J rest"
      and H: "\<And>d x y. d N \<Longrightarrow> x N \<Longrightarrow> y N \<Longrightarrow>
        app_try J d x y rest \<Longrightarrow> R"
  shows R
proof -
  have oneN: "(1::num) N"
    by simp
  have boundN: "len dfns - 1 N"
    by (rule sub_terminates[OF len_nat[OF dfns_N] oneN])
  have ad: "app_d J (len dfns - 1) rest"
    using chk
    by (rule defI[OF check_app_def[where J=J and rest=rest]])
  show R
    by (rule app_dE[OF J boundN rest ad H])
qed

lemma evals_sucI:
  assumes t: "t N" and A: "A N" and r: "r N"
      and ev: "evals t A r"
  shows "evals (pack_T T_SUC t) A (S r)"
proof -
  let ?u = "pack_T T_SUC t"
  have sucN: "T_SUC N"
    by simp
  have uN: "?u N"
    by (rule pack_T_N[OF sucN t])
  have tg: "tag_T ?u = T_SUC"
    by (rule tag_pack_T[OF sucN t])
  have ld: "load_T ?u = t"
    by (rule load_pack_T[OF sucN t])
  show ?thesis
    using ev
  proof (rule evalsE)
    fix k
    assume k: "k N" and run: "eval_fuel k t A = S r"
    have childRun: "eval_fuel k (load_T ?u) A = S r"
      by (rule eqSubst[
            where a=t and b="load_T ?u"
              and Q="\<lambda>z. eval_fuel k z A = S r",
            OF eqSym[OF ld] run])
    have value: "eval_fuel (S k) ?u A = S (S r)"
      by (rule eval_fuel_suc_value[OF k tg childRun])
    show "evals ?u A (S r)"
      by (rule evalsI[OF natS[OF k] value])
  qed
qed

lemma evals_predI:
  assumes t: "t N" and A: "A N" and r: "r N"
      and ev: "evals t A r"
  shows "evals (pack_T T_PRED t) A (P r)"
proof -
  let ?u = "pack_T T_PRED t"
  have predN: "T_PRED N"
    by simp
  have uN: "?u N"
    by (rule pack_T_N[OF predN t])
  have tg: "tag_T ?u = T_PRED"
    by (rule tag_pack_T[OF predN t])
  have ld: "load_T ?u = t"
    by (rule load_pack_T[OF predN t])
  show ?thesis
    using ev
  proof (rule evalsE)
    fix k
    assume k: "k N" and run: "eval_fuel k t A = S r"
    have childRun: "eval_fuel k (load_T ?u) A = S r"
      by (rule eqSubst[
            where a=t and b="load_T ?u"
              and Q="\<lambda>z. eval_fuel k z A = S r",
            OF eqSym[OF ld] run])
    have value: "eval_fuel (S k) ?u A = S (P r)"
      by (rule eval_fuel_pred_value[OF k tg childRun])
    show "evals ?u A (P r)"
      by (rule evalsI[OF natS[OF k] value])
  qed
qed

lemma evals_common_fuel2E:
  assumes a: "a N" and b: "b N" and A: "A N"
      and x: "x N" and y: "y N"
      and eva: "evals a A x" and evb: "evals b A y"
      and H: "\<And>k. k N \<Longrightarrow>
        eval_fuel k a A = S x \<Longrightarrow>
        eval_fuel k b A = S y \<Longrightarrow> R"
  shows R
proof -
  show R
    using eva
  proof (rule evalsE)
    fix ka
    assume ka: "ka N" and runa: "eval_fuel ka a A = S x"
    show R
      using evb
    proof (rule evalsE)
      fix kb
      assume kb: "kb N" and runb: "eval_fuel kb b A = S y"
      let ?k = "ka + kb"
      have k: "?k N"
        using ka kb by simp
      have runaK: "eval_fuel ?k a A = S x"
        by (rule eval_fuel_success_add[OF ka kb a A runa])
      have runb0: "eval_fuel (kb + ka) b A = S y"
        by (rule eval_fuel_success_add[OF kb ka b A runb])
      have comm: "kb + ka = ka + kb"
        using ka kb by simp
      have runbK: "eval_fuel ?k b A = S y"
        by (rule eqSubst[
              where a="kb + ka" and b="?k"
                and Q="\<lambda>z. eval_fuel z b A = S y",
              OF comm runb0])
      show R
        by (rule H[OF k runaK runbK])
    qed
  qed
qed

lemma evals_ifz_zeroI:
  assumes c: "c N" and t: "t N" and e: "e N" and A: "A N" and r: "r N"
      and evc: "evals c A 0" and evt: "evals t A r"
  shows "evals (pack_T T_IFZ \<langle>c, \<langle>t, e\<rangle>\<rangle>) A r"
proof -
  let ?args = "\<langle>t, e\<rangle>"
  let ?payload = "\<langle>c, ?args\<rangle>"
  let ?u = "pack_T T_IFZ ?payload"
  have argsN: "?args N"
    using t e by simp
  have payloadN: "?payload N"
    using c argsN by simp
  have ifzN: "T_IFZ N"
    by simp
  have tg: "tag_T ?u = T_IFZ"
    by (rule tag_pack_T[OF ifzN payloadN])
  have ld: "load_T ?u = ?payload"
    by (rule load_pack_T[OF ifzN payloadN])
  have payloadCond: "hyp_of ?payload = c"
    by (rule cpx_proj[OF c argsN])
  have payloadArgs: "conc_of ?payload = ?args"
    by (rule cpy_proj[OF c argsN])
  have argsThen: "hyp_of ?args = t"
    by (rule cpx_proj[OF t e])
  have selectCond: "hyp_of (load_T ?u) = c"
    by (rule eqSubst[
          where a="?payload" and b="load_T ?u"
            and Q="\<lambda>z. hyp_of z = c",
          OF eqSym[OF ld] payloadCond])
  have selectArgs: "conc_of (load_T ?u) = ?args"
    by (rule eqSubst[
          where a="?payload" and b="load_T ?u"
            and Q="\<lambda>z. conc_of z = ?args",
          OF eqSym[OF ld] payloadArgs])
  have selectThen: "hyp_of (conc_of (load_T ?u)) = t"
    by (rule eqSubst[
          where a="?args" and b="conc_of (load_T ?u)"
            and Q="\<lambda>z. hyp_of z = t",
          OF eqSym[OF selectArgs] argsThen])
  show ?thesis
  proof (rule evals_common_fuel2E[OF c t A nat0 r evc evt])
    fix k
    assume k: "k N"
        and condRun: "eval_fuel k c A = S 0"
        and thenRun: "eval_fuel k t A = S r"
    have condRunU:
      "eval_fuel k (hyp_of (load_T ?u)) A = S 0"
      by (rule eqSubst[
            where a=c and b="hyp_of (load_T ?u)"
              and Q="\<lambda>z. eval_fuel k z A = S 0",
            OF eqSym[OF selectCond] condRun])
    have thenRunU:
      "eval_fuel k (hyp_of (conc_of (load_T ?u))) A = S r"
      by (rule eqSubst[
            where a=t and b="hyp_of (conc_of (load_T ?u))"
              and Q="\<lambda>z. eval_fuel k z A = S r",
            OF eqSym[OF selectThen] thenRun])
    have value: "eval_fuel (S k) ?u A = S r"
      by (rule eval_fuel_ifz_zero_value[OF k tg condRunU thenRunU])
    show "evals ?u A r"
      by (rule evalsI[OF natS[OF k] value])
  qed
qed

lemma evals_ifz_nonzeroI:
  assumes c: "c N" and t: "t N" and e: "e N" and A: "A N"
      and z: "z N" and r: "r N"
      and evc: "evals c A (S z)" and eve: "evals e A r"
  shows "evals (pack_T T_IFZ \<langle>c, \<langle>t, e\<rangle>\<rangle>) A r"
proof -
  let ?args = "\<langle>t, e\<rangle>"
  let ?payload = "\<langle>c, ?args\<rangle>"
  let ?u = "pack_T T_IFZ ?payload"
  have argsN: "?args N"
    using t e by simp
  have payloadN: "?payload N"
    using c argsN by simp
  have ifzN: "T_IFZ N"
    by simp
  have sz: "S z N"
    by (rule natS[OF z])
  have tg: "tag_T ?u = T_IFZ"
    by (rule tag_pack_T[OF ifzN payloadN])
  have ld: "load_T ?u = ?payload"
    by (rule load_pack_T[OF ifzN payloadN])
  have payloadCond: "hyp_of ?payload = c"
    by (rule cpx_proj[OF c argsN])
  have payloadArgs: "conc_of ?payload = ?args"
    by (rule cpy_proj[OF c argsN])
  have argsElse: "conc_of ?args = e"
    by (rule cpy_proj[OF t e])
  have selectCond: "hyp_of (load_T ?u) = c"
    by (rule eqSubst[
          where a="?payload" and b="load_T ?u"
            and Q="\<lambda>w. hyp_of w = c",
          OF eqSym[OF ld] payloadCond])
  have selectArgs: "conc_of (load_T ?u) = ?args"
    by (rule eqSubst[
          where a="?payload" and b="load_T ?u"
            and Q="\<lambda>w. conc_of w = ?args",
          OF eqSym[OF ld] payloadArgs])
  have selectElse: "conc_of (conc_of (load_T ?u)) = e"
    by (rule eqSubst[
          where a="?args" and b="conc_of (load_T ?u)"
            and Q="\<lambda>w. conc_of w = e",
          OF eqSym[OF selectArgs] argsElse])
  show ?thesis
  proof (rule evals_common_fuel2E[OF c e A sz r evc eve])
    fix k
    assume k: "k N"
        and condRun: "eval_fuel k c A = S (S z)"
        and elseRun: "eval_fuel k e A = S r"
    have condRunU:
      "eval_fuel k (hyp_of (load_T ?u)) A = S (S z)"
      by (rule eqSubst[
            where a=c and b="hyp_of (load_T ?u)"
              and Q="\<lambda>w. eval_fuel k w A = S (S z)",
            OF eqSym[OF selectCond] condRun])
    have elseRunU:
      "eval_fuel k (conc_of (conc_of (load_T ?u))) A = S r"
      by (rule eqSubst[
            where a=e and b="conc_of (conc_of (load_T ?u))"
              and Q="\<lambda>w. eval_fuel k w A = S r",
            OF eqSym[OF selectElse] elseRun])
    have value: "eval_fuel (S k) ?u A = S r"
      by (rule eval_fuel_ifz_nonzero_value[OF k tg condRunU elseRunU])
    show "evals ?u A r"
      by (rule evalsI[OF natS[OF k] value])
  qed
qed

lemma evals_sucE:
  assumes t: "t N" and A: "A N"
      and ev: "evals (pack_T T_SUC t) A r"
      and H: "\<And>q. q N \<Longrightarrow> evals t A q \<Longrightarrow> r = S q \<Longrightarrow> R"
  shows R
proof -
  let ?u = "pack_T T_SUC t"
  have sucN: "T_SUC N"
    by simp
  have tg: "tag_T ?u = T_SUC"
    by (rule tag_pack_T[OF sucN t])
  have ld: "load_T ?u = t"
    by (rule load_pack_T[OF sucN t])
  show R
    using ev
  proof (rule evalsE)
    fix k
    assume k: "k N" and run: "eval_fuel k ?u A = S r"
    show R
    proof (rule cases_nat_2[where x=k])
      show "k N"
        by (rule k)
    next
      assume kz: "k = 0"
      have run0: "eval_fuel 0 ?u A = S r"
        by (rule eqSubst[
              where a=k and b=0
                and Q="\<lambda>z. eval_fuel z ?u A = S r",
              OF kz run])
      have timeout: "eval_fuel 0 ?u A = 0"
        by (rule eval_fuel_zero)
      show R
        by (rule zero_successE[OF timeout run0])
    next
      fix n
      assume n: "n N" and ks: "k = S n"
      have runS: "eval_fuel (S n) ?u A = S r"
        by (rule eqSubst[
              where a=k and b="S n"
                and Q="\<lambda>z. eval_fuel z ?u A = S r",
              OF ks run])
      have childN: "eval_fuel n t A N"
        by (rule eval_fuel_N[OF n t A])
      show R
      proof (rule cases_nat_2[where x="eval_fuel n t A"])
        show "eval_fuel n t A N"
          by (rule childN)
      next
        assume childTimeout: "eval_fuel n t A = 0"
        have childTimeoutU: "eval_fuel n (load_T ?u) A = 0"
          by (rule eqSubst[
                where a=t and b="load_T ?u"
                  and Q="\<lambda>z. eval_fuel n z A = 0",
                OF eqSym[OF ld] childTimeout])
        have timeout: "eval_fuel (S n) ?u A = 0"
          by (rule eval_fuel_suc_timeout[OF n tg childTimeoutU])
        show R
          by (rule zero_successE[OF timeout runS])
      next
        fix q
        assume q: "q N" and childSuccess: "eval_fuel n t A = S q"
        have childSuccessU: "eval_fuel n (load_T ?u) A = S q"
          by (rule eqSubst[
                where a=t and b="load_T ?u"
                  and Q="\<lambda>z. eval_fuel n z A = S q",
                OF eqSym[OF ld] childSuccess])
        have value: "eval_fuel (S n) ?u A = S (S q)"
          by (rule eval_fuel_suc_value[OF n tg childSuccessU])
        have resultSuc: "S (S q) = S r"
          by (rule same_success[OF value runS])
        have result: "r = S q"
          by (rule eqSym[OF sucInj[OF resultSuc]])
        have childEval: "evals t A q"
          by (rule evalsI[OF n childSuccess])
        show R
          by (rule H[OF q childEval result])
      qed
    qed
  qed
qed

lemma evals_predE:
  assumes t: "t N" and A: "A N"
      and ev: "evals (pack_T T_PRED t) A r"
      and H: "\<And>q. q N \<Longrightarrow> evals t A q \<Longrightarrow> r = P q \<Longrightarrow> R"
  shows R
proof -
  let ?u = "pack_T T_PRED t"
  have predN: "T_PRED N"
    by simp
  have tg: "tag_T ?u = T_PRED"
    by (rule tag_pack_T[OF predN t])
  have ld: "load_T ?u = t"
    by (rule load_pack_T[OF predN t])
  show R
    using ev
  proof (rule evalsE)
    fix k
    assume k: "k N" and run: "eval_fuel k ?u A = S r"
    show R
    proof (rule cases_nat_2[where x=k])
      show "k N"
        by (rule k)
    next
      assume kz: "k = 0"
      have run0: "eval_fuel 0 ?u A = S r"
        by (rule eqSubst[
              where a=k and b=0
                and Q="\<lambda>z. eval_fuel z ?u A = S r",
              OF kz run])
      have timeout: "eval_fuel 0 ?u A = 0"
        by (rule eval_fuel_zero)
      show R
        by (rule zero_successE[OF timeout run0])
    next
      fix n
      assume n: "n N" and ks: "k = S n"
      have runS: "eval_fuel (S n) ?u A = S r"
        by (rule eqSubst[
              where a=k and b="S n"
                and Q="\<lambda>z. eval_fuel z ?u A = S r",
              OF ks run])
      have childN: "eval_fuel n t A N"
        by (rule eval_fuel_N[OF n t A])
      show R
      proof (rule cases_nat_2[where x="eval_fuel n t A"])
        show "eval_fuel n t A N"
          by (rule childN)
      next
        assume childTimeout: "eval_fuel n t A = 0"
        have childTimeoutU: "eval_fuel n (load_T ?u) A = 0"
          by (rule eqSubst[
                where a=t and b="load_T ?u"
                  and Q="\<lambda>z. eval_fuel n z A = 0",
                OF eqSym[OF ld] childTimeout])
        have timeout: "eval_fuel (S n) ?u A = 0"
          by (rule eval_fuel_pred_timeout[OF n tg childTimeoutU])
        show R
          by (rule zero_successE[OF timeout runS])
      next
        fix q
        assume q: "q N" and childSuccess: "eval_fuel n t A = S q"
        have childSuccessU: "eval_fuel n (load_T ?u) A = S q"
          by (rule eqSubst[
                where a=t and b="load_T ?u"
                  and Q="\<lambda>z. eval_fuel n z A = S q",
                OF eqSym[OF ld] childSuccess])
        have value: "eval_fuel (S n) ?u A = S (P q)"
          by (rule eval_fuel_pred_value[OF n tg childSuccessU])
        have resultSuc: "S (P q) = S r"
          by (rule same_success[OF value runS])
        have result: "r = P q"
          by (rule eqSym[OF sucInj[OF resultSuc]])
        have childEval: "evals t A q"
          by (rule evalsI[OF n childSuccess])
        show R
          by (rule H[OF q childEval result])
      qed
    qed
  qed
qed

lemma evals_ifzE:
  assumes c: "c N" and t: "t N" and e: "e N" and A: "A N"
      and ev: "evals (pack_T T_IFZ \<langle>c, \<langle>t, e\<rangle>\<rangle>) A r"
      and H0: "evals c A 0 \<Longrightarrow> evals t A r \<Longrightarrow> R"
      and HS: "\<And>z. z N \<Longrightarrow> evals c A (S z) \<Longrightarrow>
        evals e A r \<Longrightarrow> R"
  shows R
proof -
  let ?args = "\<langle>t, e\<rangle>"
  let ?payload = "\<langle>c, ?args\<rangle>"
  let ?u = "pack_T T_IFZ ?payload"
  have argsN: "?args N"
    using t e by simp
  have payloadN: "?payload N"
    using c argsN by simp
  have ifzN: "T_IFZ N"
    by simp
  have tg: "tag_T ?u = T_IFZ"
    by (rule tag_pack_T[OF ifzN payloadN])
  have ld: "load_T ?u = ?payload"
    by (rule load_pack_T[OF ifzN payloadN])
  have payloadCond: "hyp_of ?payload = c"
    by (rule cpx_proj[OF c argsN])
  have payloadArgs: "conc_of ?payload = ?args"
    by (rule cpy_proj[OF c argsN])
  have argsThen: "hyp_of ?args = t"
    by (rule cpx_proj[OF t e])
  have argsElse: "conc_of ?args = e"
    by (rule cpy_proj[OF t e])
  have selectCond: "hyp_of (load_T ?u) = c"
    by (rule eqSubst[
          where a="?payload" and b="load_T ?u"
            and Q="\<lambda>w. hyp_of w = c",
          OF eqSym[OF ld] payloadCond])
  have selectArgs: "conc_of (load_T ?u) = ?args"
  by (rule eqSubst[
        where a="?payload" and b="load_T ?u"
          and Q="\<lambda>w. conc_of w = ?args",
        OF eqSym[OF ld] payloadArgs])
  have selectThen: "hyp_of (conc_of (load_T ?u)) = t"
    by (rule eqSubst[
          where a="?args" and b="conc_of (load_T ?u)"
            and Q="\<lambda>w. hyp_of w = t",
          OF eqSym[OF selectArgs] argsThen])
  have selectElse: "conc_of (conc_of (load_T ?u)) = e"
    by (rule eqSubst[
          where a="?args" and b="conc_of (load_T ?u)"
            and Q="\<lambda>w. conc_of w = e",
          OF eqSym[OF selectArgs] argsElse])
  show R
    using ev
  proof (rule evalsE)
    fix k
    assume k: "k N" and run: "eval_fuel k ?u A = S r"
    show R
    proof (rule cases_nat_2[where x=k])
      show "k N"
        by (rule k)
    next
      assume kz: "k = 0"
      have run0: "eval_fuel 0 ?u A = S r"
        by (rule eqSubst[
              where a=k and b=0
                and Q="\<lambda>m. eval_fuel m ?u A = S r",
              OF kz run])
      have timeout: "eval_fuel 0 ?u A = 0"
        by (rule eval_fuel_zero)
      show R
        by (rule zero_successE[OF timeout run0])
    next
      fix n
      assume n: "n N" and ks: "k = S n"
      have runS: "eval_fuel (S n) ?u A = S r"
        by (rule eqSubst[
              where a=k and b="S n"
                and Q="\<lambda>m. eval_fuel m ?u A = S r",
              OF ks run])
      have condEvalN: "eval_fuel n c A N"
        by (rule eval_fuel_N[OF n c A])
      show R
      proof (rule cases_nat_2[where x="eval_fuel n c A"])
        show "eval_fuel n c A N"
          by (rule condEvalN)
      next
        assume condTimeout: "eval_fuel n c A = 0"
        have condTimeoutU:
          "eval_fuel n (hyp_of (load_T ?u)) A = 0"
          by (rule eqSubst[
                where a=c and b="hyp_of (load_T ?u)"
                  and Q="\<lambda>w. eval_fuel n w A = 0",
                OF eqSym[OF selectCond] condTimeout])
        have timeout: "eval_fuel (S n) ?u A = 0"
          by (rule eval_fuel_ifz_cond_timeout[OF n tg condTimeoutU])
        show R
          by (rule zero_successE[OF timeout runS])
      next
        fix q
        assume q: "q N" and condSuccess: "eval_fuel n c A = S q"
        show R
        proof (rule cases_nat_2[where x=q])
          show "q N"
            by (rule q)
        next
          assume q0: "q = 0"
          have condZero: "eval_fuel n c A = S 0"
            using condSuccess sucCong[OF q0] by (rule eq_trans)
          have condZeroU:
            "eval_fuel n (hyp_of (load_T ?u)) A = S 0"
            by (rule eqSubst[
                  where a=c and b="hyp_of (load_T ?u)"
                    and Q="\<lambda>w. eval_fuel n w A = S 0",
                  OF eqSym[OF selectCond] condZero])
          have thenEvalN: "eval_fuel n t A N"
            by (rule eval_fuel_N[OF n t A])
          show R
          proof (rule cases_nat_2[where x="eval_fuel n t A"])
            show "eval_fuel n t A N"
              by (rule thenEvalN)
          next
            assume thenTimeout: "eval_fuel n t A = 0"
            have thenTimeoutU:
              "eval_fuel n (hyp_of (conc_of (load_T ?u))) A = 0"
              by (rule eqSubst[
                    where a=t and b="hyp_of (conc_of (load_T ?u))"
                      and Q="\<lambda>w. eval_fuel n w A = 0",
                    OF eqSym[OF selectThen] thenTimeout])
            have thenEvalUN:
              "eval_fuel n (hyp_of (conc_of (load_T ?u))) A N"
              by (rule eqSubst[
                    where a=t and b="hyp_of (conc_of (load_T ?u))"
                      and Q="\<lambda>w. eval_fuel n w A N",
                    OF eqSym[OF selectThen] thenEvalN])
            have step:
              "eval_fuel (S n) ?u A =
                eval_fuel n (hyp_of (conc_of (load_T ?u))) A"
              by (rule eval_fuel_ifz_zero[OF n tg condZeroU thenEvalUN])
            have timeout: "eval_fuel (S n) ?u A = 0"
              using step thenTimeoutU by (rule eq_trans)
            show R
              by (rule zero_successE[OF timeout runS])
          next
            fix v
            assume v: "v N" and thenSuccess: "eval_fuel n t A = S v"
            have thenSuccessU:
              "eval_fuel n (hyp_of (conc_of (load_T ?u))) A = S v"
              by (rule eqSubst[
                    where a=t and b="hyp_of (conc_of (load_T ?u))"
                      and Q="\<lambda>w. eval_fuel n w A = S v",
                    OF eqSym[OF selectThen] thenSuccess])
            have value: "eval_fuel (S n) ?u A = S v"
              by (rule eval_fuel_ifz_zero_value[OF n tg condZeroU thenSuccessU])
            have vrS: "S v = S r"
              by (rule same_success[OF value runS])
            have vr: "v = r"
              by (rule sucInj[OF vrS])
            have condEval: "evals c A 0"
              by (rule evalsI[OF n condZero])
            have thenEvalV: "evals t A v"
              by (rule evalsI[OF n thenSuccess])
            have thenEval: "evals t A r"
              by (rule eqSubst[
                    where a=v and b=r
                      and Q="\<lambda>w. evals t A w",
                    OF vr thenEvalV])
            show R
              by (rule H0[OF condEval thenEval])
          qed
        next
          fix z
          assume z: "z N" and qS: "q = S z"
          have condNonzero: "eval_fuel n c A = S (S z)"
            using condSuccess sucCong[OF qS] by (rule eq_trans)
          have condNonzeroU:
            "eval_fuel n (hyp_of (load_T ?u)) A = S (S z)"
            by (rule eqSubst[
                  where a=c and b="hyp_of (load_T ?u)"
                    and Q="\<lambda>w. eval_fuel n w A = S (S z)",
                  OF eqSym[OF selectCond] condNonzero])
          have elseEvalN: "eval_fuel n e A N"
            by (rule eval_fuel_N[OF n e A])
          show R
          proof (rule cases_nat_2[where x="eval_fuel n e A"])
            show "eval_fuel n e A N"
              by (rule elseEvalN)
          next
            assume elseTimeout: "eval_fuel n e A = 0"
            have elseTimeoutU:
              "eval_fuel n (conc_of (conc_of (load_T ?u))) A = 0"
              by (rule eqSubst[
                    where a=e and b="conc_of (conc_of (load_T ?u))"
                      and Q="\<lambda>w. eval_fuel n w A = 0",
                    OF eqSym[OF selectElse] elseTimeout])
            have elseEvalUN:
              "eval_fuel n (conc_of (conc_of (load_T ?u))) A N"
              by (rule eqSubst[
                    where a=e and b="conc_of (conc_of (load_T ?u))"
                      and Q="\<lambda>w. eval_fuel n w A N",
                    OF eqSym[OF selectElse] elseEvalN])
            have step:
              "eval_fuel (S n) ?u A =
                eval_fuel n (conc_of (conc_of (load_T ?u))) A"
              by (rule eval_fuel_ifz_nonzero[
                    OF n tg condNonzeroU elseEvalUN])
            have timeout: "eval_fuel (S n) ?u A = 0"
              using step elseTimeoutU by (rule eq_trans)
            show R
              by (rule zero_successE[OF timeout runS])
          next
            fix v
            assume v: "v N" and elseSuccess: "eval_fuel n e A = S v"
            have elseSuccessU:
              "eval_fuel n (conc_of (conc_of (load_T ?u))) A = S v"
              by (rule eqSubst[
                    where a=e and b="conc_of (conc_of (load_T ?u))"
                      and Q="\<lambda>w. eval_fuel n w A = S v",
                    OF eqSym[OF selectElse] elseSuccess])
            have value: "eval_fuel (S n) ?u A = S v"
              by (rule eval_fuel_ifz_nonzero_value[
                    OF n tg condNonzeroU elseSuccessU])
            have vrS: "S v = S r"
              by (rule same_success[OF value runS])
            have vr: "v = r"
              by (rule sucInj[OF vrS])
            have condEval: "evals c A (S z)"
              by (rule evalsI[OF n condNonzero])
            have elseEvalV: "evals e A v"
              by (rule evalsI[OF n elseSuccess])
            have elseEval: "evals e A r"
              by (rule eqSubst[
                    where a=v and b=r
                      and Q="\<lambda>w. evals e A w",
                    OF vr elseEvalV])
            show R
              by (rule HS[OF z condEval elseEval])
          qed
        qed
      qed
    qed
  qed
qed

lemma evals_appE:
  assumes d: "d N" and a: "a N" and b: "b N" and A: "A N"
      and ev: "evals (pack_T T_APP \<langle>d, \<langle>a, b\<rangle>\<rangle>) A r"
      and H: "\<And>x y. x N \<Longrightarrow> y N \<Longrightarrow>
        evals a A x \<Longrightarrow> evals b A y \<Longrightarrow>
        evals (nth d dfns) (x \<triangleright> y \<triangleright> Nil) r \<Longrightarrow> R"
  shows R
proof -
  let ?args = "\<langle>a, b\<rangle>"
  let ?payload = "\<langle>d, ?args\<rangle>"
  let ?u = "pack_T T_APP ?payload"
  have argsN: "?args N"
    using a b by simp
  have payloadN: "?payload N"
    using d argsN by simp
  have appN: "T_APP N"
    by simp
  have tg: "tag_T ?u = T_APP"
    by (rule tag_pack_T[OF appN payloadN])
  have nvar: "\<not> tag_T ?u = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T ?u = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T ?u = T_SUC"
    using tg by simp
  have npred: "\<not> tag_T ?u = T_PRED"
    using tg by simp
  have nifz: "\<not> tag_T ?u = T_IFZ"
    using tg by simp
  have ld: "load_T ?u = ?payload"
    by (rule load_pack_T[OF appN payloadN])
  have payloadDfn: "hyp_of ?payload = d"
    by (rule cpx_proj[OF d argsN])
  have payloadArgs: "conc_of ?payload = ?args"
    by (rule cpy_proj[OF d argsN])
  have argsLeft: "hyp_of ?args = a"
    by (rule cpx_proj[OF a b])
  have argsRight: "conc_of ?args = b"
    by (rule cpy_proj[OF a b])
  have selectDfn: "hyp_of (load_T ?u) = d"
    by (rule eqSubst[
          where a="?payload" and b="load_T ?u"
            and Q="\<lambda>w. hyp_of w = d",
          OF eqSym[OF ld] payloadDfn])
  have selectArgs: "conc_of (load_T ?u) = ?args"
  by (rule eqSubst[
        where a="?payload" and b="load_T ?u"
          and Q="\<lambda>w. conc_of w = ?args",
        OF eqSym[OF ld] payloadArgs])
  have selectLeft: "hyp_of (conc_of (load_T ?u)) = a"
    by (rule eqSubst[
          where a="?args" and b="conc_of (load_T ?u)"
            and Q="\<lambda>w. hyp_of w = a",
          OF eqSym[OF selectArgs] argsLeft])
  have selectRight: "conc_of (conc_of (load_T ?u)) = b"
    by (rule eqSubst[
          where a="?args" and b="conc_of (load_T ?u)"
            and Q="\<lambda>w. conc_of w = b",
          OF eqSym[OF selectArgs] argsRight])
  show R
    using ev
  proof (rule evalsE)
    fix k
    assume k: "k N" and run: "eval_fuel k ?u A = S r"
    show R
    proof (rule cases_nat_2[where x=k])
      show "k N"
        by (rule k)
    next
      assume kz: "k = 0"
      have run0: "eval_fuel 0 ?u A = S r"
        by (rule eqSubst[
              where a=k and b=0
                and Q="\<lambda>m. eval_fuel m ?u A = S r",
              OF kz run])
      have timeout: "eval_fuel 0 ?u A = 0"
        by (rule eval_fuel_zero)
      show R
        by (rule zero_successE[OF timeout run0])
    next
      fix n
      assume n: "n N" and ks: "k = S n"
      have runS: "eval_fuel (S n) ?u A = S r"
        by (rule eqSubst[
              where a=k and b="S n"
                and Q="\<lambda>m. eval_fuel m ?u A = S r",
              OF ks run])
      have leftEvalN: "eval_fuel n a A N"
        by (rule eval_fuel_N[OF n a A])
      show R
      proof (rule cases_nat_2[where x="eval_fuel n a A"])
        show "eval_fuel n a A N"
          by (rule leftEvalN)
      next
        assume leftTimeout: "eval_fuel n a A = 0"
        have leftTimeoutU:
          "eval_fuel n (hyp_of (conc_of (load_T ?u))) A = 0"
          by (rule eqSubst[
                where a=a and b="hyp_of (conc_of (load_T ?u))"
                  and Q="\<lambda>w. eval_fuel n w A = 0",
                OF eqSym[OF selectLeft] leftTimeout])
        have timeout: "eval_fuel (S n) ?u A = 0"
          by (rule eval_fuel_app_arg1_timeout[
                OF n nvar nzero nsuc npred nifz leftTimeoutU])
        show R
          by (rule zero_successE[OF timeout runS])
      next
        fix x
        assume x: "x N" and leftSuccess: "eval_fuel n a A = S x"
        have leftSuccessU:
          "eval_fuel n (hyp_of (conc_of (load_T ?u))) A = S x"
          by (rule eqSubst[
                where a=a and b="hyp_of (conc_of (load_T ?u))"
                  and Q="\<lambda>w. eval_fuel n w A = S x",
                OF eqSym[OF selectLeft] leftSuccess])
        have rightEvalN: "eval_fuel n b A N"
          by (rule eval_fuel_N[OF n b A])
        show R
        proof (rule cases_nat_2[where x="eval_fuel n b A"])
          show "eval_fuel n b A N"
            by (rule rightEvalN)
        next
          assume rightTimeout: "eval_fuel n b A = 0"
          have rightTimeoutU:
            "eval_fuel n (conc_of (conc_of (load_T ?u))) A = 0"
            by (rule eqSubst[
                  where a=b and b="conc_of (conc_of (load_T ?u))"
                    and Q="\<lambda>w. eval_fuel n w A = 0",
                  OF eqSym[OF selectRight] rightTimeout])
          have timeout: "eval_fuel (S n) ?u A = 0"
            by (rule eval_fuel_app_arg2_timeout[
                  OF n nvar nzero nsuc npred nifz
                    leftSuccessU rightTimeoutU])
          show R
            by (rule zero_successE[OF timeout runS])
        next
          fix y
          assume y: "y N" and rightSuccess: "eval_fuel n b A = S y"
          have rightSuccessU:
            "eval_fuel n (conc_of (conc_of (load_T ?u))) A = S y"
            by (rule eqSubst[
                  where a=b and b="conc_of (conc_of (load_T ?u))"
                    and Q="\<lambda>w. eval_fuel n w A = S y",
                  OF eqSym[OF selectRight] rightSuccess])
          have pairN: "x \<triangleright> y \<triangleright> Nil N"
            using x y by simp
          have bodyN: "nth d dfns N"
            by (rule nth_N'[OF dfns_N d])
          have bodyEvalN:
            "eval_fuel n (nth d dfns) (x \<triangleright> y \<triangleright> Nil) N"
            by (rule eval_fuel_N[OF n bodyN pairN])
          show R
          proof (rule cases_nat_2[
              where x="eval_fuel n (nth d dfns)
                (x \<triangleright> y \<triangleright> Nil)"])
            show
              "eval_fuel n (nth d dfns)
                (x \<triangleright> y \<triangleright> Nil) N"
              by (rule bodyEvalN)
          next
            assume bodyTimeout:
              "eval_fuel n (nth d dfns)
                (x \<triangleright> y \<triangleright> Nil) = 0"
            have bodyTimeoutU:
              "eval_fuel n (nth (hyp_of (load_T ?u)) dfns)
                (x \<triangleright> y \<triangleright> Nil) = 0"
              by (rule eqSubst[
                    where a=d and b="hyp_of (load_T ?u)"
                      and Q="\<lambda>w. eval_fuel n (nth w dfns)
                        (x \<triangleright> y \<triangleright> Nil) = 0",
                    OF eqSym[OF selectDfn] bodyTimeout])
            have timeout: "eval_fuel (S n) ?u A = 0"
              by (rule eval_fuel_app_body_timeout[
                    OF n nvar nzero nsuc npred nifz
                      leftSuccessU rightSuccessU bodyTimeoutU])
            show R
              by (rule zero_successE[OF timeout runS])
          next
            fix z
            assume z: "z N" and bodySuccess:
              "eval_fuel n (nth d dfns)
                (x \<triangleright> y \<triangleright> Nil) = S z"
            have bodySuccessU:
              "eval_fuel n (nth (hyp_of (load_T ?u)) dfns)
                (x \<triangleright> y \<triangleright> Nil) = S z"
              by (rule eqSubst[
                    where a=d and b="hyp_of (load_T ?u)"
                      and Q="\<lambda>w. eval_fuel n (nth w dfns)
                        (x \<triangleright> y \<triangleright> Nil) = S z",
                    OF eqSym[OF selectDfn] bodySuccess])
            have value: "eval_fuel (S n) ?u A = S z"
              by (rule eval_fuel_app_value[
                    OF n nvar nzero nsuc npred nifz
                      leftSuccessU rightSuccessU bodySuccessU])
            have zrS: "S z = S r"
              by (rule same_success[OF value runS])
            have zr: "z = r"
              by (rule sucInj[OF zrS])
            have leftEval: "evals a A x"
              by (rule evalsI[OF n leftSuccess])
            have rightEval: "evals b A y"
              by (rule evalsI[OF n rightSuccess])
            have bodyEvalZ:
              "evals (nth d dfns) (x \<triangleright> y \<triangleright> Nil) z"
              by (rule evalsI[OF n bodySuccess])
            have bodyEval:
              "evals (nth d dfns) (x \<triangleright> y \<triangleright> Nil) r"
              by (rule eqSubst[
                    where a=z and b=r
                      and Q="\<lambda>w. evals (nth d dfns)
                        (x \<triangleright> y \<triangleright> Nil) w",
                    OF zr bodyEvalZ])
            show R
              by (rule H[OF x y leftEval rightEval bodyEval])
          qed
        qed
      qed
    qed
  qed
qed

lemma subst_T_var_eq:
  assumes t: "t N" and i: "i N" and v: "v N"
      and tg: "tag_T t = T_VAR" and ld: "load_T t = i"
  shows "subst_T t i v = v"
proof -
  show ?thesis
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=v]])
    apply (rule condI1Eq[OF tg v])
    apply (rule condI1Eq[OF ld v])
    using v by simp
qed

lemma subst_T_var_ne:
  assumes t: "t N" and i: "i N" and v: "v N"
      and tg: "tag_T t = T_VAR" and ld: "\<not> load_T t = i"
  shows "subst_T t i v = t"
proof -
  show ?thesis
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=v]])
    apply (rule condI1Eq[OF tg t])
    apply (rule condI2Eq[OF ld t])
    using t by simp
qed

lemma subst_T_zero:
  assumes t: "t N" and i: "i N" and v: "v N"
      and tg: "tag_T t = T_ZERO"
  shows "subst_T t i v = pack_T T_ZERO 0"
proof -
  let ?z = "pack_T T_ZERO 0"
  have zN: "?z N"
    by (rule pack_T_N[OF _ nat0], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  show ?thesis
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=v]])
    apply (rule condI2Eq[OF nvar zN])
    apply (rule condI1Eq[OF tg zN])
    using zN by simp
qed

lemma subst_T_suc:
  assumes t: "t N" and i: "i N" and v: "v N"
      and tg: "tag_T t = T_SUC"
  shows "subst_T t i v = pack_T T_SUC (subst_T (load_T t) i v)"
proof -
  let ?u = "pack_T T_SUC (subst_T (load_T t) i v)"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have subN: "subst_T (load_T t) i v N"
    by (rule subst_T_N[OF loadN i v])
  have uN: "?u N"
    by (rule pack_T_N[OF _ subN], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  show ?thesis
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=v]])
    apply (rule condI2Eq[OF nvar uN])
    apply (rule condI2Eq[OF nzero uN])
    apply (rule condI1Eq[OF tg uN])
    using uN by simp
qed

lemma subst_T_pred:
  assumes t: "t N" and i: "i N" and v: "v N"
      and tg: "tag_T t = T_PRED"
  shows "subst_T t i v = pack_T T_PRED (subst_T (load_T t) i v)"
proof -
  let ?u = "pack_T T_PRED (subst_T (load_T t) i v)"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have subN: "subst_T (load_T t) i v N"
    by (rule subst_T_N[OF loadN i v])
  have uN: "?u N"
    by (rule pack_T_N[OF _ subN], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  show ?thesis
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=v]])
    apply (rule condI2Eq[OF nvar uN])
    apply (rule condI2Eq[OF nzero uN])
    apply (rule condI2Eq[OF nsuc uN])
    apply (rule condI1Eq[OF tg uN])
    using uN by simp
qed

lemma subst_T_ifz:
  assumes t: "t N" and i: "i N" and v: "v N"
      and tg: "tag_T t = T_IFZ"
  shows
    "subst_T t i v =
      pack_T T_IFZ
        \<langle>subst_T (hyp_of (load_T t)) i v,
         \<langle>subst_T (hyp_of (conc_of (load_T t))) i v,
          subst_T (conc_of (conc_of (load_T t))) i v\<rangle>\<rangle>"
proof -
  let ?c = "subst_T (hyp_of (load_T t)) i v"
  let ?l = "subst_T (hyp_of (conc_of (load_T t))) i v"
  let ?r = "subst_T (conc_of (conc_of (load_T t))) i v"
  let ?u = "pack_T T_IFZ \<langle>?c, \<langle>?l, ?r\<rangle>\<rangle>"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have condN: "hyp_of (load_T t) N"
    by (rule cpx_terminates[OF loadN])
  have tailN: "conc_of (load_T t) N"
    by (rule cpy_terminates[OF loadN])
  have leftN: "hyp_of (conc_of (load_T t)) N"
    by (rule cpx_terminates[OF tailN])
  have rightN: "conc_of (conc_of (load_T t)) N"
    by (rule cpy_terminates[OF tailN])
  have cN: "?c N"
    by (rule subst_T_N[OF condN i v])
  have lN: "?l N"
    by (rule subst_T_N[OF leftN i v])
  have rN: "?r N"
    by (rule subst_T_N[OF rightN i v])
  have payloadN: "\<langle>?c, \<langle>?l, ?r\<rangle>\<rangle> N"
    using cN lN rN by simp
  have uN: "?u N"
    by (rule pack_T_N[OF _ payloadN], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have npred: "\<not> tag_T t = T_PRED"
    using tg by simp
  show ?thesis
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=v]])
    apply (rule condI2Eq[OF nvar uN])
    apply (rule condI2Eq[OF nzero uN])
    apply (rule condI2Eq[OF nsuc uN])
    apply (rule condI2Eq[OF npred uN])
    apply (rule condI1Eq[OF tg uN])
    using uN by simp
qed

lemma subst_T_app:
  assumes t: "t N" and i: "i N" and v: "v N"
      and tg: "tag_T t = T_APP"
  shows
    "subst_T t i v =
      pack_T T_APP
        \<langle>hyp_of (load_T t),
         \<langle>subst_T (hyp_of (conc_of (load_T t))) i v,
          subst_T (conc_of (conc_of (load_T t))) i v\<rangle>\<rangle>"
proof -
  let ?d = "hyp_of (load_T t)"
  let ?l = "subst_T (hyp_of (conc_of (load_T t))) i v"
  let ?r = "subst_T (conc_of (conc_of (load_T t))) i v"
  let ?u = "pack_T T_APP \<langle>?d, \<langle>?l, ?r\<rangle>\<rangle>"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have dN: "?d N"
    by (rule cpx_terminates[OF loadN])
  have tailN: "conc_of (load_T t) N"
    by (rule cpy_terminates[OF loadN])
  have leftN: "hyp_of (conc_of (load_T t)) N"
    by (rule cpx_terminates[OF tailN])
  have rightN: "conc_of (conc_of (load_T t)) N"
    by (rule cpy_terminates[OF tailN])
  have lN: "?l N"
    by (rule subst_T_N[OF leftN i v])
  have rN: "?r N"
    by (rule subst_T_N[OF rightN i v])
  have payloadN: "\<langle>?d, \<langle>?l, ?r\<rangle>\<rangle> N"
    using dN lN rN by simp
  have uN: "?u N"
    by (rule pack_T_N[OF _ payloadN], simp)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have npred: "\<not> tag_T t = T_PRED"
    using tg by simp
  have nifz: "\<not> tag_T t = T_IFZ"
    using tg by simp
  show ?thesis
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=v]])
    apply (rule condI2Eq[OF nvar uN])
    apply (rule condI2Eq[OF nzero uN])
    apply (rule condI2Eq[OF nsuc uN])
    apply (rule condI2Eq[OF npred uN])
    apply (rule condI2Eq[OF nifz uN])
    using uN by simp
qed

lemma evals_subst_T_var_transport:
  assumes t: "t N" and i: "i N" and a: "a N" and b: "b N"
      and A: "A N" and r: "r N" and tg: "tag_T t = T_VAR"
      and tr: "\<And>q. q N \<Longrightarrow> evals a A q \<Longrightarrow> evals b A q"
      and ev: "evals (subst_T t i a) A r"
  shows "evals (subst_T t i b) A r"
proof -
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have eqB: "(load_T t = i) B"
    by (rule eqBool[OF loadN i])
  show ?thesis
  proof (rule cases_bool[where q="load_T t = i"])
    show "(load_T t = i) B"
      by (rule eqB)
  next
    assume ld: "load_T t = i"
    have sa: "subst_T t i a = a"
      by (rule subst_T_var_eq[OF t i a tg ld])
    have sb: "subst_T t i b = b"
      by (rule subst_T_var_eq[OF t i b tg ld])
    have eva: "evals a A r"
      by (rule eqSubst[
            where a="subst_T t i a" and b=a
              and Q="\<lambda>u. evals u A r",
            OF sa ev])
    have evb: "evals b A r"
      by (rule tr[OF r eva])
    show "evals (subst_T t i b) A r"
      by (rule eqSubst[
            where a=b and b="subst_T t i b"
              and Q="\<lambda>u. evals u A r",
            OF eqSym[OF sb] evb])
  next
    assume ld: "\<not> load_T t = i"
    have sa: "subst_T t i a = t"
      by (rule subst_T_var_ne[OF t i a tg ld])
    have sb: "subst_T t i b = t"
      by (rule subst_T_var_ne[OF t i b tg ld])
    have evt: "evals t A r"
      by (rule eqSubst[
            where a="subst_T t i a" and b=t
              and Q="\<lambda>u. evals u A r",
            OF sa ev])
    show "evals (subst_T t i b) A r"
      by (rule eqSubst[
            where a=t and b="subst_T t i b"
              and Q="\<lambda>u. evals u A r",
            OF eqSym[OF sb] evt])
  qed
qed

lemma evals_subst_T_zero_transport:
  assumes t: "t N" and i: "i N" and a: "a N" and b: "b N"
      and A: "A N" and r: "r N" and tg: "tag_T t = T_ZERO"
      and ev: "evals (subst_T t i a) A r"
  shows "evals (subst_T t i b) A r"
proof -
  let ?z = "pack_T T_ZERO 0"
  have sa: "subst_T t i a = ?z"
    by (rule subst_T_zero[OF t i a tg])
  have sb: "subst_T t i b = ?z"
    by (rule subst_T_zero[OF t i b tg])
  have evz: "evals ?z A r"
    by (rule eqSubst[
          where a="subst_T t i a" and b="?z"
            and Q="\<lambda>u. evals u A r",
          OF sa ev])
  show ?thesis
    by (rule eqSubst[
          where a="?z" and b="subst_T t i b"
            and Q="\<lambda>u. evals u A r",
          OF eqSym[OF sb] evz])
qed

lemma evals_subst_T_suc_transport:
  assumes t: "t N" and i: "i N" and a: "a N" and b: "b N"
      and A: "A N" and r: "r N" and tg: "tag_T t = T_SUC"
      and IH: "\<And>q. q N \<Longrightarrow>
        evals (subst_T (load_T t) i a) A q \<Longrightarrow>
        evals (subst_T (load_T t) i b) A q"
      and ev: "evals (subst_T t i a) A r"
  shows "evals (subst_T t i b) A r"
proof -
  let ?ca = "subst_T (load_T t) i a"
  let ?cb = "subst_T (load_T t) i b"
  let ?sa = "pack_T T_SUC ?ca"
  let ?sb = "pack_T T_SUC ?cb"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have caN: "?ca N"
    by (rule subst_T_N[OF loadN i a])
  have cbN: "?cb N"
    by (rule subst_T_N[OF loadN i b])
  have substA: "subst_T t i a = ?sa"
    by (rule subst_T_suc[OF t i a tg])
  have substB: "subst_T t i b = ?sb"
    by (rule subst_T_suc[OF t i b tg])
  have source: "evals ?sa A r"
    by (rule eqSubst[
          where a="subst_T t i a" and b="?sa"
            and Q="\<lambda>u. evals u A r",
          OF substA ev])
  show ?thesis
  proof (rule evals_sucE[OF caN A source])
    fix q
    assume q: "q N" and eva: "evals ?ca A q" and rq: "r = S q"
    have evb: "evals ?cb A q"
      by (rule IH[OF q eva])
    have packed: "evals ?sb A (S q)"
      by (rule evals_sucI[OF cbN A q evb])
    have packedR: "evals ?sb A r"
      by (rule eqSubst[
            where a="S q" and b=r
              and Q="\<lambda>z. evals ?sb A z",
            OF eqSym[OF rq] packed])
    show "evals (subst_T t i b) A r"
      by (rule eqSubst[
            where a="?sb" and b="subst_T t i b"
              and Q="\<lambda>u. evals u A r",
            OF eqSym[OF substB] packedR])
  qed
qed

lemma evals_subst_T_pred_transport:
  assumes t: "t N" and i: "i N" and a: "a N" and b: "b N"
      and A: "A N" and r: "r N" and tg: "tag_T t = T_PRED"
      and IH: "\<And>q. q N \<Longrightarrow>
        evals (subst_T (load_T t) i a) A q \<Longrightarrow>
        evals (subst_T (load_T t) i b) A q"
      and ev: "evals (subst_T t i a) A r"
  shows "evals (subst_T t i b) A r"
proof -
  let ?ca = "subst_T (load_T t) i a"
  let ?cb = "subst_T (load_T t) i b"
  let ?pa = "pack_T T_PRED ?ca"
  let ?pb = "pack_T T_PRED ?cb"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have caN: "?ca N"
    by (rule subst_T_N[OF loadN i a])
  have cbN: "?cb N"
    by (rule subst_T_N[OF loadN i b])
  have substA: "subst_T t i a = ?pa"
    by (rule subst_T_pred[OF t i a tg])
  have substB: "subst_T t i b = ?pb"
    by (rule subst_T_pred[OF t i b tg])
  have source: "evals ?pa A r"
    by (rule eqSubst[
          where a="subst_T t i a" and b="?pa"
            and Q="\<lambda>u. evals u A r",
          OF substA ev])
  show ?thesis
  proof (rule evals_predE[OF caN A source])
    fix q
    assume q: "q N" and eva: "evals ?ca A q" and rq: "r = P q"
    have evb: "evals ?cb A q"
      by (rule IH[OF q eva])
    have packed: "evals ?pb A (P q)"
      by (rule evals_predI[OF cbN A q evb])
    have packedR: "evals ?pb A r"
      by (rule eqSubst[
            where a="P q" and b=r
              and Q="\<lambda>z. evals ?pb A z",
            OF eqSym[OF rq] packed])
    show "evals (subst_T t i b) A r"
      by (rule eqSubst[
            where a="?pb" and b="subst_T t i b"
              and Q="\<lambda>u. evals u A r",
            OF eqSym[OF substB] packedR])
  qed
qed

lemma evals_subst_T_ifz_transport:
  assumes t: "t N" and i: "i N" and a: "a N" and b: "b N"
      and A: "A N" and r: "r N" and tg: "tag_T t = T_IFZ"
      and IHcond: "\<And>q. q N \<Longrightarrow>
        evals (subst_T (hyp_of (load_T t)) i a) A q \<Longrightarrow>
        evals (subst_T (hyp_of (load_T t)) i b) A q"
      and IHthen: "\<And>q. q N \<Longrightarrow>
        evals (subst_T (hyp_of (conc_of (load_T t))) i a) A q \<Longrightarrow>
        evals (subst_T (hyp_of (conc_of (load_T t))) i b) A q"
      and IHelse: "\<And>q. q N \<Longrightarrow>
        evals (subst_T (conc_of (conc_of (load_T t))) i a) A q \<Longrightarrow>
        evals (subst_T (conc_of (conc_of (load_T t))) i b) A q"
      and ev: "evals (subst_T t i a) A r"
  shows "evals (subst_T t i b) A r"
proof -
  let ?ca = "subst_T (hyp_of (load_T t)) i a"
  let ?cb = "subst_T (hyp_of (load_T t)) i b"
  let ?ta = "subst_T (hyp_of (conc_of (load_T t))) i a"
  let ?tb = "subst_T (hyp_of (conc_of (load_T t))) i b"
  let ?ea = "subst_T (conc_of (conc_of (load_T t))) i a"
  let ?eb = "subst_T (conc_of (conc_of (load_T t))) i b"
  let ?ua = "pack_T T_IFZ \<langle>?ca, \<langle>?ta, ?ea\<rangle>\<rangle>"
  let ?ub = "pack_T T_IFZ \<langle>?cb, \<langle>?tb, ?eb\<rangle>\<rangle>"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have condN: "hyp_of (load_T t) N"
    by (rule cpx_terminates[OF loadN])
  have tailN: "conc_of (load_T t) N"
    by (rule cpy_terminates[OF loadN])
  have thenN: "hyp_of (conc_of (load_T t)) N"
    by (rule cpx_terminates[OF tailN])
  have elseN: "conc_of (conc_of (load_T t)) N"
    by (rule cpy_terminates[OF tailN])
  have caN: "?ca N"
    by (rule subst_T_N[OF condN i a])
  have cbN: "?cb N"
    by (rule subst_T_N[OF condN i b])
  have taN: "?ta N"
    by (rule subst_T_N[OF thenN i a])
  have tbN: "?tb N"
    by (rule subst_T_N[OF thenN i b])
  have eaN: "?ea N"
    by (rule subst_T_N[OF elseN i a])
  have ebN: "?eb N"
    by (rule subst_T_N[OF elseN i b])
  have substA: "subst_T t i a = ?ua"
    by (rule subst_T_ifz[OF t i a tg])
  have substB: "subst_T t i b = ?ub"
    by (rule subst_T_ifz[OF t i b tg])
  have source: "evals ?ua A r"
    by (rule eqSubst[
          where a="subst_T t i a" and b="?ua"
            and Q="\<lambda>u. evals u A r",
          OF substA ev])
  have target: "evals ?ub A r"
  proof (rule evals_ifzE[OF caN taN eaN A source])
    assume condA: "evals ?ca A 0" and thenA: "evals ?ta A r"
    have condB: "evals ?cb A 0"
      by (rule IHcond[OF nat0 condA])
    have thenB: "evals ?tb A r"
      by (rule IHthen[OF r thenA])
    show "evals ?ub A r"
      by (rule evals_ifz_zeroI[OF cbN tbN ebN A r condB thenB])
  next
    fix z
    assume z: "z N" and condA: "evals ?ca A (S z)"
        and elseA: "evals ?ea A r"
    have sz: "S z N"
      by (rule natS[OF z])
    have condB: "evals ?cb A (S z)"
      by (rule IHcond[OF sz condA])
    have elseB: "evals ?eb A r"
      by (rule IHelse[OF r elseA])
    show "evals ?ub A r"
      by (rule evals_ifz_nonzeroI[OF cbN tbN ebN A z r condB elseB])
  qed
  show ?thesis
    by (rule eqSubst[
          where a="?ub" and b="subst_T t i b"
            and Q="\<lambda>u. evals u A r",
          OF eqSym[OF substB] target])
qed

lemma evals_subst_T_app_transport:
  assumes t: "t N" and i: "i N" and a: "a N" and b: "b N"
      and A: "A N" and r: "r N" and tg: "tag_T t = T_APP"
      and IHleft: "\<And>q. q N \<Longrightarrow>
        evals (subst_T (hyp_of (conc_of (load_T t))) i a) A q \<Longrightarrow>
        evals (subst_T (hyp_of (conc_of (load_T t))) i b) A q"
      and IHright: "\<And>q. q N \<Longrightarrow>
        evals (subst_T (conc_of (conc_of (load_T t))) i a) A q \<Longrightarrow>
        evals (subst_T (conc_of (conc_of (load_T t))) i b) A q"
      and ev: "evals (subst_T t i a) A r"
  shows "evals (subst_T t i b) A r"
proof -
  let ?d = "hyp_of (load_T t)"
  let ?la = "subst_T (hyp_of (conc_of (load_T t))) i a"
  let ?lb = "subst_T (hyp_of (conc_of (load_T t))) i b"
  let ?ra = "subst_T (conc_of (conc_of (load_T t))) i a"
  let ?rb = "subst_T (conc_of (conc_of (load_T t))) i b"
  let ?ua = "pack_T T_APP \<langle>?d, \<langle>?la, ?ra\<rangle>\<rangle>"
  let ?ub = "pack_T T_APP \<langle>?d, \<langle>?lb, ?rb\<rangle>\<rangle>"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have dN: "?d N"
    by (rule cpx_terminates[OF loadN])
  have tailN: "conc_of (load_T t) N"
    by (rule cpy_terminates[OF loadN])
  have leftN: "hyp_of (conc_of (load_T t)) N"
    by (rule cpx_terminates[OF tailN])
  have rightN: "conc_of (conc_of (load_T t)) N"
    by (rule cpy_terminates[OF tailN])
  have laN: "?la N"
    by (rule subst_T_N[OF leftN i a])
  have lbN: "?lb N"
    by (rule subst_T_N[OF leftN i b])
  have raN: "?ra N"
    by (rule subst_T_N[OF rightN i a])
  have rbN: "?rb N"
    by (rule subst_T_N[OF rightN i b])
  have substA: "subst_T t i a = ?ua"
    by (rule subst_T_app[OF t i a tg])
  have substB: "subst_T t i b = ?ub"
    by (rule subst_T_app[OF t i b tg])
  have source: "evals ?ua A r"
    by (rule eqSubst[
          where a="subst_T t i a" and b="?ua"
            and Q="\<lambda>u. evals u A r",
          OF substA ev])
  have target: "evals ?ub A r"
  proof (rule evals_appE[OF dN laN raN A source])
    fix x y
    assume x: "x N" and y: "y N"
        and leftA: "evals ?la A x"
        and rightA: "evals ?ra A y"
        and body: "evals (nth ?d dfns) (x \<triangleright> y \<triangleright> Nil) r"
    have leftB: "evals ?lb A x"
      by (rule IHleft[OF x leftA])
    have rightB: "evals ?rb A y"
      by (rule IHright[OF y rightA])
    show "evals ?ub A r"
      by (rule evals_appI[OF dN lbN rbN A leftB rightB body])
  qed
  show ?thesis
    by (rule eqSubst[
          where a="?ub" and b="subst_T t i b"
            and Q="\<lambda>u. evals u A r",
          OF eqSym[OF substB] target])
qed

lemma subst_T_default:
  assumes t: "t N" and i: "i N" and v: "v N"
      and nvar: "\<not> tag_T t = T_VAR"
      and nzero: "\<not> tag_T t = T_ZERO"
      and nsuc: "\<not> tag_T t = T_SUC"
      and npred: "\<not> tag_T t = T_PRED"
      and nifz: "\<not> tag_T t = T_IFZ"
  shows
    "subst_T t i v =
      pack_T T_APP
        \<langle>hyp_of (load_T t),
         \<langle>subst_T (hyp_of (conc_of (load_T t))) i v,
          subst_T (conc_of (conc_of (load_T t))) i v\<rangle>\<rangle>"
proof -
  let ?d = "hyp_of (load_T t)"
  let ?l = "subst_T (hyp_of (conc_of (load_T t))) i v"
  let ?r = "subst_T (conc_of (conc_of (load_T t))) i v"
  let ?u = "pack_T T_APP \<langle>?d, \<langle>?l, ?r\<rangle>\<rangle>"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have dN: "?d N"
    by (rule cpx_terminates[OF loadN])
  have tailN: "conc_of (load_T t) N"
    by (rule cpy_terminates[OF loadN])
  have leftN: "hyp_of (conc_of (load_T t)) N"
    by (rule cpx_terminates[OF tailN])
  have rightN: "conc_of (conc_of (load_T t)) N"
    by (rule cpy_terminates[OF tailN])
  have lN: "?l N"
    by (rule subst_T_N[OF leftN i v])
  have rN: "?r N"
    by (rule subst_T_N[OF rightN i v])
  have payloadN: "\<langle>?d, \<langle>?l, ?r\<rangle>\<rangle> N"
    using dN lN rN by simp
  have uN: "?u N"
    by (rule pack_T_N[OF _ payloadN], simp)
  show ?thesis
    apply (rule defE[OF subst_T_def[where t=t and j=i and v=v]])
    apply (rule condI2Eq[OF nvar uN])
    apply (rule condI2Eq[OF nzero uN])
    apply (rule condI2Eq[OF nsuc uN])
    apply (rule condI2Eq[OF npred uN])
    apply (rule condI2Eq[OF nifz uN])
    using uN by simp
qed

lemma evals_subst_T_default_transport:
  assumes t: "t N" and i: "i N" and a: "a N" and b: "b N"
      and A: "A N" and r: "r N"
      and nvar: "\<not> tag_T t = T_VAR"
      and nzero: "\<not> tag_T t = T_ZERO"
      and nsuc: "\<not> tag_T t = T_SUC"
      and npred: "\<not> tag_T t = T_PRED"
      and nifz: "\<not> tag_T t = T_IFZ"
      and IHleft: "\<And>q. q N \<Longrightarrow>
        evals (subst_T (hyp_of (conc_of (load_T t))) i a) A q \<Longrightarrow>
        evals (subst_T (hyp_of (conc_of (load_T t))) i b) A q"
      and IHright: "\<And>q. q N \<Longrightarrow>
        evals (subst_T (conc_of (conc_of (load_T t))) i a) A q \<Longrightarrow>
        evals (subst_T (conc_of (conc_of (load_T t))) i b) A q"
      and ev: "evals (subst_T t i a) A r"
  shows "evals (subst_T t i b) A r"
proof -
  let ?d = "hyp_of (load_T t)"
  let ?la = "subst_T (hyp_of (conc_of (load_T t))) i a"
  let ?lb = "subst_T (hyp_of (conc_of (load_T t))) i b"
  let ?ra = "subst_T (conc_of (conc_of (load_T t))) i a"
  let ?rb = "subst_T (conc_of (conc_of (load_T t))) i b"
  let ?ua = "pack_T T_APP \<langle>?d, \<langle>?la, ?ra\<rangle>\<rangle>"
  let ?ub = "pack_T T_APP \<langle>?d, \<langle>?lb, ?rb\<rangle>\<rangle>"
  have loadN: "load_T t N"
    by (rule load_T_N[OF t])
  have dN: "?d N"
    by (rule cpx_terminates[OF loadN])
  have tailN: "conc_of (load_T t) N"
    by (rule cpy_terminates[OF loadN])
  have leftN: "hyp_of (conc_of (load_T t)) N"
    by (rule cpx_terminates[OF tailN])
  have rightN: "conc_of (conc_of (load_T t)) N"
    by (rule cpy_terminates[OF tailN])
  have laN: "?la N"
    by (rule subst_T_N[OF leftN i a])
  have lbN: "?lb N"
    by (rule subst_T_N[OF leftN i b])
  have raN: "?ra N"
    by (rule subst_T_N[OF rightN i a])
  have rbN: "?rb N"
    by (rule subst_T_N[OF rightN i b])
  have substA: "subst_T t i a = ?ua"
    by (rule subst_T_default[
          OF t i a nvar nzero nsuc npred nifz])
  have substB: "subst_T t i b = ?ub"
    by (rule subst_T_default[
          OF t i b nvar nzero nsuc npred nifz])
  have source: "evals ?ua A r"
    by (rule eqSubst[
          where a="subst_T t i a" and b="?ua"
            and Q="\<lambda>u. evals u A r",
          OF substA ev])
  have target: "evals ?ub A r"
  proof (rule evals_appE[OF dN laN raN A source])
    fix x y
    assume x: "x N" and y: "y N"
        and leftA: "evals ?la A x"
        and rightA: "evals ?ra A y"
        and body:
          "evals (nth ?d dfns) (x \<triangleright> y \<triangleright> Nil) r"
    have leftB: "evals ?lb A x"
      by (rule IHleft[OF x leftA])
    have rightB: "evals ?rb A y"
      by (rule IHright[OF y rightA])
    show "evals ?ub A r"
      by (rule evals_appI[OF dN lbN rbN A leftB rightB body])
  qed
  show ?thesis
    by (rule eqSubst[
          where a="?ub" and b="subst_T t i b"
            and Q="\<lambda>u. evals u A r",
          OF eqSym[OF substB] target])
qed

lemma evals_subst_T_transport_aux:
  assumes t: "t N" and i: "i N" and a: "a N" and b: "b N"
      and A: "A N"
      and tr: "\<And>q. q N \<Longrightarrow> evals a A q \<Longrightarrow> evals b A q"
  shows "\<And>r. r N \<Longrightarrow>
    evals (subst_T t i a) A r \<Longrightarrow>
    evals (subst_T t i b) A r"
proof -
  have main:
    "\<forall>k. \<forall>r.
      (eval_fuel k (subst_T t i a) A = S r) \<longrightarrow>
      evals (subst_T t i b) A r"
  proof (rule strong_induction[where a=t])
    show "t N"
      by (rule t)
  next
    show
      "\<forall>k. \<forall>r.
        (eval_fuel k (subst_T 0 i a) A = S r) \<longrightarrow>
        evals (subst_T 0 i b) A r"
    proof (rule forallI)
      fix k
      assume k: "k N"
      show
        "\<forall>r.
          (eval_fuel k (subst_T 0 i a) A = S r) \<longrightarrow>
          evals (subst_T 0 i b) A r"
      proof (rule forallI)
        fix r
        assume r: "r N"
        show
          "(eval_fuel k (subst_T 0 i a) A = S r) \<longrightarrow>
            evals (subst_T 0 i b) A r"
        proof (rule implI)
          have subN: "subst_T 0 i a N"
            by (rule subst_T_N[OF nat0 i a])
          have evalN: "eval_fuel k (subst_T 0 i a) A N"
            by (rule eval_fuel_N[OF k subN A])
          show "(eval_fuel k (subst_T 0 i a) A = S r) B"
            by (rule eqBool[OF evalN natS[OF r]])
        next
          assume run: "eval_fuel k (subst_T 0 i a) A = S r"
          have ev: "evals (subst_T 0 i a) A r"
            by (rule evalsI[OF k run])
          have tg: "tag_T 0 = T_ZERO"
            by (rule tag_T_zero)
          show "evals (subst_T 0 i b) A r"
            by (rule evals_subst_T_zero_transport[
                  OF nat0 i a b A r tg ev])
        qed
      qed
    qed
  next
    fix x
    assume x: "x N"
        and IH: "\<And>u. u N \<Longrightarrow> u \<le> x = 1 \<Longrightarrow>
          \<forall>k. \<forall>r.
            (eval_fuel k (subst_T u i a) A = S r) \<longrightarrow>
            evals (subst_T u i b) A r"
    show
      "\<forall>k. \<forall>r.
        (eval_fuel k (subst_T (S x) i a) A = S r) \<longrightarrow>
        evals (subst_T (S x) i b) A r"
    proof (rule forallI)
      fix k
      assume k: "k N"
      show
        "\<forall>r.
          (eval_fuel k (subst_T (S x) i a) A = S r) \<longrightarrow>
          evals (subst_T (S x) i b) A r"
      proof (rule forallI)
        fix r
        assume r: "r N"
        show
          "(eval_fuel k (subst_T (S x) i a) A = S r) \<longrightarrow>
            evals (subst_T (S x) i b) A r"
        proof (rule implI)
          have sx: "S x N"
            by (rule natS[OF x])
          have subN: "subst_T (S x) i a N"
            by (rule subst_T_N[OF sx i a])
          have evalN: "eval_fuel k (subst_T (S x) i a) A N"
            by (rule eval_fuel_N[OF k subN A])
          show "(eval_fuel k (subst_T (S x) i a) A = S r) B"
            by (rule eqBool[OF evalN natS[OF r]])
        next
          assume run: "eval_fuel k (subst_T (S x) i a) A = S r"
          have sx: "S x N"
            by (rule natS[OF x])
          have ev: "evals (subst_T (S x) i a) A r"
            by (rule evalsI[OF k run])
          have IHmeta:
            "\<And>u q. u N \<Longrightarrow> u \<le> x = 1 \<Longrightarrow> q N \<Longrightarrow>
              evals (subst_T u i a) A q \<Longrightarrow>
              evals (subst_T u i b) A q"
          proof -
            fix u q
            assume u: "u N" and ux: "u \<le> x = 1" and q: "q N"
                and source: "evals (subst_T u i a) A q"
            show "evals (subst_T u i b) A q"
              using source
            proof (rule evalsE)
              fix m
              assume m: "m N"
                  and sourceRun:
                    "eval_fuel m (subst_T u i a) A = S q"
              have IHu:
                "\<forall>m. \<forall>q.
                  (eval_fuel m (subst_T u i a) A = S q) \<longrightarrow>
                  evals (subst_T u i b) A q"
                by (rule IH[OF u ux])
              have IHm:
                "\<forall>q.
                  (eval_fuel m (subst_T u i a) A = S q) \<longrightarrow>
                  evals (subst_T u i b) A q"
                by (rule forallE[where a=m, OF IHu m])
              have IHq:
                "(eval_fuel m (subst_T u i a) A = S q) \<longrightarrow>
                  evals (subst_T u i b) A q"
                by (rule forallE[where a=q, OF IHm q])
              show "evals (subst_T u i b) A q"
                using IHq sourceRun by (rule implE)
            qed
          qed
          have sxnz: "S x \<noteq> 0"
            by (rule sucNonZero[OF x])
          have loadN: "load_T (S x) N"
            by (rule load_T_N[OF sx])
          have loadLe: "load_T (S x) \<le> x = 1"
            by (rule le_suc_implies_leq[
                  OF decrease_T[OF sx sxnz] loadN x])
          have condN: "hyp_of (load_T (S x)) N"
            by (rule cpx_terminates[OF loadN])
          have tailN: "conc_of (load_T (S x)) N"
            by (rule cpy_terminates[OF loadN])
          have condLe: "hyp_of (load_T (S x)) \<le> x = 1"
            by (rule leq_trans[
                  OF condN loadN x cpx_mono[OF loadN] loadLe])
          have tailLe: "conc_of (load_T (S x)) \<le> x = 1"
            by (rule leq_trans[
                  OF tailN loadN x cpy_mono[OF loadN] loadLe])
          have leftN: "hyp_of (conc_of (load_T (S x))) N"
            by (rule cpx_terminates[OF tailN])
          have rightN: "conc_of (conc_of (load_T (S x))) N"
            by (rule cpy_terminates[OF tailN])
          have leftLe:
            "hyp_of (conc_of (load_T (S x))) \<le> x = 1"
            by (rule leq_trans[
                  OF leftN tailN x cpx_mono[OF tailN] tailLe])
          have rightLe:
            "conc_of (conc_of (load_T (S x))) \<le> x = 1"
            by (rule leq_trans[
                  OF rightN tailN x cpy_mono[OF tailN] tailLe])
          have IHload:
            "\<And>q. q N \<Longrightarrow>
              evals (subst_T (load_T (S x)) i a) A q \<Longrightarrow>
              evals (subst_T (load_T (S x)) i b) A q"
          proof -
            fix q
            assume q: "q N"
                and source:
                  "evals (subst_T (load_T (S x)) i a) A q"
            show "evals (subst_T (load_T (S x)) i b) A q"
              by (rule IHmeta[OF loadN loadLe q source])
          qed
          have IHcond:
            "\<And>q. q N \<Longrightarrow>
              evals (subst_T (hyp_of (load_T (S x))) i a) A q \<Longrightarrow>
              evals (subst_T (hyp_of (load_T (S x))) i b) A q"
          proof -
            fix q
            assume q: "q N"
                and source:
                  "evals (subst_T (hyp_of (load_T (S x))) i a) A q"
            show "evals (subst_T (hyp_of (load_T (S x))) i b) A q"
              by (rule IHmeta[OF condN condLe q source])
          qed
          have IHleft:
            "\<And>q. q N \<Longrightarrow>
              evals (subst_T (hyp_of (conc_of (load_T (S x)))) i a) A q \<Longrightarrow>
              evals (subst_T (hyp_of (conc_of (load_T (S x)))) i b) A q"
          proof -
            fix q
            assume q: "q N"
                and source:
                  "evals
                    (subst_T (hyp_of (conc_of (load_T (S x)))) i a) A q"
            show
              "evals
                (subst_T (hyp_of (conc_of (load_T (S x)))) i b) A q"
              by (rule IHmeta[OF leftN leftLe q source])
          qed
          have IHright:
            "\<And>q. q N \<Longrightarrow>
              evals (subst_T (conc_of (conc_of (load_T (S x)))) i a) A q \<Longrightarrow>
              evals (subst_T (conc_of (conc_of (load_T (S x)))) i b) A q"
          proof -
            fix q
            assume q: "q N"
                and source:
                  "evals
                    (subst_T (conc_of (conc_of (load_T (S x)))) i a) A q"
            show
              "evals
                (subst_T (conc_of (conc_of (load_T (S x)))) i b) A q"
              by (rule IHmeta[OF rightN rightLe q source])
          qed
          have tagN: "tag_T (S x) N"
            by (rule tag_T_N[OF sx])
          have varB: "(tag_T (S x) = T_VAR) B"
            by (rule eqBool[OF tagN], simp)
          have zeroB: "(tag_T (S x) = T_ZERO) B"
            by (rule eqBool[OF tagN], simp)
          have sucB: "(tag_T (S x) = T_SUC) B"
            by (rule eqBool[OF tagN], simp)
          have predB: "(tag_T (S x) = T_PRED) B"
            by (rule eqBool[OF tagN], simp)
          have ifzB: "(tag_T (S x) = T_IFZ) B"
            by (rule eqBool[OF tagN], simp)
          show "evals (subst_T (S x) i b) A r"
          proof (rule cases_bool[where q="tag_T (S x) = T_VAR"])
            show "(tag_T (S x) = T_VAR) B"
              by (rule varB)
          next
            assume tg: "tag_T (S x) = T_VAR"
            show "evals (subst_T (S x) i b) A r"
              by (rule evals_subst_T_var_transport[
                    OF sx i a b A r tg tr ev])
          next
            assume nvar: "\<not> tag_T (S x) = T_VAR"
            show "evals (subst_T (S x) i b) A r"
            proof (rule cases_bool[where q="tag_T (S x) = T_ZERO"])
              show "(tag_T (S x) = T_ZERO) B"
                by (rule zeroB)
            next
              assume tg: "tag_T (S x) = T_ZERO"
              show "evals (subst_T (S x) i b) A r"
                by (rule evals_subst_T_zero_transport[
                      OF sx i a b A r tg ev])
            next
              assume nzero: "\<not> tag_T (S x) = T_ZERO"
              show "evals (subst_T (S x) i b) A r"
              proof (rule cases_bool[where q="tag_T (S x) = T_SUC"])
                show "(tag_T (S x) = T_SUC) B"
                  by (rule sucB)
              next
                assume tg: "tag_T (S x) = T_SUC"
                show "evals (subst_T (S x) i b) A r"
                  by (rule evals_subst_T_suc_transport[
                        OF sx i a b A r tg IHload ev])
              next
                assume nsuc: "\<not> tag_T (S x) = T_SUC"
                show "evals (subst_T (S x) i b) A r"
                proof (rule cases_bool[where q="tag_T (S x) = T_PRED"])
                  show "(tag_T (S x) = T_PRED) B"
                    by (rule predB)
                next
                  assume tg: "tag_T (S x) = T_PRED"
                  show "evals (subst_T (S x) i b) A r"
                    by (rule evals_subst_T_pred_transport[
                          OF sx i a b A r tg IHload ev])
                next
                  assume npred: "\<not> tag_T (S x) = T_PRED"
                  show "evals (subst_T (S x) i b) A r"
                  proof (rule cases_bool[where q="tag_T (S x) = T_IFZ"])
                    show "(tag_T (S x) = T_IFZ) B"
                      by (rule ifzB)
                  next
                    assume tg: "tag_T (S x) = T_IFZ"
                    show "evals (subst_T (S x) i b) A r"
                      by (rule evals_subst_T_ifz_transport[
                            OF sx i a b A r tg
                              IHcond IHleft IHright ev])
                  next
                    assume nifz: "\<not> tag_T (S x) = T_IFZ"
                    show "evals (subst_T (S x) i b) A r"
                      by (rule evals_subst_T_default_transport[
                            OF sx i a b A r
                              nvar nzero nsuc npred nifz
                              IHleft IHright ev])
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  fix r
  assume r: "r N" and ev: "evals (subst_T t i a) A r"
  show "evals (subst_T t i b) A r"
    using ev
  proof (rule evalsE)
    fix k
    assume k: "k N"
        and run: "eval_fuel k (subst_T t i a) A = S r"
    have mainK:
      "\<forall>r.
        (eval_fuel k (subst_T t i a) A = S r) \<longrightarrow>
        evals (subst_T t i b) A r"
      by (rule forallE[where a=k, OF main k])
    have mainR:
      "(eval_fuel k (subst_T t i a) A = S r) \<longrightarrow>
        evals (subst_T t i b) A r"
      by (rule forallE[where a=r, OF mainK r])
    show "evals (subst_T t i b) A r"
      using mainR run by (rule implE)
  qed
qed

lemma evals_subst_T_transport:
  assumes t: "t N" and i: "i N" and a: "a N" and b: "b N"
      and A: "A N"
      and tr: "\<And>q. q N \<Longrightarrow> evals a A q \<Longrightarrow> evals b A q"
      and ev: "evals (subst_T t i a) A r"
  shows "evals (subst_T t i b) A r"
proof -
  have subN: "subst_T t i a N"
    by (rule subst_T_N[OF t i a])
  have r: "r N"
    using ev
  proof (rule evalsE)
    fix k
    assume k: "k N"
        and run: "eval_fuel k (subst_T t i a) A = S r"
    show "r N"
      by (rule eval_fuel_result_N[OF k subN A run])
  qed
  show ?thesis
    by (rule evals_subst_T_transport_aux[
          OF t i a b A tr r ev])
qed

lemma subst_F_eq_case:
  assumes f: "f N" and i: "i N" and v: "v N"
      and tg: "tag_F f = F_EQ"
  shows
    "subst_F f i v =
      pack_F F_EQ
        \<langle>subst_T (hyp_of (load_F f)) i v,
         subst_T (conc_of (load_F f)) i v\<rangle>"
proof -
  let ?l = "subst_T (hyp_of (load_F f)) i v"
  let ?r = "subst_T (conc_of (load_F f)) i v"
  let ?u = "pack_F F_EQ \<langle>?l, ?r\<rangle>"
  have loadN: "load_F f N"
    by (rule load_F_N[OF f])
  have leftN: "hyp_of (load_F f) N"
    by (rule cpx_terminates[OF loadN])
  have rightN: "conc_of (load_F f) N"
    by (rule cpy_terminates[OF loadN])
  have lN: "?l N"
    by (rule subst_T_N[OF leftN i v])
  have rN: "?r N"
    by (rule subst_T_N[OF rightN i v])
  have argsN: "\<langle>?l, ?r\<rangle> N"
    using lN rN by simp
  have uN: "?u N"
    by (rule pack_F_N[OF _ argsN], simp)
  show ?thesis
    apply (rule defE[OF subst_F_def[where f=f and j=i and v=v]])
    apply (rule condI1Eq[OF tg uN])
    using uN by simp
qed

lemma subst_F_neq_case:
  assumes f: "f N" and i: "i N" and v: "v N"
      and tg: "\<not> tag_F f = F_EQ"
  shows
    "subst_F f i v =
      pack_F F_NEQ
        \<langle>subst_T (hyp_of (load_F f)) i v,
         subst_T (conc_of (load_F f)) i v\<rangle>"
proof -
  let ?l = "subst_T (hyp_of (load_F f)) i v"
  let ?r = "subst_T (conc_of (load_F f)) i v"
  let ?u = "pack_F F_NEQ \<langle>?l, ?r\<rangle>"
  have loadN: "load_F f N"
    by (rule load_F_N[OF f])
  have leftN: "hyp_of (load_F f) N"
    by (rule cpx_terminates[OF loadN])
  have rightN: "conc_of (load_F f) N"
    by (rule cpy_terminates[OF loadN])
  have lN: "?l N"
    by (rule subst_T_N[OF leftN i v])
  have rN: "?r N"
    by (rule subst_T_N[OF rightN i v])
  have argsN: "\<langle>?l, ?r\<rangle> N"
    using lN rN by simp
  have uN: "?u N"
    by (rule pack_F_N[OF _ argsN], simp)
  show ?thesis
    apply (rule defE[OF subst_F_def[where f=f and j=i and v=v]])
    apply (rule condI2Eq[OF tg uN])
    using uN by simp
qed

lemma sat_fuel_pack_transport:
  assumes g: "g N"
      and l1: "l1 N" and r1: "r1 N"
      and l2: "l2 N" and r2: "r2 N"
      and A: "A N"
      and trL: "\<And>q. q N \<Longrightarrow> evals l1 A q \<Longrightarrow> evals l2 A q"
      and trR: "\<And>q. q N \<Longrightarrow> evals r1 A q \<Longrightarrow> evals r2 A q"
      and sat: "sat_fuel (pack_F g \<langle>l1, r1\<rangle>) A"
  shows "sat_fuel (pack_F g \<langle>l2, r2\<rangle>) A"
proof -
  let ?args1 = "\<langle>l1, r1\<rangle>"
  let ?args2 = "\<langle>l2, r2\<rangle>"
  let ?f1 = "pack_F g ?args1"
  let ?f2 = "pack_F g ?args2"
  have args1N: "?args1 N"
    using l1 r1 by simp
  have args2N: "?args2 N"
    using l2 r2 by simp
  have f1N: "?f1 N"
    by (rule pack_F_N[OF g args1N])
  have f2N: "?f2 N"
    by (rule pack_F_N[OF g args2N])
  have tag1: "tag_F ?f1 = g"
    by (rule tag_pack_F[OF g args1N])
  have tag2: "tag_F ?f2 = g"
    by (rule tag_pack_F[OF g args2N])
  have tagEq: "tag_F ?f1 = tag_F ?f2"
    using tag1 eqSym[OF tag2] by (rule eq_trans)
  have load1: "load_F ?f1 = ?args1"
    by (rule load_pack_F[OF g args1N])
  have load2: "load_F ?f2 = ?args2"
    by (rule load_pack_F[OF g args2N])
  have args1Left: "hyp_of ?args1 = l1"
    by (rule cpx_proj[OF l1 r1])
  have args1Right: "conc_of ?args1 = r1"
    by (rule cpy_proj[OF l1 r1])
  have args2Left: "hyp_of ?args2 = l2"
    by (rule cpx_proj[OF l2 r2])
  have args2Right: "conc_of ?args2 = r2"
    by (rule cpy_proj[OF l2 r2])
  have selectLeft1: "hyp_of (load_F ?f1) = l1"
    by (rule eqSubst[
          where a="?args1" and b="load_F ?f1"
            and Q="\<lambda>z. hyp_of z = l1",
          OF eqSym[OF load1] args1Left])
  have selectRight1: "conc_of (load_F ?f1) = r1"
    by (rule eqSubst[
          where a="?args1" and b="load_F ?f1"
            and Q="\<lambda>z. conc_of z = r1",
          OF eqSym[OF load1] args1Right])
  have selectLeft2: "hyp_of (load_F ?f2) = l2"
    by (rule eqSubst[
          where a="?args2" and b="load_F ?f2"
            and Q="\<lambda>z. hyp_of z = l2",
          OF eqSym[OF load2] args2Left])
  have selectRight2: "conc_of (load_F ?f2) = r2"
    by (rule eqSubst[
          where a="?args2" and b="load_F ?f2"
            and Q="\<lambda>z. conc_of z = r2",
          OF eqSym[OF load2] args2Right])
  show ?thesis
    using sat
  proof (rule sat_fuelE)
    fix x y
    assume x: "x N" and y: "y N"
        and left1: "evals (hyp_of (load_F ?f1)) A x"
        and right1: "evals (conc_of (load_F ?f1)) A y"
        and relation1:
          "if tag_F ?f1 = F_EQ then x = y else x \<noteq> y"
    have evalLeft1: "evals l1 A x"
      by (rule eqSubst[
            where a="hyp_of (load_F ?f1)" and b=l1
              and Q="\<lambda>z. evals z A x",
            OF selectLeft1 left1])
    have evalRight1: "evals r1 A y"
      by (rule eqSubst[
            where a="conc_of (load_F ?f1)" and b=r1
              and Q="\<lambda>z. evals z A y",
            OF selectRight1 right1])
    have evalLeft2: "evals l2 A x"
      by (rule trL[OF x evalLeft1])
    have evalRight2: "evals r2 A y"
      by (rule trR[OF y evalRight1])
    have left2: "evals (hyp_of (load_F ?f2)) A x"
      by (rule eqSubst[
            where a=l2 and b="hyp_of (load_F ?f2)"
              and Q="\<lambda>z. evals z A x",
            OF eqSym[OF selectLeft2] evalLeft2])
    have right2: "evals (conc_of (load_F ?f2)) A y"
      by (rule eqSubst[
            where a=r2 and b="conc_of (load_F ?f2)"
              and Q="\<lambda>z. evals z A y",
            OF eqSym[OF selectRight2] evalRight2])
    have relation2:
      "if tag_F ?f2 = F_EQ then x = y else x \<noteq> y"
      by (rule eqSubst[
            where a="tag_F ?f1" and b="tag_F ?f2"
              and Q="\<lambda>z. if z = F_EQ then x = y else x \<noteq> y",
            OF tagEq relation1])
    show "sat_fuel ?f2 A"
      unfolding sat_fuel_def
      apply (rule existsI[where a=x])
      apply (rule x)
      apply (rule existsI[where a=y])
      apply (rule y)
      apply (rule conjI)
      apply (rule left2)
      apply (rule conjI)
      apply (rule right2)
      apply (rule relation2)
      done
  qed
qed

lemma sat_fuel_subst_F_transport:
  assumes f: "f N" and i: "i N" and a: "a N" and b: "b N"
      and A: "A N"
      and tr: "\<And>q. q N \<Longrightarrow> evals a A q \<Longrightarrow> evals b A q"
      and sat: "sat_fuel (subst_F f i a) A"
  shows "sat_fuel (subst_F f i b) A"
proof -
  let ?l = "hyp_of (load_F f)"
  let ?r = "conc_of (load_F f)"
  let ?la = "subst_T ?l i a"
  let ?lb = "subst_T ?l i b"
  let ?ra = "subst_T ?r i a"
  let ?rb = "subst_T ?r i b"
  have loadN: "load_F f N"
    by (rule load_F_N[OF f])
  have lN: "?l N"
    by (rule cpx_terminates[OF loadN])
  have rN: "?r N"
    by (rule cpy_terminates[OF loadN])
  have laN: "?la N"
    by (rule subst_T_N[OF lN i a])
  have lbN: "?lb N"
    by (rule subst_T_N[OF lN i b])
  have raN: "?ra N"
    by (rule subst_T_N[OF rN i a])
  have rbN: "?rb N"
    by (rule subst_T_N[OF rN i b])
  have trL:
    "\<And>q. q N \<Longrightarrow> evals ?la A q \<Longrightarrow> evals ?lb A q"
  proof -
    fix q
    assume q: "q N" and ev: "evals ?la A q"
    show "evals ?lb A q"
      by (rule evals_subst_T_transport[OF lN i a b A tr ev])
  qed
  have trR:
    "\<And>q. q N \<Longrightarrow> evals ?ra A q \<Longrightarrow> evals ?rb A q"
  proof -
    fix q
    assume q: "q N" and ev: "evals ?ra A q"
    show "evals ?rb A q"
      by (rule evals_subst_T_transport[OF rN i a b A tr ev])
  qed
  have tagN: "tag_F f N"
    by (rule tag_F_N[OF f])
  have eqB: "(tag_F f = F_EQ) B"
    by (rule eqBool[OF tagN], simp)
  show ?thesis
  proof (rule cases_bool[where q="tag_F f = F_EQ"])
    show "(tag_F f = F_EQ) B"
      by (rule eqB)
  next
    assume tg: "tag_F f = F_EQ"
    let ?fa = "pack_F F_EQ \<langle>?la, ?ra\<rangle>"
    let ?fb = "pack_F F_EQ \<langle>?lb, ?rb\<rangle>"
    have subA: "subst_F f i a = ?fa"
      by (rule subst_F_eq_case[OF f i a tg])
    have subB: "subst_F f i b = ?fb"
      by (rule subst_F_eq_case[OF f i b tg])
    have satA: "sat_fuel ?fa A"
      by (rule eqSubst[
            where a="subst_F f i a" and b="?fa"
              and Q="\<lambda>z. sat_fuel z A",
            OF subA sat])
    have satB: "sat_fuel ?fb A"
      by (rule sat_fuel_pack_transport[
            OF _ laN raN lbN rbN A trL trR satA], simp)
    show "sat_fuel (subst_F f i b) A"
      by (rule eqSubst[
            where a="?fb" and b="subst_F f i b"
              and Q="\<lambda>z. sat_fuel z A",
            OF eqSym[OF subB] satB])
  next
    assume tg: "\<not> tag_F f = F_EQ"
    let ?fa = "pack_F F_NEQ \<langle>?la, ?ra\<rangle>"
    let ?fb = "pack_F F_NEQ \<langle>?lb, ?rb\<rangle>"
    have subA: "subst_F f i a = ?fa"
      by (rule subst_F_neq_case[OF f i a tg])
    have subB: "subst_F f i b = ?fb"
      by (rule subst_F_neq_case[OF f i b tg])
    have satA: "sat_fuel ?fa A"
      by (rule eqSubst[
            where a="subst_F f i a" and b="?fa"
              and Q="\<lambda>z. sat_fuel z A",
            OF subA sat])
    have satB: "sat_fuel ?fb A"
      by (rule sat_fuel_pack_transport[
            OF _ laN raN lbN rbN A trL trR satA], simp)
    show "sat_fuel (subst_F f i b) A"
      by (rule eqSubst[
            where a="?fb" and b="subst_F f i b"
              and Q="\<lambda>z. sat_fuel z A",
            OF eqSym[OF subB] satB])
  qed
qed

lemma check_templateE:
  assumes f: "f N" and phi: "phi N"
      and a: "a N" and b: "b N"
      and p: "p N" and i: "i N"
      and chk: "check_template f phi a b p i"
      and H:
        "\<And>q. q N \<Longrightarrow>
          subst_F q i a = phi \<Longrightarrow>
          subst_F q i b = f \<Longrightarrow> R"
  shows R
proof -
  have main: "check_template f phi a b p i \<turnstile> R"
  proof (rule ind[OF p])
    show "check_template f phi a b 0 i \<turnstile> R"
    proof (rule entailsI)
      assume chk0: "check_template f phi a b 0 i"
      have C0: "if subst_F 0 i a = phi \<and> subst_F 0 i b = f then True
                  else if 0 > 0 = 1 then check_template f phi a b (0 - 1) i
                  else False"
        using chk0
        by (rule defI[OF check_template_def[
              where f=f and phi=phi and a=a and b=b and p=0 and i=i]])
      have C: "if subst_F 0 i a = phi \<and> subst_F 0 i b = f then True else False"
        using C0 by simp
      have sa: "subst_F 0 i a N"
        by (rule subst_F_N[OF nat0 i a])
      have sb: "subst_F 0 i b N"
        by (rule subst_F_N[OF nat0 i b])
      have eaB: "(subst_F 0 i a = phi) B"
        by (rule eqBool[OF sa phi])
      have ebB: "(subst_F 0 i b = f) B"
        by (rule eqBool[OF sb f])
      have bothB: "(subst_F 0 i a = phi \<and> subst_F 0 i b = f) B"
        using eaB ebB by simp
      show R
      proof (rule cases_bool[where q="subst_F 0 i a = phi \<and> subst_F 0 i b = f"])
        show "(subst_F 0 i a = phi \<and> subst_F 0 i b = f) B"
          by (rule bothB)
      next
        assume both: "subst_F 0 i a = phi \<and> subst_F 0 i b = f"
        have ea: "subst_F 0 i a = phi"
          using both by (rule conjE1)
        have eb: "subst_F 0 i b = f"
          using both by (rule conjE2)
        show R
          using nat0 ea eb by (rule H)
      next
        assume nboth: "\<not>(subst_F 0 i a = phi \<and> subst_F 0 i b = f)"
        have F: "False"
          using nboth C by (rule notcond_thenE)
        show R
          by (rule exF[OF F not_false])
      qed
    qed
   next
    fix k
    assume k: "k N"
       and IH: "check_template f phi a b k i \<turnstile> R"
    show "check_template f phi a b (S k) i \<turnstile> R"
    proof (rule entailsI)
      assume chks: "check_template f phi a b (S k) i"
      have C0: "if subst_F (S k) i a = phi \<and> subst_F (S k) i b = f then True
                  else if S k > 0 = 1 then check_template f phi a b (S k - 1) i
                  else False"
        using chks
        by (rule defI[OF check_template_def[where f=f and phi=phi and a=a and b=b and p="S k" and i=i]])
      have sk: "S k N"
        using k by simp
      have gt: "S k > 0 = 1"
        using k by simp
      have sk1: "S k - 1 = k"
        using k by simp
      have sa: "subst_F (S k) i a N"
        by (rule subst_F_N[OF sk i a])
      have sb: "subst_F (S k) i b N"
        by (rule subst_F_N[OF sk i b])
      have eaB: "(subst_F (S k) i a = phi) B"
        by (rule eqBool[OF sa phi])
      have ebB: "(subst_F (S k) i b = f) B"
        by (rule eqBool[OF sb f])
      have bothB: "(subst_F (S k) i a = phi \<and> subst_F (S k) i b = f) B"
        using eaB ebB by simp
      show R
      proof (rule cases_bool[where q="subst_F (S k) i a = phi \<and> subst_F (S k) i b = f"])
        show "(subst_F (S k) i a = phi \<and> subst_F (S k) i b = f) B"
          by (rule bothB)
      next
        assume both: "subst_F (S k) i a = phi \<and> subst_F (S k) i b = f"
        have ea: "subst_F (S k) i a = phi"
          using both by (rule conjE1)
        have eb: "subst_F (S k) i b = f"
          using both by (rule conjE2)
        show R
          using sk ea eb by (rule H)
      next
        assume nboth: "\<not>(subst_F (S k) i a = phi \<and> subst_F (S k) i b = f)"
        have C1: "if S k > 0 = 1 then check_template f phi a b (S k - 1) i else False"
          using nboth C0 by (rule notcond_thenE)
        have chkp: "check_template f phi a b (S k - 1) i"
          using gt C1 by (rule cond_thenE)
        have chkk: "check_template f phi a b k i"
          using sk1 chkp
          by (rule eqSubst[where Q="\<lambda>q. check_template f phi a b q i"])
        show R
          using IH chkk by (rule entailsE)
      qed
    qed
  qed
  show R
    using main chk by (rule entailsE)
qed

lemma check_template_sound_fuel:
  assumes f: "f N" and phi: "phi N"
      and a: "a N" and b: "b N"
      and p: "p N" and i: "i N" and A: "A N"
      and chk: "check_template f phi a b p i"
      and satPhi: "sat_fuel phi A"
      and tr: "\<And>q. q N \<Longrightarrow> evals a A q \<Longrightarrow> evals b A q"
  shows "sat_fuel f A"
proof (rule check_templateE[OF f phi a b p i chk])
  fix q
  assume q: "q N"
      and qa: "subst_F q i a = phi"
      and qb: "subst_F q i b = f"
  have satA: "sat_fuel (subst_F q i a) A"
    using eqSym[OF qa] satPhi
    by (rule eqSubst[where Q="\<lambda>z. sat_fuel z A"])
  have satB: "sat_fuel (subst_F q i b) A"
    by (rule sat_fuel_subst_F_transport[
          OF q i a b A tr satA])
  show "sat_fuel f A"
    using qb satB
    by (rule eqSubst[where Q="\<lambda>z. sat_fuel z A"])
qed

lemma subset_cons_headE:
  assumes h: "h N" and t: "t N" and G: "G N"
      and sub: "subset (h \<triangleright> t) G"
  shows "h \<in> G"
proof -
  have C: "h \<in> G \<and> subset t G"
    using h t G sub by simp
  show ?thesis
    using C by (rule conjE1)
qed

lemma subset_cons_tailE:
  assumes h: "h N" and t: "t N" and G: "G N"
      and sub: "subset (h \<triangleright> t) G"
  shows "subset t G"
proof -
  have C: "h \<in> G \<and> subset t G"
    using h t G sub by simp
  show ?thesis
    using C by (rule conjE2)
qed

lemma find_phiE:
  assumes J: "J N" and a: "a N" and b: "b N"
      and rest: "rest N" and ptr: "ptr N"
      and sub: "subset ptr rest"
      and fp: "find_phi J a b ptr"
      and H:
        "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
          hyp_of K = hyp_of J \<Longrightarrow>
          check_template (conc_of J) (conc_of K) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1) \<Longrightarrow> R"
  shows R
proof -
  have main: "subset ptr rest \<turnstile> (find_phi J a b ptr \<turnstile> R)"
  proof (rule list_induct[OF ptr])
    show "subset Nil rest \<turnstile> (find_phi J a b Nil \<turnstile> R)"
    proof (rule entailsI)
      assume sub0: "subset Nil rest"
      show "find_phi J a b Nil \<turnstile> R"
      proof (rule entailsI)
        assume fp0: "find_phi J a b Nil"
        have C0: "if Nil = Nil then False
                    else if hyp_of (list_hd Nil) = hyp_of J \<and>
                               check_template (conc_of J) (conc_of (list_hd Nil)) a b
                              (rep_vars_F (conc_of J) (J + 1)) (J + 1)
                    then True
                    else find_phi J a b (list_tl Nil)"
          using fp0
          by (rule defI[OF find_phi_def[
                where J=J and a=a and b=b and ptr=Nil]])
        have F: "False"
          using C0 by simp
        show R
          by (rule exF[OF F not_false])
      qed
    qed
  next
    fix h t
    assume h: "h N"
       and t: "t N"
       and IH: "subset t rest \<turnstile> (find_phi J a b t \<turnstile> R)"
    show "subset (Cons h t) rest \<turnstile> (find_phi J a b (Cons h t) \<turnstile> R)"
    proof (rule entailsI)
      assume subht: "subset (Cons h t) rest"
      have hrest: "mem h rest"
        using h t rest subht by (rule subset_cons_headE)
      have subt: "subset t rest"
        using h t rest subht by (rule subset_cons_tailE)
      show "find_phi J a b (Cons h t) \<turnstile> R"
      proof (rule entailsI)
        assume fpht: "find_phi J a b (Cons h t)"
        have C0: "if Cons h t = Nil then False
                    else if hyp_of (list_hd (Cons h t)) = hyp_of J \<and> 
                                     check_template (conc_of J) (conc_of (list_hd (Cons h t))) a b
                                     (rep_vars_F (conc_of J) (J + 1)) (J + 1)
                    then True
                    else find_phi J a b (list_tl (Cons h t))"
          using fpht
          by (rule defI[OF find_phi_def[
                where J=J and a=a and b=b and ptr="Cons h t"]])
        have C: "if Cons h t = Nil then False
                   else if hyp_of h = hyp_of J \<and> check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1)
                   then True
                   else find_phi J a b t"
          using C0
          by (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
        have ne: "\<not>(Cons h t = Nil)"
          using h t by simp
        have C1: "if hyp_of h = hyp_of J \<and> check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1)
                    then True
                    else find_phi J a b t"
          using ne C by (rule notcond_thenE)
        have cJ: "conc_of J N"
          using J by simp
        have ch: "conc_of h N"
          using h by simp
        have ji: "J + 1 N"
          using J by simp
        have rp: "rep_vars_F (conc_of J) (J + 1) N"
          by (rule rep_vars_F_N[OF cJ ji])
        have eqB: "(hyp_of h = hyp_of J) B"
          using h J by simp
        have ctB: "check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1) B"
          by (rule check_template_bool[OF cJ ch a b ji rp])
        have bothB: "(hyp_of h = hyp_of J \<and> check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1)) B"
          using eqB ctB by simp
        show R
        proof (rule cases_bool[where q="hyp_of h = hyp_of J \<and> check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1)"])
          show "(hyp_of h = hyp_of J \<and>  check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1)) B"
            by (rule bothB)
        next
          assume both: "hyp_of h = hyp_of J \<and> check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1)"
          have heq: "hyp_of h = hyp_of J"
            using both by (rule conjE1)
          have ct: "check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1)"
            using both by (rule conjE2)
          show R
            using h hrest heq ct by (rule H)
        next
          assume nboth: "\<not>(hyp_of h = hyp_of J \<and> check_template (conc_of J) (conc_of h) a b (rep_vars_F (conc_of J) (J + 1)) (J + 1))"
          have fpt: "find_phi J a b t"
            using nboth C1 by (rule notcond_thenE)
          have IR: "find_phi J a b t \<turnstile> R"
            using IH subt by (rule entailsE)
          show R
            using IR fpt by (rule entailsE)
        qed
      qed
    qed
  qed
  have IR: "find_phi J a b ptr \<turnstile> R"
    using main sub by (rule entailsE)
  show R
    using IR fp by (rule entailsE)
qed

lemma find_phi_sound_fuel:
  assumes J: "J N" and a: "a N" and b: "b N"
      and rest: "rest N" and ptr: "ptr N" and A: "A N"
      and sub: "subset ptr rest"
      and fp: "find_phi J a b ptr"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
        sat_hyp_fuel (hyp_of K) A \<Longrightarrow>
        sat_fuel (conc_of K) A"
      and satG: "sat_hyp_fuel (hyp_of J) A"
      and tr: "\<And>q. q N \<Longrightarrow> evals a A q \<Longrightarrow> evals b A q"
  shows "sat_fuel (conc_of J) A"
proof (rule find_phiE[OF J a b rest ptr sub fp])
  fix K
  assume K: "K N"
      and Km: "mem K rest"
      and Kh: "hyp_of K = hyp_of J"
      and chk:
        "check_template
          (conc_of J) (conc_of K) a b
          (rep_vars_F (conc_of J) (J + 1)) (J + 1)"
  let ?f = "conc_of J"
  let ?phi = "conc_of K"
  let ?i = "J + 1"
  let ?p = "rep_vars_F ?f ?i"
  have fN: "?f N"
    using J by simp
  have phiN: "?phi N"
    using K by simp
  have iN: "?i N"
    using J by simp
  have pN: "?p N"
    by (rule rep_vars_F_N[OF fN iN])
  have hKJ: "hyp_of J = hyp_of K"
    by (rule eqSym[OF Kh])
  have satKh: "sat_hyp_fuel (hyp_of K) A"
    using hKJ satG
    by (rule eqSubst[where Q="\<lambda>G. sat_hyp_fuel G A"])
  have satK: "sat_fuel ?phi A"
    by (rule prev[OF K Km satKh])
  show "sat_fuel ?f A"
    by (rule check_template_sound_fuel[
          OF fN phiN a b pN iN A chk satK tr])
qed

lemma mem_cons_head:
  assumes h: "h N" and t: "t N"
  shows "h \<in> (h \<triangleright> t)"
  using h t by simp

lemma mem_cons_tail:
  assumes h: "h N"
      and t: "t N"
      and x: "x N"
      and xt: "x \<in> t"
  shows "x \<in> (h \<triangleright> t)"
proof -
  have rhs: "if h = x then True else x \<in> t"
  proof (rule cases_bool[where q="h = x"])
    show "(h = x) B"
      by (rule eqBool[OF h x])
  next
    assume hx: "h = x"
    have e: "(if h = x then True else x \<in> t) \<longleftrightarrow> True"
      by (rule condI1B[OF hx true_bool])
    show "if h = x then True else x \<in> t"
      using true e by simp
  next
    assume hx: "\<not> (h = x)"
    have e: "(if h = x then True else x \<in> t) \<longleftrightarrow> x \<in> t"
      by (rule condI2B[OF hx mem_bool[OF x t]])
    show "if h = x then True else x \<in> t"
      using xt e by simp
  qed
  have bck: "(if h = x then True else x \<in> t) \<longrightarrow> x \<in> (h \<triangleright> t)"
    by (rule iffE2[OF mem_cons[OF h t x]])
  show "x \<in> (h \<triangleright> t)"
    using bck rhs
    by (rule implE)
qed

lemma subset_nilI:
  assumes G: "G N"
  shows "subset Nil G"
proof -
  have nn: "Nil = Nil"
    using nil_nat by simp
  have eq: "subset Nil G \<longleftrightarrow> True"
    apply (rule defE[OF subset_def[where G'=Nil and G=G]])
    apply (rule condI1B[OF nn true_bool])
    done
  have bck: "True \<longrightarrow> subset Nil G"
    by (rule iffE2[OF eq])
  show ?thesis
    using bck true by (rule implE)
qed

lemma subset_cons_right:
  assumes h: "h N"
      and G': "G' N"
      and G: "G N"
      and sub: "subset G' G"
  shows "subset G' (h \<triangleright> G)"
proof -
  have hG: "h \<triangleright> G N"
    using h G by simp
  have main: "subset G' G \<longrightarrow> subset G' (h \<triangleright> G)"
  proof (rule list_induct[OF G', where Q="\<lambda>L. subset L G \<longrightarrow> subset L (h \<triangleright> G)"])
    show "subset Nil G \<longrightarrow> subset Nil (h \<triangleright> G)"
    proof (rule implI)
      show "subset Nil G B"
        by (rule subset_bool[OF nil_nat G])
    next
      assume "subset Nil G"
      show "subset Nil (h \<triangleright> G)"
        by (rule subset_nilI[OF hG])
    qed
  next
    fix a t
    assume a: "a N"
       and t: "t N"
       and IH: "subset t G \<longrightarrow> subset t (h \<triangleright> G)"
    have atN: "a \<triangleright> t N"
      using a t by simp
    show "subset (a \<triangleright> t) G \<longrightarrow> subset (a \<triangleright> t) (h \<triangleright> G)"
    proof (rule implI)
      show "subset (a \<triangleright> t) G B"
        by (rule subset_bool[OF atN G])
    next
      assume atG: "subset (a \<triangleright> t) G"
      have split: "mem a G \<and> subset t G"
        using atG a t G by simp
      have aG: "mem a G"
        using split by (rule conjE1)
      have tG: "subset t G"
        using split by (rule conjE2)
      have thG: "subset t (h \<triangleright> G)"
        using IH tG by (rule implE)
      have ahG: "mem a (h \<triangleright> G)"
        using h G a aG by (rule mem_cons_tail)
      have pair: "mem a (h \<triangleright> G) \<and> subset t (h \<triangleright> G)"
        apply (rule conjI)
        apply (rule ahG)
        apply (rule thG)
        done
      have eq:
        "subset (a \<triangleright> t) (h \<triangleright> G) \<longleftrightarrow>
         (mem a (h \<triangleright> G) \<and> subset t (h \<triangleright> G))"
        by (rule subset_cons[OF a t hG])
      have bck: "(mem a (h \<triangleright> G) \<and> subset t (h \<triangleright> G)) \<longrightarrow> subset (a \<triangleright> t) (h \<triangleright> G)"
        by (rule iffE2[OF eq])
      show "subset (a \<triangleright> t) (h \<triangleright> G)"
        using bck pair by (rule implE)
    qed
  qed
  show ?thesis
    using main sub by (rule implE)
qed

lemma subset_refl:
  assumes G: "G N"
  shows "subset G G"
proof (rule list_induct[OF G])
  show "subset Nil Nil"
    by (rule subset_nilI[OF nil_nat])
next
  fix h t
  assume h: "h N"
     and t: "t N"
     and IH: "subset t t"
  have htN: "h \<triangleright> t N"
    using h t by simp
  have tail: "subset t (h \<triangleright> t)"
    using h t t IH by (rule subset_cons_right)
  have head: "mem h (h \<triangleright> t)"
    using h t by simp
  have pair: "mem h (h \<triangleright> t) \<and> subset t (h \<triangleright> t)"
    apply (rule conjI)
    apply (rule head)
    apply (rule tail)
    done
  have eq: "subset (h \<triangleright> t) (h \<triangleright> t) \<longleftrightarrow> (mem h (h \<triangleright> t) \<and> subset t (h \<triangleright> t))"
    by (rule subset_cons[OF h t htN])
  have bck: "(mem h (h \<triangleright> t) \<and> subset t (h \<triangleright> t)) \<longrightarrow> subset (h \<triangleright> t) (h \<triangleright> t)"
    by (rule iffE2[OF eq])
  show "subset (h \<triangleright> t) (h \<triangleright> t)"
    using bck pair by (rule implE)
qed

lemma check_app_sound_fuel:
  assumes J: "J N" and rest: "rest N" and A: "A N"
      and chk: "check_app J rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
        sat_hyp_fuel (hyp_of K) A \<Longrightarrow>
        sat_fuel (conc_of K) A"
      and satG: "sat_hyp_fuel (hyp_of J) A"
  shows "sat_fuel (conc_of J) A"
proof (rule check_appE[OF J rest chk])
  fix d x y
  assume d: "d N" and x: "x N" and y: "y N"
      and app: "app_try J d x y rest"
  show "sat_fuel (conc_of J) A"
  proof (rule app_try_argsE[
      OF J rest d x y A app prev satG])
    fix vx vy
    assume vx: "vx N" and vy: "vy N"
        and di: "dfn_is d 2 (nth d dfns)"
        and evx: "evals x A vx"
        and evy: "evals y A vy"
        and fp:
          "find_phi J
            (subst_body (nth d dfns) x y)
            (pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>)
            rest"
    let ?body = "nth d dfns"
    let ?subBody = "subst_body ?body x y"
    let ?app = "pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>"
    have bodyN: "?body N"
      by (rule nth_N'[OF dfns_N d])
    have subBodyN: "?subBody N"
      by (rule subst_body_N[OF bodyN x y])
    have argsN: "\<langle>x, y\<rangle> N"
      using x y by simp
    have payloadN: "\<langle>d, \<langle>x, y\<rangle>\<rangle> N"
      using d argsN by simp
    have appN: "?app N"
      by (rule pack_T_N[OF _ payloadN], simp)
    have sub: "subset rest rest"
      by (rule subset_refl[OF rest])
    have tr:
      "\<And>q. q N \<Longrightarrow>
        evals ?subBody A q \<Longrightarrow>
        evals ?app A q"
    proof -
      fix q
      assume q: "q N" and evBody: "evals ?subBody A q"
      show "evals ?app A q"
        by (rule evals_subst_body_appI[
              OF d x y A vx vy di evx evy evBody])
    qed
    show "sat_fuel (conc_of J) A"
      by (rule find_phi_sound_fuel[
            OF J subBodyN appN rest rest A
              sub fp prev satG tr])
  qed
qed

lemma sat_hyp_fuel_subset:
  assumes sub: "subset G' G" and G': "G' N" and G: "G N"
      and satG: "sat_hyp_fuel G A"
  shows "sat_hyp_fuel G' A"
proof -
  show ?thesis
    unfolding sat_hyp_fuel_def
    apply (rule forallI)
    apply (rule implI)
     apply (simp add: G')
    apply (rule G')
  proof -
    fix f
    assume f: "f N" and fG': "f \<in> G'"
    have fG: "f \<in> G"
      using f G' G sub fG' by (rule subset_mem)
    show "sat_fuel f A"
      by (rule sat_hyp_fuel_mem[OF f fG satG])
  qed
qed

lemma find_structE:
  assumes J: "J N" and G: "G N" and rest: "rest N" and ptr: "ptr N"
      and sub: "subset ptr rest"
      and fs: "find_struct J G ptr"
      and H: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   conc_of K = conc_of J \<Longrightarrow>
                   subset (hyp_of K) G \<Longrightarrow> R"
  shows R
proof -
  have main: "subset ptr rest \<turnstile> (find_struct J G ptr \<turnstile> R)"
  proof (rule list_induct[OF ptr])
    show "subset Nil rest \<turnstile> (find_struct J G Nil \<turnstile> R)"
    proof (rule entailsI)
      assume sub0: "subset Nil rest"
      show "find_struct J G Nil \<turnstile> R"
      proof (rule entailsI)
        assume fs0: "find_struct J G Nil"
        have C0: "if Nil = Nil then False
                    else if conc_of (list_hd Nil) = conc_of J \<and>
                            subset (hyp_of (list_hd Nil)) G then True
                    else find_struct J G (list_tl Nil)"
          using fs0
          by (rule defI[OF find_struct_def[where J=J and G=G and ptr=Nil]])
        have F: "False" using C0 by simp
        show R by (rule exF[OF F not_false])
      qed
    qed
  next
    fix h t
    assume h: "h N" and t: "t N"
       and IH: "subset t rest \<turnstile> (find_struct J G t \<turnstile> R)"
    show "subset (Cons h t) rest \<turnstile> (find_struct J G (Cons h t) \<turnstile> R)"
    proof (rule entailsI)
      assume subht: "subset (Cons h t) rest"
      have hrest: "mem h rest"
        using h t rest subht by (rule subset_cons_headE)
      have subt: "subset t rest"
        using h t rest subht by (rule subset_cons_tailE)
      show "find_struct J G (Cons h t) \<turnstile> R"
      proof (rule entailsI)
        assume fsht: "find_struct J G (Cons h t)"
        have C0: "if Cons h t = Nil then False
                    else if conc_of (list_hd (Cons h t)) = conc_of J \<and>
                            subset (hyp_of (list_hd (Cons h t))) G then True
                    else find_struct J G (list_tl (Cons h t))"
          using fsht
          by (rule defI[OF find_struct_def[where J=J and G=G and ptr="Cons h t"]])
        have C: "if Cons h t = Nil then False
                   else if conc_of h = conc_of J \<and> subset (hyp_of h) G then True
                   else find_struct J G t"
          using C0
          by (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
        have ne: "\<not> (Cons h t = Nil)" using h t by simp
        have C1: "if conc_of h = conc_of J \<and> subset (hyp_of h) G then True
                  else find_struct J G t"
          using ne C by (rule notcond_thenE)
        have ch: "conc_of h N" using h by simp
        have cJ: "conc_of J N" using J by simp
        have hh: "hyp_of h N" using h by simp
        have eqcB: "(conc_of h = conc_of J) B" by (rule eqBool[OF ch cJ])
        have subBd: "(subset (hyp_of h) G) B" by (rule subset_bool[OF hh G])
        have bothB: "(conc_of h = conc_of J \<and> subset (hyp_of h) G) B"
          using eqcB subBd by simp
        show R
        proof (rule cases_bool[where q="conc_of h = conc_of J \<and> subset (hyp_of h) G"])
          show "(conc_of h = conc_of J \<and> subset (hyp_of h) G) B" by (rule bothB)
        next
          assume both: "conc_of h = conc_of J \<and> subset (hyp_of h) G"
          have hceq: "conc_of h = conc_of J" using both by (rule conjE1)
          have hsub: "subset (hyp_of h) G" using both by (rule conjE2)
          show R using h hrest hceq hsub by (rule H)
        next
          assume nboth: "\<not> (conc_of h = conc_of J \<and> subset (hyp_of h) G)"
          have fst: "find_struct J G t" using nboth C1 by (rule notcond_thenE)
          have IR: "find_struct J G t \<turnstile> R" using IH subt by (rule entailsE)
          show R using IR fst by (rule entailsE)
        qed
      qed
    qed
  qed
  have IR: "find_struct J G ptr \<turnstile> R" using main sub by (rule entailsE)
  show R using IR fs by (rule entailsE)
qed

lemma check_struct_sound_fuel:
  assumes J: "J N" and rest: "rest N" and A: "A N"
      and chk: "check_struct J rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
        sat_hyp_fuel (hyp_of K) A \<Longrightarrow>
        sat_fuel (conc_of K) A"
      and satG: "sat_hyp_fuel (hyp_of J) A"
  shows "sat_fuel (conc_of J) A"
proof -
  have hJ: "hyp_of J N"
    using J by simp
  have fs: "find_struct J (hyp_of J) rest"
    using chk
    by (rule defI[OF check_struct_def[where J=J and rest=rest]])
  have sub: "subset rest rest"
    by (rule subset_refl[OF rest])
  show ?thesis
  proof (rule find_structE[OF J hJ rest rest sub fs])
    fix K
    assume K: "K N"
        and Km: "mem K rest"
        and Kc: "conc_of K = conc_of J"
        and Ksub: "subset (hyp_of K) (hyp_of J)"
    have hK: "hyp_of K N"
      using K by simp
    have satKh: "sat_hyp_fuel (hyp_of K) A"
      by (rule sat_hyp_fuel_subset[OF Ksub hK hJ satG])
    have satK: "sat_fuel (conc_of K) A"
      by (rule prev[OF K Km satKh])
    show "sat_fuel (conc_of J) A"
      using Kc satK
      by (rule eqSubst[where Q="\<lambda>c. sat_fuel c A"])
  qed
qed

lemma sat_fuel_formula_eq_transport:
  assumes f: "f N" and A: "A N" and q: "q N"
      and tg: "tag_F f = F_EQ"
      and sat: "sat_fuel f A"
      and ev: "evals (hyp_of (load_F f)) A q"
  shows "evals (conc_of (load_F f)) A q"
proof -
  have loadN: "load_F f N"
    by (rule load_F_N[OF f])
  have leftN: "hyp_of (load_F f) N"
    by (rule cpx_terminates[OF loadN])
  show ?thesis
  proof (rule sat_fuel_formula_eqE[OF f tg sat])
    fix x y
    assume x: "x N" and y: "y N"
        and left: "evals (hyp_of (load_F f)) A x"
        and right: "evals (conc_of (load_F f)) A y"
        and xy: "x = y"
    have xq: "x = q"
      using left
    proof (rule evalsE)
      fix k
      assume k: "k N"
          and run: "eval_fuel k (hyp_of (load_F f)) A = S x"
      show "x = q"
        by (rule evals_fuel_unique[OF k leftN A ev run])
    qed
    have qx: "q = x"
      by (rule eqSym[OF xq])
    have qy: "q = y"
      using qx xy by (rule eq_trans)
    show "evals (conc_of (load_F f)) A q"
      by (rule eqSubst[
            where a=y and b=q
              and Q="\<lambda>z. evals (conc_of (load_F f)) A z",
            OF eqSym[OF qy] right])
  qed
qed

lemma find_cutE:
  assumes J: "J N" and rest: "rest N" and ptr: "ptr N"
      and sub: "subset ptr rest"
      and fc: "find_cut J rest ptr"
      and H: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   hyp_of K = hyp_of J \<Longrightarrow>
                   mem (conc_of K \<triangleright> hyp_of J \<tturnstile> conc_of J) rest \<Longrightarrow> R"
  shows R
proof -
  have main: "subset ptr rest \<turnstile> (find_cut J rest ptr \<turnstile> R)"
  proof (rule list_induct[OF ptr])
    show "subset Nil rest \<turnstile> (find_cut J rest Nil \<turnstile> R)"
    proof (rule entailsI)
      assume sub0: "subset Nil rest"
      show "find_cut J rest Nil \<turnstile> R"
      proof (rule entailsI)
        assume fc0: "find_cut J rest Nil"
        have C0: "if Nil = Nil then False
                    else if hyp_of (list_hd Nil) = hyp_of J then
                      if mem (conc_of (list_hd Nil) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
                      then True
                      else find_cut J rest (list_tl Nil)
                    else find_cut J rest (list_tl Nil)"
          using fc0
          by (rule defI[OF find_cut_def[where J=J and rest=rest and ptr=Nil]])
        have F: "False"
          using C0 by simp
        show R
          by (rule exF[OF F not_false])
      qed
    qed
  next
    fix h t
    assume h: "h N"
       and t: "t N"
       and IH: "subset t rest \<turnstile> (find_cut J rest t \<turnstile> R)"
    show "subset (Cons h t) rest \<turnstile> (find_cut J rest (Cons h t) \<turnstile> R)"
    proof (rule entailsI)
      assume subht: "subset (Cons h t) rest"
      have hrest: "mem h rest"
        using h t rest subht by (rule subset_cons_headE)
      have subt: "subset t rest"
        using h t rest subht by (rule subset_cons_tailE)
      show "find_cut J rest (Cons h t) \<turnstile> R"
      proof (rule entailsI)
        assume fcht: "find_cut J rest (Cons h t)"
        have C0: "if Cons h t = Nil then False
                    else if hyp_of (list_hd (Cons h t)) = hyp_of J then
                      if mem (conc_of (list_hd (Cons h t)) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
                      then True
                      else find_cut J rest (list_tl (Cons h t))
                    else find_cut J rest (list_tl (Cons h t))"
          using fcht
          by (rule defI[OF find_cut_def[where J=J and rest=rest and ptr="Cons h t"]])
        have C: "if Cons h t = Nil then False
                   else if hyp_of h = hyp_of J then
                     if mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
                     then True
                     else find_cut J rest t
                   else find_cut J rest t"
          using C0
          by (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
        have ne: "\<not> (Cons h t = Nil)"
          using h t by simp
        have C1: "if hyp_of h = hyp_of J then
                    if mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
                    then True
                    else find_cut J rest t
                  else find_cut J rest t"
          using ne C by (rule notcond_thenE)
        have eqB: "(hyp_of h = hyp_of J) B"
          using h J by simp
        show R
        proof (rule cases_bool[where q="hyp_of h = hyp_of J"])
          show "(hyp_of h = hyp_of J) B"
            by (rule eqB)
        next
          assume eq: "hyp_of h = hyp_of J"
          have C2: "if mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
                    then True
                    else find_cut J rest t"
            using eq C1 by (rule cond_thenE)
          have L: "conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J N"
            using h J by simp
          have memB: "mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest B"
            by (rule mem_bool[OF L rest])
          show R
          proof (rule cases_bool[where q="mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest"])
            show "mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest B"
              by (rule memB)
          next
            assume m: "mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest"
            show R
              using h hrest eq m by (rule H)
          next
            assume nm: "\<not> mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest"
            have fct: "find_cut J rest t"
              using nm C2 by (rule notcond_thenE)
            have IR: "find_cut J rest t \<turnstile> R"
              using IH subt by (rule entailsE)
            show R
              using IR fct by (rule entailsE)
          qed
        next
          assume neq: "\<not> (hyp_of h = hyp_of J)"
          have fct: "find_cut J rest t"
            using neq C1 by (rule notcond_thenE)
          have IR: "find_cut J rest t \<turnstile> R"
            using IH subt by (rule entailsE)
          show R
            using IR fct by (rule entailsE)
        qed
      qed
    qed
  qed
  have IR: "find_cut J rest ptr \<turnstile> R"
    using main sub by (rule entailsE)
  show R
    using IR fc by (rule entailsE)
qed

lemma check_cut_sound_fuel:
  assumes J: "J N" and rest: "rest N" and A: "A N"
      and chk: "check_cut J rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
        sat_hyp_fuel (hyp_of K) A \<Longrightarrow>
        sat_fuel (conc_of K) A"
      and satG: "sat_hyp_fuel (hyp_of J) A"
  shows "sat_fuel (conc_of J) A"
proof -
  have fc: "find_cut J rest rest"
    using chk
    by (rule defI[OF check_cut_def[where J=J and rest=rest]])
  have sub: "subset rest rest"
    by (rule subset_refl[OF rest])
  show ?thesis
  proof (rule find_cutE[OF J rest rest sub fc])
    fix K
    assume K: "K N"
        and Km: "mem K rest"
        and Kh: "hyp_of K = hyp_of J"
        and Lm:
          "mem
            (conc_of K \<triangleright> hyp_of J \<tturnstile> conc_of J)
            rest"
    have hKJ: "hyp_of J = hyp_of K"
      by (rule eqSym[OF Kh])
    have satKh: "sat_hyp_fuel (hyp_of K) A"
      using hKJ satG
      by (rule eqSubst[where Q="\<lambda>G. sat_hyp_fuel G A"])
    have satK: "sat_fuel (conc_of K) A"
      by (rule prev[OF K Km satKh])
    have cK: "conc_of K N"
      using K by simp
    have hJ: "hyp_of J N"
      using J by simp
    have satCons:
      "sat_hyp_fuel (conc_of K \<triangleright> hyp_of J) A"
      by (rule sat_hyp_fuel_consI[OF cK hJ satK satG])
    let ?L =
      "conc_of K \<triangleright> hyp_of J \<tturnstile> conc_of J"
    have L: "?L N"
      using K J by simp
    have satLh: "sat_hyp_fuel (hyp_of ?L) A"
      using K J satCons by simp
    have satL: "sat_fuel (conc_of ?L) A"
      by (rule prev[OF L Lm satLh])
    show "sat_fuel (conc_of J) A"
      using K J satL by simp
  qed
qed

lemma find_eqE:
  assumes J: "J N" and rest: "rest N" and ptr: "ptr N"
      and sub: "subset ptr rest"
      and fe: "find_eq J rest ptr"
      and H: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   hyp_of K = hyp_of J \<Longrightarrow>
                   tag_F (conc_of K) = F_EQ \<Longrightarrow>
                   find_phi J
                     (cpx (load_F (conc_of K)))
                     (cpy (load_F (conc_of K))) rest \<Longrightarrow> R"
  shows R
proof -
  have main: "subset ptr rest \<turnstile> (find_eq J rest ptr \<turnstile> R)"
  proof (rule list_induct[OF ptr])
    show "subset Nil rest \<turnstile> (find_eq J rest Nil \<turnstile> R)"
    proof (rule entailsI)
      assume sub0: "subset Nil rest"
      show "find_eq J rest Nil \<turnstile> R"
      proof (rule entailsI)
        assume fe0: "find_eq J rest Nil"
        have C0: "if Nil = Nil then False
                    else if hyp_of (list_hd Nil) = hyp_of J \<and>
                            tag_F (conc_of (list_hd Nil)) = F_EQ then
                      if find_phi J
                           (cpx (load_F (conc_of (list_hd Nil))))
                           (cpy (load_F (conc_of (list_hd Nil)))) rest
                      then True
                      else find_eq J rest (list_tl Nil)
                    else find_eq J rest (list_tl Nil)"
          using fe0
          by (rule defI[OF find_eq_def[where J=J and rest=rest and ptr=Nil]])
        have F: "False"
          using C0 by simp
        show R
          by (rule exF[OF F not_false])
      qed
    qed
  next
    fix h t
    assume h: "h N"
       and t: "t N"
       and IH: "subset t rest \<turnstile> (find_eq J rest t \<turnstile> R)"
    show "subset (Cons h t) rest \<turnstile> (find_eq J rest (Cons h t) \<turnstile> R)"
    proof (rule entailsI)
      assume subht: "subset (Cons h t) rest"
      have hrest: "mem h rest"
        using h t rest subht by (rule subset_cons_headE)
      have subt: "subset t rest"
        using h t rest subht by (rule subset_cons_tailE)
      show "find_eq J rest (Cons h t) \<turnstile> R"
      proof (rule entailsI)
        assume feht: "find_eq J rest (Cons h t)"
        have C0: "if Cons h t = Nil then False
                    else if hyp_of (list_hd (Cons h t)) = hyp_of J \<and>
                            tag_F (conc_of (list_hd (Cons h t))) = F_EQ then
                      if find_phi J
                           (cpx (load_F (conc_of (list_hd (Cons h t)))))
                           (cpy (load_F (conc_of (list_hd (Cons h t))))) rest
                      then True
                      else find_eq J rest (list_tl (Cons h t))
                    else find_eq J rest (list_tl (Cons h t))"
          using feht
          by (rule defI[OF find_eq_def[where J=J and rest=rest and ptr="Cons h t"]])
        have C: "if Cons h t = Nil then False
                   else if hyp_of h = hyp_of J \<and>
                           tag_F (conc_of h) = F_EQ then
                     if find_phi J
                          (cpx (load_F (conc_of h)))
                          (cpy (load_F (conc_of h))) rest
                     then True
                     else find_eq J rest t
                   else find_eq J rest t"
          using C0
          by (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
        have ne: "\<not> (Cons h t = Nil)"
          using h t by simp
        have C1: "if hyp_of h = hyp_of J \<and>
                          tag_F (conc_of h) = F_EQ then
                    if find_phi J
                         (cpx (load_F (conc_of h)))
                         (cpy (load_F (conc_of h))) rest
                    then True
                    else find_eq J rest t
                  else find_eq J rest t"
          using ne C by (rule notcond_thenE)
        have ch: "conc_of h N"
          using h by simp
        have eqhB: "(hyp_of h = hyp_of J) B"
          using h J by simp
        have tgh: "tag_F (conc_of h) N"
          using ch by (rule tag_F_N)
        have feq: "F_EQ N"
          by simp
        have eqtgB: "(tag_F (conc_of h) = F_EQ) B"
          by (rule eqBool[OF tgh feq])
        have bothB: "(hyp_of h = hyp_of J \<and> tag_F (conc_of h) = F_EQ) B"
          using eqhB eqtgB by simp
        show R
        proof (rule cases_bool[where q="hyp_of h = hyp_of J \<and> tag_F (conc_of h) = F_EQ"])
          show "(hyp_of h = hyp_of J \<and> tag_F (conc_of h) = F_EQ) B"
            by (rule bothB)
        next
          assume both: "hyp_of h = hyp_of J \<and> tag_F (conc_of h) = F_EQ"
          have heq: "hyp_of h = hyp_of J"
            using both by (rule conjE1)
          have htg: "tag_F (conc_of h) = F_EQ"
            using both by (rule conjE2)
          have C2: "if find_phi J
                         (cpx (load_F (conc_of h)))
                         (cpy (load_F (conc_of h))) rest
                    then True
                    else find_eq J rest t"
            using both C1 by (rule cond_thenE)
          have lh: "load_F (conc_of h) N"
            using ch by (rule load_F_N)
          have ah: "cpx (load_F (conc_of h)) N"
            using lh by (rule cpx_terminates)
          have bh: "cpy (load_F (conc_of h)) N"
            using lh by (rule cpy_terminates)
          have fpB: "find_phi J
                       (cpx (load_F (conc_of h)))
                       (cpy (load_F (conc_of h))) rest B"
            by (rule find_phi_bool[OF J ah bh rest])
          show R
          proof (rule cases_bool[where q="find_phi J
                      (cpx (load_F (conc_of h)))
                      (cpy (load_F (conc_of h))) rest"])
            show "find_phi J
                    (cpx (load_F (conc_of h)))
                    (cpy (load_F (conc_of h))) rest B"
              by (rule fpB)
          next
            assume fp: "find_phi J
                          (cpx (load_F (conc_of h)))
                          (cpy (load_F (conc_of h))) rest"
            show R
              using h hrest heq htg fp by (rule H)
          next
            assume nfp: "\<not> find_phi J
                           (cpx (load_F (conc_of h)))
                           (cpy (load_F (conc_of h))) rest"
            have fet: "find_eq J rest t"
              using nfp C2 by (rule notcond_thenE)
            have IR: "find_eq J rest t \<turnstile> R"
              using IH subt by (rule entailsE)
            show R
              using IR fet by (rule entailsE)
          qed
        next
          assume nboth: "\<not> (hyp_of h = hyp_of J \<and> tag_F (conc_of h) = F_EQ)"
          have fet: "find_eq J rest t"
            using nboth C1 by (rule notcond_thenE)
          have IR: "find_eq J rest t \<turnstile> R"
            using IH subt by (rule entailsE)
          show R
            using IR fet by (rule entailsE)
        qed
      qed
    qed
  qed
  have IR: "find_eq J rest ptr \<turnstile> R"
    using main sub by (rule entailsE)
  show R
    using IR fe by (rule entailsE)
qed

lemma check_subst_sound_fuel:
  assumes J: "J N" and rest: "rest N" and A: "A N"
      and chk: "check_subst J rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
        sat_hyp_fuel (hyp_of K) A \<Longrightarrow>
        sat_fuel (conc_of K) A"
      and satG: "sat_hyp_fuel (hyp_of J) A"
  shows "sat_fuel (conc_of J) A"
proof -
  have fe: "find_eq J rest rest"
    using chk
    by (rule defI[OF check_subst_def[where J=J and rest=rest]])
  have sub: "subset rest rest"
    by (rule subset_refl[OF rest])
  show ?thesis
  proof (rule find_eqE[OF J rest rest sub fe])
    fix K
    assume K: "K N"
        and Km: "mem K rest"
        and Kh: "hyp_of K = hyp_of J"
        and Ktg: "tag_F (conc_of K) = F_EQ"
        and fp:
          "find_phi J
            (cpx (load_F (conc_of K)))
            (cpy (load_F (conc_of K))) rest"
    let ?a = "cpx (load_F (conc_of K))"
    let ?b = "cpy (load_F (conc_of K))"
    have cK: "conc_of K N"
      using K by simp
    have loadK: "load_F (conc_of K) N"
      by (rule load_F_N[OF cK])
    have aN: "?a N"
      by (rule cpx_terminates[OF loadK])
    have bN: "?b N"
      by (rule cpy_terminates[OF loadK])
    have hKJ: "hyp_of J = hyp_of K"
      by (rule eqSym[OF Kh])
    have satKh: "sat_hyp_fuel (hyp_of K) A"
      using hKJ satG
      by (rule eqSubst[where Q="\<lambda>G. sat_hyp_fuel G A"])
    have satK: "sat_fuel (conc_of K) A"
      by (rule prev[OF K Km satKh])
    have tr:
      "\<And>q. q N \<Longrightarrow> evals ?a A q \<Longrightarrow> evals ?b A q"
    proof -
      fix q
      assume q: "q N" and eva: "evals ?a A q"
      show "evals ?b A q"
        by (rule sat_fuel_formula_eq_transport[
              OF cK A q Ktg satK eva])
    qed
    have subRest: "subset rest rest"
      by (rule subset_refl[OF rest])
    show "sat_fuel (conc_of J) A"
      by (rule find_phi_sound_fuel[
            OF J aN bN rest rest A
              subRest fp prev satG tr])
  qed
qed

lemma evals_zeroI:
  assumes A: "A N"
  shows "evals (pack_T T_ZERO 0) A 0"
proof -
  let ?z = "pack_T T_ZERO 0"
  have tg: "tag_T ?z = T_ZERO"
    by (rule tag_pack_T[OF _ nat0], simp)
  have run: "eval_fuel (S 0) ?z A = S 0"
    by (rule eval_fuel_zero_step[OF nat0 tg])
  show ?thesis
    by (rule evalsI[OF natS[OF nat0] run])
qed

lemma evals_var_putI:
  assumes A: "A N" and i: "i N" and v: "v N"
  shows "evals (pack_T T_VAR i) (asn_put A i v) v"
proof -
  let ?vi = "pack_T T_VAR i"
  let ?A2 = "asn_put A i v"
  have A2: "?A2 N"
    by (rule asn_put_N[OF A i v])
  have tg: "tag_T ?vi = T_VAR"
    by (rule tag_pack_T[OF _ i], simp)
  have ld: "load_T ?vi = i"
    by (rule load_pack_T[OF _ i], simp)
  have key: "nth i ?A2 = v"
    by (rule nth_put_eq[OF A i v])
  have keyLoad: "nth (load_T ?vi) ?A2 = v"
    by (rule eqSubst[
          where a=i and b="load_T ?vi"
            and Q="\<lambda>j. nth j ?A2 = v",
          OF eqSym[OF ld] key])
  have nthN: "nth (load_T ?vi) ?A2 N"
    by (rule eqSubst[
          where a=v and b="nth (load_T ?vi) ?A2"
            and Q="\<lambda>w. w N",
          OF eqSym[OF keyLoad] v])
  have raw:
    "eval_fuel (S 0) ?vi ?A2 =
      S (nth (load_T ?vi) ?A2)"
    by (rule eval_fuel_var[OF nat0 tg nthN])
  have value: "eval_fuel (S 0) ?vi ?A2 = S v"
    using raw sucCong[OF keyLoad] by (rule eq_trans)
  show ?thesis
    by (rule evalsI[OF natS[OF nat0] value])
qed

lemma sat_fuel_reflI:
  assumes a: "a N" and A: "A N" and r: "r N"
      and ev: "evals a A r"
  shows "sat_fuel (pack_F F_EQ \<langle>a, a\<rangle>) A"
proof -
  let ?args = "\<langle>a, a\<rangle>"
  let ?f = "pack_F F_EQ ?args"
  have argsN: "?args N"
    using a by simp
  have feqN: "F_EQ N"
    by simp
  have tg: "tag_F ?f = F_EQ"
    by (rule tag_pack_F[OF feqN argsN])
  have ld: "load_F ?f = ?args"
    by (rule load_pack_F[OF feqN argsN])
  have leftArg: "hyp_of ?args = a"
    by (rule cpx_proj[OF a a])
  have rightArg: "conc_of ?args = a"
    by (rule cpy_proj[OF a a])
  have leftSel: "hyp_of (load_F ?f) = a"
    by (rule eqSubst[
          where a="?args" and b="load_F ?f"
            and Q="\<lambda>z. hyp_of z = a",
          OF eqSym[OF ld] leftArg])
  have rightSel: "conc_of (load_F ?f) = a"
    by (rule eqSubst[
          where a="?args" and b="load_F ?f"
            and Q="\<lambda>z. conc_of z = a",
          OF eqSym[OF ld] rightArg])
  have left: "evals (hyp_of (load_F ?f)) A r"
    by (rule eqSubst[
          where a=a and b="hyp_of (load_F ?f)"
            and Q="\<lambda>z. evals z A r",
          OF eqSym[OF leftSel] ev])
  have right: "evals (conc_of (load_F ?f)) A r"
    by (rule eqSubst[
          where a=a and b="conc_of (load_F ?f)"
            and Q="\<lambda>z. evals z A r",
          OF eqSym[OF rightSel] ev])
  have relation:
    "if tag_F ?f = F_EQ then r = r else r \<noteq> r"
    using tg r by simp
  show ?thesis
    unfolding sat_fuel_def
    apply (rule existsI[where a=r])
    apply (rule r)
    apply (rule existsI[where a=r])
    apply (rule r)
    apply (rule conjI)
    apply (rule left)
    apply (rule conjI)
    apply (rule right)
    apply (rule relation)
    done
qed

lemma nat_ind_sound_put_fuel:
  assumes p: "p N" and i: "i N" and a: "a N"
      and G: "G N" and A: "A N" and n: "n N"
      and fresh: "fresh_H i G"
      and satG: "sat_hyp_fuel G A"
      and base: "sat_fuel (subst_F p i (pack_T T_ZERO 0)) A"
      and step:
        "\<And>m. m N \<Longrightarrow>
          sat_hyp_fuel
            (pack_F F_EQ
               \<langle>pack_T T_VAR i, pack_T T_VAR i\<rangle>
               \<triangleright> p \<triangleright> G)
            (asn_put A i m) \<Longrightarrow>
          sat_fuel
            (subst_F p i
              (pack_T T_SUC (pack_T T_VAR i)))
            (asn_put A i m)"
      and eva: "evals a A n"
  shows "sat_fuel (subst_F p i a) A"
proof -
  let ?z = "pack_T T_ZERO 0"
  let ?vi = "pack_T T_VAR i"
  let ?svi = "pack_T T_SUC ?vi"
  let ?eqvi = "pack_F F_EQ \<langle>?vi, ?vi\<rangle>"
  have zN: "?z N"
    by (rule pack_T_N[OF _ nat0], simp)
  have viN: "?vi N"
    by (rule pack_T_N[OF _ i], simp)
  have sviN: "?svi N"
    by (rule pack_T_N[OF _ viN], simp)
  have vvN: "\<langle>?vi, ?vi\<rangle> N"
    using viN by simp
  have eqviN: "?eqvi N"
    by (rule pack_F_N[OF _ vvN], simp)
  have pGN: "p \<triangleright> G N"
    using p G by simp
  have main: "\<And>m. m N \<Longrightarrow> sat_fuel p (asn_put A i m)"
  proof -
    fix m
    assume m: "m N"
    show "sat_fuel p (asn_put A i m)"
    proof (rule ind[OF m])
      have evz: "evals ?z A 0"
        by (rule evals_zeroI[OF A])
      show "sat_fuel p (asn_put A i 0)"
        by (rule sat_fuel_subst_FD[
              OF p i zN A nat0 evz base])
    next
      fix k
      assume k: "k N"
          and IH: "sat_fuel p (asn_put A i k)"
      let ?Ak = "asn_put A i k"
      have Ak: "?Ak N"
        by (rule asn_put_N[OF A i k])
      have Gk: "sat_hyp_fuel G ?Ak"
        apply (rule sat_hyp_fuel_put[OF G i A k fresh satG])
        done
      have evvi: "evals ?vi ?Ak k"
        by (rule evals_var_putI[OF A i k])
      have satvi: "sat_fuel ?eqvi ?Ak"
        by (rule sat_fuel_reflI[OF viN Ak k evvi])
      have pG: "sat_hyp_fuel (p \<triangleright> G) ?Ak"
        by (rule sat_hyp_fuel_consI[
              OF p G IH Gk])
      have stepG:
        "sat_hyp_fuel (?eqvi \<triangleright> p \<triangleright> G) ?Ak"
        by (rule sat_hyp_fuel_consI[
              OF eqviN pGN satvi pG])
      have stepSat:
        "sat_fuel (subst_F p i ?svi) ?Ak"
        by (rule step[OF k stepG])
      have evsvi: "evals ?svi ?Ak (S k)"
        by (rule evals_sucI[
              OF viN Ak k evvi])
      have Sk: "S k N"
        by (rule natS[OF k])
      have next0:
        "sat_fuel p (asn_put ?Ak i (S k))"
        by (rule sat_fuel_subst_FD[
              OF p i sviN Ak Sk evsvi stepSat])
      have overwrite:
        "asn_put ?Ak i (S k) = asn_put A i (S k)"
        by (rule asn_put_overwrite[OF A i k Sk])
      show "sat_fuel p (asn_put A i (S k))"
        using overwrite next0
        by (rule eqSubst[
              where Q="\<lambda>C. sat_fuel p C"])
    qed
  qed
  have pn: "sat_fuel p (asn_put A i n)"
    by (rule main[OF n])
  show ?thesis
    by (rule sat_fuel_subst_FI[
          OF p i a A n eva pn])
qed

lemma ind_jdg_N:
  assumes p: "p N" and G: "G N" and i: "i N"
  shows "pack_F F_EQ \<langle>pack_T T_VAR i, pack_T T_VAR i\<rangle> \<triangleright> p \<triangleright> G \<tturnstile>
         subst_F p i (pack_T T_SUC (pack_T T_VAR i)) N"
proof -
  have vi: "pack_T T_VAR i N" 
    by (rule pack_T_N[OF _ i], simp)
  have vv: "\<langle>pack_T T_VAR i, pack_T T_VAR i\<rangle> N" 
    using vi by simp
  have feq: "pack_F F_EQ \<langle>pack_T T_VAR i, pack_T T_VAR i\<rangle> N" 
    by (rule pack_F_N[OF _ vv], simp)
  have sv: "pack_T T_SUC (pack_T T_VAR i) N" 
    by (rule pack_T_N[OF _ vi], simp)
  have cc: "subst_F p i (pack_T T_SUC (pack_T T_VAR i)) N" 
    by (rule subst_F_N[OF p i sv])
  show ?thesis 
    using feq p G cc by simp
qed

lemma check_ind_template_bool [auto]:
  assumes f: "f N" and phi: "phi N" and a: "a N" and G: "G N"
      and p: "p N" and i: "i N" and r: "rest N"
  shows "check_ind_template f phi a G p i rest B"
proof (rule ind[OF p])
  have ztz: "pack_T T_ZERO 0 N" 
    by (rule pack_T_N[OF _ nat0], simp)
  show "check_ind_template f phi a G 0 i rest B"
    apply (rule defE[OF check_ind_template_def[where p=0]], insert f phi a G i r)
    apply simp
    apply (rule condTB[OF _ true_bool false_bool])
    using subst_F_N[OF nat0 i a] subst_F_N[OF nat0 i ztz] f phi ind_jdg_N[OF nat0 G i] r
    by auto
next
  fix k assume k: "k N" and IH: "check_ind_template f phi a G k i rest B"
  have ztz: "pack_T T_ZERO 0 N" 
    by (rule pack_T_N[OF _ nat0], simp)
  have skN: "S k N" 
    by (rule natS[OF k])
  have oneN: "(1::num) N" 
    by simp
  have grN: "(S k > 0) N"
    by (unfold greater_def, rule sub_terminates[OF oneN leq_terminates[OF skN nat0]])
  have g2B: "(S k > 0 = 1) B" 
    by (rule eqBool[OF grN oneN])
  have sk1: "S k - 1 = k" 
    using k by simp
  have RECB: "check_ind_template f phi a G (S k - 1) i rest B" 
    using IH sk1 by simp
  have innerB: "(if S k > 0 = 1 then check_ind_template f phi a G (S k - 1) i rest else False) B"
    by (rule condTB[OF g2B RECB false_bool])
  show "check_ind_template f phi a G (S k) i rest B"
    apply (rule defE[OF check_ind_template_def[where p="S k"]])
    apply (rule condTB[OF _ true_bool innerB])
    using subst_F_N[OF skN i a] subst_F_N[OF skN i ztz] f phi ind_jdg_N[OF skN G i] r
    by auto
qed

lemma find_ind_baseE:
  assumes J: "J N" and a: "a N"
      and rest: "rest N" and ptr: "ptr N"
      and sub: "subset ptr rest"
      and fib: "find_ind_base J a rest ptr"
      and H:
        "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
          hyp_of K = hyp_of J \<Longrightarrow>
          check_ind_template
            (conc_of J) (conc_of K) a (hyp_of J)
            (rep_vars_F (conc_of J) (J + 1))
            (J + 1) rest \<Longrightarrow> R"
  shows R
proof -
  have main:
    "subset ptr rest \<turnstile> (find_ind_base J a rest ptr \<turnstile> R)"
  proof (rule list_induct[OF ptr])
    show
      "subset Nil rest \<turnstile>
       (find_ind_base J a rest Nil \<turnstile> R)"
    proof (rule entailsI)
      assume sub0: "subset Nil rest"
      show "find_ind_base J a rest Nil \<turnstile> R"
      proof (rule entailsI)
        assume fib0: "find_ind_base J a rest Nil"
        have C0:
          "if Nil = Nil then False
           else if hyp_of (list_hd Nil) = hyp_of J then
             if check_ind_template
                  (conc_of J) (conc_of (list_hd Nil))
                  a (hyp_of J)
                  (rep_vars_F (conc_of J) (J + 1))
                  (J + 1) rest
             then True
             else find_ind_base J a rest (list_tl Nil)
           else find_ind_base J a rest (list_tl Nil)"
          using fib0
          by (rule defI[OF find_ind_base_def[
            where J=J and a=a and rest=rest and ptr=Nil]])
        have F: "False"
          using C0 by simp
        show R
          by (rule exF[OF F not_false])
      qed
    qed
  next
    fix h t
    assume h: "h N"
       and t: "t N"
       and IH:
         "subset t rest \<turnstile>
          (find_ind_base J a rest t \<turnstile> R)"
    show
      "subset (Cons h t) rest \<turnstile>
       (find_ind_base J a rest (Cons h t) \<turnstile> R)"
    proof (rule entailsI)
      assume subht: "subset (Cons h t) rest"
      have hrest: "mem h rest"
        using h t rest subht by (rule subset_cons_headE)
      have subt: "subset t rest"
        using h t rest subht by (rule subset_cons_tailE)
      show "find_ind_base J a rest (Cons h t) \<turnstile> R"
      proof (rule entailsI)
        assume fibht:
          "find_ind_base J a rest (Cons h t)"
        have C0:
          "if Cons h t = Nil then False
           else if
             hyp_of (list_hd (Cons h t)) = hyp_of J
           then
             if check_ind_template (conc_of J) (conc_of (list_hd (Cons h t)))
                  a (hyp_of J) (rep_vars_F (conc_of J) (J + 1)) (J + 1) rest
             then True
             else find_ind_base J a rest (list_tl (Cons h t))
           else find_ind_base J a rest
                  (list_tl (Cons h t))"
          using fibht
          by (rule defI[OF find_ind_base_def[
            where J=J and a=a and rest=rest
              and ptr="Cons h t"]])
        have C:
          "if Cons h t = Nil then False
           else if hyp_of h = hyp_of J then
             if check_ind_template
                  (conc_of J) (conc_of h) a (hyp_of J)
                  (rep_vars_F (conc_of J) (J + 1))
                  (J + 1) rest
             then True
             else find_ind_base J a rest t
           else find_ind_base J a rest t"
          using C0
          by (simp only:
            list_hd_cons[OF h t] list_tl_cons[OF h t])
        have ne: "\<not> Cons h t = Nil"
          using h t by simp
        have C1:
          "if hyp_of h = hyp_of J then
             if check_ind_template
                  (conc_of J) (conc_of h) a (hyp_of J)
                  (rep_vars_F (conc_of J) (J + 1))
                  (J + 1) rest
             then True
             else find_ind_base J a rest t
           else find_ind_base J a rest t"
          using ne C by (rule notcond_thenE)
        have cJ: "conc_of J N"
          using J by simp
        have ch: "conc_of h N"
          using h by simp
        have hJ: "hyp_of J N"
          using J by simp
        have i: "J + 1 N"
          using J by simp
        have p:
          "rep_vars_F (conc_of J) (J + 1) N"
          by (rule rep_vars_F_N[OF cJ i])
        have eqB: "(hyp_of h = hyp_of J) B"
          using h J by simp
        have ctB:
          "check_ind_template
            (conc_of J) (conc_of h) a (hyp_of J)
            (rep_vars_F (conc_of J) (J + 1))
            (J + 1) rest B"
          by (rule check_ind_template_bool[
            OF cJ ch a hJ p i rest])
        show R
        proof (rule cases_bool[
          where q="hyp_of h = hyp_of J"])
          show "(hyp_of h = hyp_of J) B"
            by (rule eqB)
        next
          assume heq: "hyp_of h = hyp_of J"
          have C2:
            "if check_ind_template
                 (conc_of J) (conc_of h) a (hyp_of J)
                 (rep_vars_F (conc_of J) (J + 1))
                 (J + 1) rest
             then True
             else find_ind_base J a rest t"
            using heq C1 by (rule cond_thenE)
          show R
          proof (rule cases_bool[
            where q="check_ind_template
              (conc_of J) (conc_of h) a (hyp_of J)
              (rep_vars_F (conc_of J) (J + 1))
              (J + 1) rest"])
            show
              "check_ind_template
                (conc_of J) (conc_of h) a (hyp_of J)
                (rep_vars_F (conc_of J) (J + 1))
                (J + 1) rest B"
              by (rule ctB)
          next
            assume ct:
              "check_ind_template
                (conc_of J) (conc_of h) a (hyp_of J)
                (rep_vars_F (conc_of J) (J + 1))
                (J + 1) rest"
            show R
              using h hrest heq ct by (rule H)
          next
            assume nct:
              "\<not> check_ind_template
                   (conc_of J) (conc_of h) a (hyp_of J)
                   (rep_vars_F (conc_of J) (J + 1))
                   (J + 1) rest"
            have fibt: "find_ind_base J a rest t"
              using nct C2 by (rule notcond_thenE)
            have IR: "find_ind_base J a rest t \<turnstile> R"
              using IH subt by (rule entailsE)
            show R
              using IR fibt by (rule entailsE)
          qed
        next
          assume nheq: "\<not> hyp_of h = hyp_of J"
          have fibt: "find_ind_base J a rest t"
            using nheq C1 by (rule notcond_thenE)
          have IR: "find_ind_base J a rest t \<turnstile> R"
            using IH subt by (rule entailsE)
          show R
            using IR fibt by (rule entailsE)
        qed
      qed
    qed
  qed
  have IR: "find_ind_base J a rest ptr \<turnstile> R"
    using main sub by (rule entailsE)
  show R
    using IR fib by (rule entailsE)
qed

lemma check_ind_templateE:
  assumes f: "f N" and phi: "phi N"
      and a: "a N" and G: "G N"
      and p: "p N" and i: "i N"
      and rest: "rest N"
      and chk: "check_ind_template f phi a G p i rest"
      and H: "\<And>q. q N \<Longrightarrow> subst_F q i a = f \<Longrightarrow> subst_F q i (pack_T T_ZERO 0) = phi \<Longrightarrow>
          mem (pack_F F_EQ \<langle>pack_T T_VAR i, pack_T T_VAR i\<rangle> \<triangleright> q \<triangleright> G \<tturnstile> subst_F q i (pack_T T_SUC (pack_T T_VAR i))) rest \<Longrightarrow> R"
  shows R
proof -
  let ?z = "pack_T T_ZERO 0"
  let ?vi = "pack_T T_VAR i"
  let ?svi = "pack_T T_SUC ?vi"
  have zN: "?z N"
    by (rule pack_T_N[OF _ nat0], simp)
  have main:
    "check_ind_template f phi a G p i rest \<turnstile> R"
  proof (rule ind[OF p])
    show "check_ind_template f phi a G 0 i rest \<turnstile> R"
    proof (rule entailsI)
      assume chk0: "check_ind_template f phi a G 0 i rest"
      have C0:
        "if subst_F 0 i a = f \<and>subst_F 0 i ?z = phi \<and>
            mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G \<tturnstile> subst_F 0 i ?svi) rest
         then True
         else if 0 > 0 = 1
         then check_ind_template f phi a G (0 - 1) i rest
         else False"
        using chk0
        by (rule defI[OF check_ind_template_def[
          where f=f and phi=phi and a=a and G=G
            and p=0 and i=i and rest=rest]])
      have C: "if subst_F 0 i a = f \<and> subst_F 0 i ?z = phi \<and> mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G \<tturnstile> subst_F 0 i ?svi) rest
         then True
         else False"
        using C0 by simp
      have sa: "subst_F 0 i a N"
        by (rule subst_F_N[OF nat0 i a])
      have sz: "subst_F 0 i ?z N"
        by (rule subst_F_N[OF nat0 i zN])
      have sj:
        "(pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G \<tturnstile> subst_F 0 i ?svi) N"
        by (rule ind_jdg_N[OF nat0 G i])
      have eaB: "(subst_F 0 i a = f) B"
        by (rule eqBool[OF sa f])
      have ezB: "(subst_F 0 i ?z = phi) B"
        by (rule eqBool[OF sz phi])
      have emB:
        "mem
          (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G
           \<tturnstile> subst_F 0 i ?svi)
          rest B"
        by (rule mem_bool[OF sj rest])
      have allB:
        "(subst_F 0 i a = f \<and>
          subst_F 0 i ?z = phi \<and>
          mem
            (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G
             \<tturnstile> subst_F 0 i ?svi)
            rest) B"
        using eaB ezB emB by auto
      show R
      proof (rule cases_bool[
        where q="subst_F 0 i a = f \<and>
          subst_F 0 i ?z = phi \<and>
          mem
            (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G
             \<tturnstile> subst_F 0 i ?svi)
            rest"])
        show
          "(subst_F 0 i a = f \<and>
            subst_F 0 i ?z = phi \<and>
            mem
              (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G
               \<tturnstile> subst_F 0 i ?svi)
              rest) B"
          by (rule allB)
      next
        assume all:
          "subst_F 0 i a = f \<and>
           subst_F 0 i ?z = phi \<and>
           mem
             (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G
              \<tturnstile> subst_F 0 i ?svi)
             rest"
                have left:
          "subst_F 0 i a = f \<and>
           subst_F 0 i ?z = phi"
          using all by (rule conjE1)
        have qa: "subst_F 0 i a = f"
          using left by (rule conjE1)
        have qz: "subst_F 0 i ?z = phi"
          using left by (rule conjE2)
        have qm:
          "mem
            (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G
             \<tturnstile> subst_F 0 i ?svi)
            rest"
          using all by (rule conjE2)
        show R
          using nat0 qa qz qm by (rule H)
      next
        assume nall: "\<not>(subst_F 0 i a = f \<and> subst_F 0 i ?z = phi \<and> mem
               (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> 0 \<triangleright> G
                \<tturnstile> subst_F 0 i ?svi)
               rest)"
        have F: "False"
          using nall C by (rule notcond_thenE)
        show R
          by (rule exF[OF F not_false])
      qed
    qed
  next
    fix k
    assume k: "k N"
       and IH: "check_ind_template f phi a G k i rest \<turnstile> R"
    show "check_ind_template f phi a G (S k) i rest \<turnstile> R"
    proof (rule entailsI)
      assume chks:
        "check_ind_template f phi a G (S k) i rest"
      have C0:
        "if subst_F (S k) i a = f \<and>
            subst_F (S k) i ?z = phi \<and>
            mem
              (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G
               \<tturnstile> subst_F (S k) i ?svi)
              rest
         then True
         else if S k > 0 = 1
         then check_ind_template
                f phi a G (S k - 1) i rest
         else False"
        using chks
        by (rule defI[OF check_ind_template_def[
          where f=f and phi=phi and a=a and G=G
            and p="S k" and i=i and rest=rest]])
      have sk: "S k N"
        using k by simp
      have gt: "S k > 0 = 1"
        using k by simp
      have sk1: "S k - 1 = k"
        using k by simp
      have sa: "subst_F (S k) i a N"
        by (rule subst_F_N[OF sk i a])
      have sz: "subst_F (S k) i ?z N"
        by (rule subst_F_N[OF sk i zN])
      have sj:
        "(pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G
          \<tturnstile> subst_F (S k) i ?svi) N"
        by (rule ind_jdg_N[OF sk G i])
      have eaB: "(subst_F (S k) i a = f) B"
        by (rule eqBool[OF sa f])
      have ezB: "(subst_F (S k) i ?z = phi) B"
        by (rule eqBool[OF sz phi])
      have emB: "mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G \<tturnstile> subst_F (S k) i ?svi) rest B"
        by (rule mem_bool[OF sj rest])
      have allB: "(subst_F (S k) i a = f \<and> subst_F (S k) i ?z = phi \<and> mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G \<tturnstile> subst_F (S k) i ?svi) rest) B"
        using eaB ezB emB by auto
      show R
      proof (rule cases_bool[
        where q="subst_F (S k) i a = f \<and>
          subst_F (S k) i ?z = phi \<and>
          mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G \<tturnstile> subst_F (S k) i ?svi) rest"])
        show
          "(subst_F (S k) i a = f \<and>
            subst_F (S k) i ?z = phi \<and>
            mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G \<tturnstile> subst_F (S k) i ?svi) rest) B"
          by (rule allB)
      next
        assume all:
          "subst_F (S k) i a = f \<and>
           subst_F (S k) i ?z = phi \<and>
           mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G \<tturnstile> subst_F (S k) i ?svi) rest"
        have left:
          "subst_F (S k) i a = f \<and>
           subst_F (S k) i ?z = phi"
          using all by (rule conjE1)
        have qa: "subst_F (S k) i a = f"
          using left by (rule conjE1)
        have qz: "subst_F (S k) i ?z = phi"
          using left by (rule conjE2)
        have qm:
          "mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G \<tturnstile> subst_F (S k) i ?svi) rest"
          using all by (rule conjE2)
        show R
          using sk qa qz qm by (rule H)
      next
        assume nall:
          "\<not>(subst_F (S k) i a = f \<and> subst_F (S k) i ?z = phi \<and> mem (pack_F F_EQ \<langle>?vi, ?vi\<rangle> \<triangleright> S k \<triangleright> G \<tturnstile> subst_F (S k) i ?svi) rest)"
        have C1:
          "if S k > 0 = 1
           then check_ind_template
                  f phi a G (S k - 1) i rest
           else False"
          using nall C0 by (rule notcond_thenE)
        have chkp:
          "check_ind_template f phi a G (S k - 1) i rest"
          using gt C1 by (rule cond_thenE)
        have chkk:
          "check_ind_template f phi a G k i rest"
          using sk1 chkp
          by (rule eqSubst[
            where Q="\<lambda>q. check_ind_template f phi a G q i rest"])
        show R
          using IH chkk by (rule entailsE)
      qed
    qed
  qed
  show R
    using main chk by (rule entailsE)
qed

lemma check_ind_sound_fuel:
  assumes J: "J N" and rest: "rest N" and A: "A N"
      and chk: "check_ind J rest"
      and prev:
        "\<And>K A2. A2 N \<Longrightarrow> K N \<Longrightarrow> mem K rest \<Longrightarrow>
          sat_hyp_fuel (hyp_of K) A2 \<Longrightarrow>
          sat_fuel (conc_of K) A2"
      and satG: "sat_hyp_fuel (hyp_of J) A"
  shows "sat_fuel (conc_of J) A"
proof -
  let ?f = "conc_of J"
  let ?G = "hyp_of J"
  let ?a = "cpx (load_F ?f)"
  let ?i = "J + 1"
  let ?p = "rep_vars_F ?f ?i"
  let ?z = "pack_T T_ZERO 0"
  let ?vi = "pack_T T_VAR ?i"
  let ?svi = "pack_T T_SUC ?vi"
  let ?eqaa = "pack_F F_EQ \<langle>?a, ?a\<rangle>"
  let ?Qa = "?G \<tturnstile> ?eqaa"
  have f: "?f N"
    using J by simp
  have G: "?G N"
    using J by simp
  have lf: "load_F ?f N"
    by (rule load_F_N[OF f])
  have a: "?a N"
    by (rule cpx_terminates[OF lf])
  have i: "?i N"
    using J by simp
  have p: "?p N"
    by (rule rep_vars_F_N[OF f i])
  have z: "?z N"
    by (rule pack_T_N[OF _ nat0], simp)
  have vi: "?vi N"
    by (rule pack_T_N[OF _ i], simp)
  have svi: "?svi N"
    by (rule pack_T_N[OF _ vi], simp)
  have aa: "\<langle>?a, ?a\<rangle> N"
    using a by simp
  have eqaa: "?eqaa N"
    by (rule pack_F_N[OF _ aa], simp)
  have Qa: "?Qa N"
    using G eqaa by simp
  have freshB: "fresh_H ?i ?G B"
    by (rule fresh_H_bool[OF i G])
  have memB: "mem ?Qa rest B"
    by (rule mem_bool[OF Qa rest])
  have guardB: "(fresh_H ?i ?G \<and> mem ?Qa rest) B"
    using freshB memB by auto
  have C:
    "if fresh_H ?i ?G \<and> mem ?Qa rest
     then find_ind_base J ?a rest rest
     else False"
    using chk
    by (rule defI[OF check_ind_def[
          where J=J and rest=rest]])
  have guard: "fresh_H ?i ?G \<and> mem ?Qa rest"
  proof (rule cases_bool[
      where q="fresh_H ?i ?G \<and> mem ?Qa rest"])
    show "(fresh_H ?i ?G \<and> mem ?Qa rest) B"
      by (rule guardB)
  next
    assume guard: "fresh_H ?i ?G \<and> mem ?Qa rest"
    show "fresh_H ?i ?G \<and> mem ?Qa rest"
      by (rule guard)
  next
    assume nguard: "\<not> (fresh_H ?i ?G \<and> mem ?Qa rest)"
    have bot: "False"
      using nguard C by (rule notcond_thenE)
    show "fresh_H ?i ?G \<and> mem ?Qa rest"
      by (rule exF[OF bot not_false])
  qed
  have fresh: "fresh_H ?i ?G"
    by (rule conjE1[OF guard])
  have mQa: "mem ?Qa rest"
    by (rule conjE2[OF guard])
  have fib: "find_ind_base J ?a rest rest"
    using guard C by (rule cond_thenE)
  have QaG: "sat_hyp_fuel (hyp_of ?Qa) A"
    using G eqaa satG by simp
  have satQa0: "sat_fuel (conc_of ?Qa) A"
    by (rule prev[OF A Qa mQa QaG])
  have satQa: "sat_fuel ?eqaa A"
    using G eqaa satQa0 by simp
  show "sat_fuel ?f A"
  proof (rule sat_fuel_reflE[OF a satQa])
    fix n
    assume n: "n N" and eva: "evals ?a A n"
    have sub: "subset rest rest"
      by (rule subset_refl[OF rest])
    show "sat_fuel ?f A"
    proof (rule find_ind_baseE[
        OF J a rest rest sub fib])
      fix K
      assume K: "K N"
          and Km: "mem K rest"
          and Kh: "hyp_of K = ?G"
          and ct:
            "check_ind_template
              ?f (conc_of K) ?a ?G ?p ?i rest"
      have cK: "conc_of K N"
        using K by simp
      have hK: "?G = hyp_of K"
        by (rule eqSym[OF Kh])
      have satKh: "sat_hyp_fuel (hyp_of K) A"
        using hK satG
        by (rule eqSubst[
              where Q="\<lambda>H. sat_hyp_fuel H A"])
      have satK: "sat_fuel (conc_of K) A"
        by (rule prev[OF A K Km satKh])
      show "sat_fuel ?f A"
      proof (rule check_ind_templateE[
          OF f cK a G p i rest ct])
        fix q
        assume q: "q N"
            and qa: "subst_F q ?i ?a = ?f"
            and qz: "subst_F q ?i ?z = conc_of K"
            and qm:
              "mem
                (pack_F F_EQ \<langle>?vi, ?vi\<rangle>
                   \<triangleright> q \<triangleright> ?G
                 \<tturnstile> subst_F q ?i ?svi)
                rest"
        have base: "sat_fuel (subst_F q ?i ?z) A"
          using eqSym[OF qz] satK
          by (rule eqSubst[
                where Q="\<lambda>f. sat_fuel f A"])
        have step:
          "\<And>m. m N \<Longrightarrow>
            sat_hyp_fuel
              (pack_F F_EQ \<langle>?vi, ?vi\<rangle>
                 \<triangleright> q \<triangleright> ?G)
              (asn_put A ?i m) \<Longrightarrow>
            sat_fuel
              (subst_F q ?i ?svi)
              (asn_put A ?i m)"
        proof -
          fix m
          assume m: "m N"
              and satStep:
                "sat_hyp_fuel
                  (pack_F F_EQ \<langle>?vi, ?vi\<rangle>
                     \<triangleright> q \<triangleright> ?G)
                  (asn_put A ?i m)"
          let ?H =
            "pack_F F_EQ \<langle>?vi, ?vi\<rangle>
               \<triangleright> q \<triangleright> ?G"
          let ?C = "subst_F q ?i ?svi"
          let ?Kstep = "?H \<tturnstile> ?C"
          let ?Am = "asn_put A ?i m"
          have eqviArgs: "\<langle>?vi, ?vi\<rangle> N"
            using vi by simp
          have eqvi: "pack_F F_EQ \<langle>?vi, ?vi\<rangle> N"
            by (rule pack_F_N[OF _ eqviArgs], simp)
          have qG: "q \<triangleright> ?G N"
            using q G by simp
          have H: "?H N"
            using eqvi qG by simp
          have Cn: "?C N"
            by (rule subst_F_N[OF q i svi])
          have Kstep: "?Kstep N"
            using H Cn by simp
          have Am: "?Am N"
            by (rule asn_put_N[OF A i m])
          have hp: "hyp_of ?Kstep = ?H"
            by (rule cpx_proj[OF H Cn])
          have satKstepH: "sat_hyp_fuel (hyp_of ?Kstep) ?Am"
            using eqSym[OF hp] satStep
            by (rule eqSubst[
                  where Q="\<lambda>H. sat_hyp_fuel H ?Am"])
          have satKstep: "sat_fuel (conc_of ?Kstep) ?Am"
            by (rule prev[OF Am Kstep qm satKstepH])
          have cp: "conc_of ?Kstep = ?C"
            by (rule cpy_proj[OF H Cn])
          show "sat_fuel ?C ?Am"
            using cp satKstep
            by (rule eqSubst[
                  where Q="\<lambda>f. sat_fuel f ?Am"])
        qed
        have sq: "sat_fuel (subst_F q ?i ?a) A"
          by (rule nat_ind_sound_put_fuel[
                OF q i a G A n fresh satG base step eva])
        show "sat_fuel ?f A"
          using qa sq
          by (rule eqSubst[
                where Q="\<lambda>f. sat_fuel f A"])
      qed
    qed
  qed
qed

lemma sat_fuel_formula_eqI:
  assumes f: "f N" and A: "A N" and q: "q N"
      and tg: "tag_F f = F_EQ"
      and left: "evals (cpx (load_F f)) A q"
      and right: "evals (cpy (load_F f)) A q"
  shows "sat_fuel f A"
proof -
  have relation:
    "if tag_F f = F_EQ then q = q else q \<noteq> q"
    using tg q by simp
  show ?thesis
    unfolding sat_fuel_def
    apply (rule existsI[where a=q])
    apply (rule q)
    apply (rule existsI[where a=q])
    apply (rule q)
    apply (rule conjI)
    apply (rule left)
    apply (rule conjI)
    apply (rule right)
    apply (rule relation)
    done
qed

lemma sat_fuel_formula_neqI:
  assumes f: "f N" and A: "A N"
      and x: "x N" and y: "y N"
      and tg: "\<not> tag_F f = F_EQ"
      and left: "evals (cpx (load_F f)) A x"
      and right: "evals (cpy (load_F f)) A y"
      and neq: "x \<noteq> y"
  shows "sat_fuel f A"
proof -
  have relation:
    "if tag_F f = F_EQ then x = y else x \<noteq> y"
    using x y tg neq by simp
  show ?thesis
    unfolding sat_fuel_def
    apply (rule existsI[where a=x])
    apply (rule x)
    apply (rule existsI[where a=y])
    apply (rule y)
    apply (rule conjI)
    apply (rule left)
    apply (rule conjI)
    apply (rule right)
    apply (rule relation)
    done
qed

lemma eq_prem_fuel:
  assumes hJ: "hyp_of J N" and rest: "rest N"
      and a: "a N" and b: "b N" and A: "A N"
      and m: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>a, b\<rangle>) rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
        sat_hyp_fuel (hyp_of K) A \<Longrightarrow>
        sat_fuel (conc_of K) A"
      and satG: "sat_hyp_fuel (hyp_of J) A"
  obtains q where "q N" and "evals a A q" and "evals b A q"
proof -
  let ?f = "pack_F F_EQ \<langle>a, b\<rangle>"
  let ?K = "hyp_of J \<tturnstile> ?f"
  have ab: "\<langle>a, b\<rangle> N"
    using a b by simp
  have f: "?f N"
    by (rule pack_F_N[OF _ ab], simp)
  have K: "?K N"
    using hJ f by simp
  have hK: "hyp_of ?K = hyp_of J"
    by (rule cpx_proj[OF hJ f])
  have cK: "conc_of ?K = ?f"
    by (rule cpy_proj[OF hJ f])
  have satKh: "sat_hyp_fuel (hyp_of ?K) A"
    using eqSym[OF hK] satG
    by (rule eqSubst[
          where Q="\<lambda>G. sat_hyp_fuel G A"])
  have satK: "sat_fuel (conc_of ?K) A"
    by (rule prev[OF K m satKh])
  have sat: "sat_fuel ?f A"
    using cK satK
    by (rule eqSubst[
          where Q="\<lambda>p. sat_fuel p A"])
  have tg: "tag_F ?f = F_EQ"
    by (rule tag_pack_F[OF _ ab], simp)
  have ld: "load_F ?f = \<langle>a, b\<rangle>"
    by (rule load_pack_F[OF _ ab], simp)
  show thesis
  proof (rule sat_fuel_formula_eqE[OF f tg sat])
    fix x y
    assume x: "x N" and y: "y N"
        and left: "evals (cpx (load_F ?f)) A x"
        and right: "evals (cpy (load_F ?f)) A y"
        and xy: "x = y"
    have px: "cpx (load_F ?f) = a"
      using eqSym[OF ld] cpx_proj[OF a b]
      by (rule eqSubst[
            where Q="\<lambda>z. cpx z = a"])
    have py: "cpy (load_F ?f) = b"
      using eqSym[OF ld] cpy_proj[OF a b]
      by (rule eqSubst[
            where Q="\<lambda>z. cpy z = b"])
    have eva: "evals a A x"
      using px left
      by (rule eqSubst[
            where Q="\<lambda>t. evals t A x"])
    have evby: "evals b A y"
      using py right
      by (rule eqSubst[
            where Q="\<lambda>t. evals t A y"])
    have evb: "evals b A x"
      using eqSym[OF xy] evby
      by (rule eqSubst[
            where Q="\<lambda>q. evals b A q"])
    show thesis
      by (rule that[OF x eva evb])
  qed
qed

lemma neq_prem_fuel:
  assumes hJ: "hyp_of J N" and rest: "rest N"
      and a: "a N" and b: "b N" and A: "A N"
      and m: "mem (hyp_of J \<tturnstile> pack_F F_NEQ \<langle>a, b\<rangle>) rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
        sat_hyp_fuel (hyp_of K) A \<Longrightarrow>
        sat_fuel (conc_of K) A"
      and satG: "sat_hyp_fuel (hyp_of J) A"
  obtains x y where "x N" and "y N"
      and "evals a A x" and "evals b A y"
      and "x \<noteq> y"
proof -
  let ?f = "pack_F F_NEQ \<langle>a, b\<rangle>"
  let ?K = "hyp_of J \<tturnstile> ?f"
  have ab: "\<langle>a, b\<rangle> N"
    using a b by simp
  have f: "?f N"
    by (rule pack_F_N[OF _ ab], simp)
  have K: "?K N"
    using hJ f by simp
  have hK: "hyp_of ?K = hyp_of J"
    by (rule cpx_proj[OF hJ f])
  have cK: "conc_of ?K = ?f"
    by (rule cpy_proj[OF hJ f])
  have satKh: "sat_hyp_fuel (hyp_of ?K) A"
    using eqSym[OF hK] satG
    by (rule eqSubst[
          where Q="\<lambda>G. sat_hyp_fuel G A"])
  have satK: "sat_fuel (conc_of ?K) A"
    by (rule prev[OF K m satKh])
  have sat: "sat_fuel ?f A"
    using cK satK
    by (rule eqSubst[
          where Q="\<lambda>p. sat_fuel p A"])
  have tg: "tag_F ?f = F_NEQ"
    by (rule tag_pack_F[OF _ ab], simp)
  have ld: "load_F ?f = \<langle>a, b\<rangle>"
    by (rule load_pack_F[OF _ ab], simp)
  show thesis
    using sat
  proof (rule sat_fuelE)
    fix x y
    assume x: "x N" and y: "y N"
        and left: "evals (cpx (load_F ?f)) A x"
        and right: "evals (cpy (load_F ?f)) A y"
        and relation:
          "if tag_F ?f = F_EQ then x = y else x \<noteq> y"
    have px: "cpx (load_F ?f) = a"
      using eqSym[OF ld] cpx_proj[OF a b]
      by (rule eqSubst[
            where Q="\<lambda>z. cpx z = a"])
    have py: "cpy (load_F ?f) = b"
      using eqSym[OF ld] cpy_proj[OF a b]
      by (rule eqSubst[
            where Q="\<lambda>z. cpy z = b"])
    have eva: "evals a A x"
      using px left
      by (rule eqSubst[
            where Q="\<lambda>t. evals t A x"])
    have evb: "evals b A y"
      using py right
      by (rule eqSubst[
            where Q="\<lambda>t. evals t A y"])
    have neq: "x \<noteq> y"
      using x y tg relation by simp
    show thesis
      by (rule that[OF x y eva evb neq])
  qed
qed

lemma evals_suc_tagI:
  assumes t: "t N" and A: "A N" and q: "q N"
      and tg: "tag_T t = T_SUC"
      and ev: "evals (load_T t) A q"
  shows "evals t A (S q)"
proof -
  have load: "load_T t N"
    by (rule load_T_N[OF t])
  have packed: "pack_T T_SUC (load_T t) = t"
  proof -
    have rep: "pack_T (tag_T t) (load_T t) = t"
      by (rule pack_tag_T[OF t])
    show ?thesis
      using tg rep
      by (rule eqSubst[
            where a="tag_T t" and b=T_SUC
              and Q="\<lambda>z. pack_T z (load_T t) = t"])
  qed
  have run: "evals (pack_T T_SUC (load_T t)) A (S q)"
    by (rule evals_sucI[OF load A q ev])
  show ?thesis
    using packed run
    by (rule eqSubst[
          where Q="\<lambda>u. evals u A (S q)"])
qed

lemma evals_pred_suc_tagI:
  assumes t: "t N" and A: "A N" and q: "q N"
      and pred: "tag_T t = T_PRED"
      and suc: "tag_T (load_T t) = T_SUC"
      and body: "load_T (load_T t) = u"
      and u: "u N" and ev: "evals u A q"
  shows "evals t A q"
proof -
  have load: "load_T t N"
    by (rule load_T_N[OF t])
  have load2: "load_T (load_T t) N"
    by (rule load_T_N[OF load])
  have innerPacked: "pack_T T_SUC u = load_T t"
  proof -
    have rep:
      "pack_T (tag_T (load_T t)) (load_T (load_T t)) =
        load_T t"
      by (rule pack_tag_T[OF load])
    have repSuc:
      "pack_T T_SUC (load_T (load_T t)) = load_T t"
      using suc rep
      by (rule eqSubst[
            where a="tag_T (load_T t)" and b=T_SUC
              and Q="\<lambda>z.
                pack_T z (load_T (load_T t)) = load_T t"])
    show ?thesis
      using body repSuc
      by (rule eqSubst[
            where a="load_T (load_T t)" and b=u
              and Q="\<lambda>z. pack_T T_SUC z = load_T t"])
  qed
  have evSuc: "evals (pack_T T_SUC u) A (S q)"
    by (rule evals_sucI[OF u A q ev])
  have evLoad: "evals (load_T t) A (S q)"
    using innerPacked evSuc
    by (rule eqSubst[
          where Q="\<lambda>v. evals v A (S q)"])
  have Sq: "S q N"
    by (rule natS[OF q])
  have evPred0:
    "evals (pack_T T_PRED (load_T t)) A (P (S q))"
    by (rule evals_predI[OF load A Sq evLoad])
  have psq: "P (S q) = q"
    by (rule predSucInv[OF q])
  have evPred:
    "evals (pack_T T_PRED (load_T t)) A q"
    using psq evPred0
    by (rule eqSubst[
          where a="P (S q)" and b=q
            and Q="\<lambda>v.
            evals (pack_T T_PRED (load_T t)) A v"])
  have packed: "pack_T T_PRED (load_T t) = t"
  proof -
    have rep: "pack_T (tag_T t) (load_T t) = t"
      by (rule pack_tag_T[OF t])
    show ?thesis
      using pred rep
      by (rule eqSubst[
            where a="tag_T t" and b=T_PRED
              and Q="\<lambda>z. pack_T z (load_T t) = t"])
  qed
  show ?thesis
    using packed evPred
    by (rule eqSubst[
          where Q="\<lambda>v. evals v A q"])
qed

lemma evals_ifz_nonzero_tagI:
  assumes t: "t N" and A: "A N"
      and v: "v N" and r: "r N"
      and tg: "tag_T t = T_IFZ"
      and evc: "evals (cpx (load_T t)) A v"
      and nz: "v \<noteq> 0"
      and evr: "evals (cpy (cpy (load_T t))) A r"
  shows "evals t A r"
proof -
  let ?c = "cpx (load_T t)"
  let ?tail = "cpy (load_T t)"
  let ?l = "cpx ?tail"
  let ?r = "cpy ?tail"
  have load: "load_T t N"
    by (rule load_T_N[OF t])
  have c: "?c N"
    by (rule cpx_terminates[OF load])
  have tail: "?tail N"
    by (rule cpy_terminates[OF load])
  have l: "?l N"
    by (rule cpx_terminates[OF tail])
  have rr: "?r N"
    by (rule cpy_terminates[OF tail])
  have ex: "\<exists>w. v = S w"
    by (rule num_nonzero[OF v nz[unfolded neq_def]])
  obtain w where w: "w N" and vw: "v = S w"
    by (rule existsE[OF ex])
  have evcS: "evals ?c A (S w)"
    using vw evc
    by (rule eqSubst[
          where a=v and b="S w"
            and Q="\<lambda>q. evals ?c A q"])
  have evPacked:
    "evals (pack_T T_IFZ \<langle>?c, \<langle>?l, ?r\<rangle>\<rangle>) A r"
    by (rule evals_ifz_nonzeroI[OF c l rr A w r evcS evr])
  have tailRec: "\<langle>?l, ?r\<rangle> = ?tail"
    by (rule cpair_reconstr[OF tail])
  have loadRec0: "\<langle>?c, ?tail\<rangle> = load_T t"
    by (rule cpair_reconstr[OF load])
  have loadRec:
    "\<langle>?c, \<langle>?l, ?r\<rangle>\<rangle> = load_T t"
    using eqSym[OF tailRec] loadRec0
    by (rule eqSubst[
          where a="?tail" and b="\<langle>?l, ?r\<rangle>"
            and Q="\<lambda>z. \<langle>?c, z\<rangle> = load_T t"])
  have packed0: "pack_T T_IFZ (load_T t) = t"
  proof -
    have rep: "pack_T (tag_T t) (load_T t) = t"
      by (rule pack_tag_T[OF t])
    show ?thesis
      using tg rep
      by (rule eqSubst[
            where a="tag_T t" and b=T_IFZ
              and Q="\<lambda>z. pack_T z (load_T t) = t"])
  qed
  have packed:
  "pack_T T_IFZ \<langle>?c, \<langle>?l, ?r\<rangle>\<rangle> = t"
  by (rule eqSubst[
        where a="load_T t"
          and b="\<langle>?c, \<langle>?l, ?r\<rangle>\<rangle>"
          and Q="\<lambda>z. pack_T T_IFZ z = t",
        OF eqSym[OF loadRec] packed0])
  show ?thesis
    using packed evPacked
    by (rule eqSubst[
          where Q="\<lambda>u. evals u A r"])
qed

lemma evals_ifz_zero_tagI:
  assumes t: "t N" and A: "A N" and r: "r N"
      and tg: "tag_T t = T_IFZ"
      and evc: "evals (cpx (load_T t)) A 0"
      and evl: "evals (cpx (cpy (load_T t))) A r"
  shows "evals t A r"
proof -
  let ?c = "cpx (load_T t)"
  let ?tail = "cpy (load_T t)"
  let ?l = "cpx ?tail"
  let ?r = "cpy ?tail"
  have load: "load_T t N"
    by (rule load_T_N[OF t])
  have c: "?c N"
    by (rule cpx_terminates[OF load])
  have tail: "?tail N"
    by (rule cpy_terminates[OF load])
  have l: "?l N"
    by (rule cpx_terminates[OF tail])
  have rr: "?r N"
    by (rule cpy_terminates[OF tail])
  have evPacked:
    "evals (pack_T T_IFZ \<langle>?c, \<langle>?l, ?r\<rangle>\<rangle>) A r"
    using c l rr A r evc evl
    by (rule evals_ifz_zeroI)
  have tailRec: "\<langle>?l, ?r\<rangle> = ?tail"
    by (rule cpair_reconstr[OF tail])
  have loadRec0: "\<langle>?c, ?tail\<rangle> = load_T t"
    by (rule cpair_reconstr[OF load])
  have loadRec:
    "\<langle>?c, \<langle>?l, ?r\<rangle>\<rangle> = load_T t"
    using eqSym[OF tailRec] loadRec0
    by (rule eqSubst[
          where a="?tail" and b="\<langle>?l, ?r\<rangle>"
            and Q="\<lambda>z. \<langle>?c, z\<rangle> = load_T t"])
  have packed0: "pack_T T_IFZ (load_T t) = t"
  proof -
    have rep: "pack_T (tag_T t) (load_T t) = t"
      by (rule pack_tag_T[OF t])
    show ?thesis
      using tg rep
      by (rule eqSubst[
            where a="tag_T t" and b=T_IFZ
              and Q="\<lambda>z. pack_T z (load_T t) = t"])
  qed
  have packed:
  "pack_T T_IFZ \<langle>?c, \<langle>?l, ?r\<rangle>\<rangle> = t"
  by (rule eqSubst[
        where a="load_T t"
          and b="\<langle>?c, \<langle>?l, ?r\<rangle>\<rangle>"
          and Q="\<lambda>z. pack_T T_IFZ z = t",
        OF eqSym[OF loadRec] packed0])
  show ?thesis
    using packed evPacked
    by (rule eqSubst[
          where Q="\<lambda>u. evals u A r"])
qed

lemma check_eq_rules_sound_fuel:
  assumes J: "J N" and rest: "rest N" and A: "A N"
      and tg: "tag_F (conc_of J) = F_EQ"
      and chk:
        "check_eq_rules (hyp_of J)
          (cpx (load_F (conc_of J)))
          (cpy (load_F (conc_of J)))
          (tag_T (cpx (load_F (conc_of J))))
          (tag_T (cpy (load_F (conc_of J)))) rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
        sat_hyp_fuel (hyp_of K) A \<Longrightarrow>
        sat_fuel (conc_of K) A"
      and satG: "sat_hyp_fuel (hyp_of J) A"
  shows "sat_fuel (conc_of J) A"
proof -
  let ?f = "conc_of J"
  let ?G = "hyp_of J"
  let ?a = "cpx (load_F ?f)"
  let ?b = "cpy (load_F ?f)"
  let ?z = "pack_T T_ZERO 0"
  let ?la = "load_T ?a"
  let ?lb = "load_T ?b"
  let ?c = "cpx (load_T ?a)"
  let ?l = "cpx (cpy (load_T ?a))"
  let ?r = "cpy (cpy (load_T ?a))"
  have f: "?f N"
    using J by simp
  have G: "?G N"
    using J by simp
  have lf: "load_F ?f N"
    by (rule load_F_N[OF f])
  have a: "?a N"
    by (rule cpx_terminates[OF lf])
  have b: "?b N"
    by (rule cpy_terminates[OF lf])
  have taga: "tag_T ?a N"
    by (rule tag_T_N[OF a])
  have tagb: "tag_T ?b N"
    by (rule tag_T_N[OF b])
  have z: "?z N"
    by (rule pack_T_N[OF _ nat0], simp)
  have la: "?la N"
    by (rule load_T_N[OF a])
  have lb: "?lb N"
    by (rule load_T_N[OF b])
  have lla: "load_T ?la N"
    by (rule load_T_N[OF la])
  have c: "?c N"
    by (rule cpx_terminates[OF la])
  have tail: "cpy (load_T ?a) N"
    by (rule cpy_terminates[OF la])
  have l: "?l N"
    by (rule cpx_terminates[OF tail])
  have r: "?r N"
    by (rule cpy_terminates[OF tail])
  have suca: "pack_T T_SUC ?a N"
    by (rule pack_T_N[OF _ a], simp)
  have sucb: "pack_T T_SUC ?b N"
    by (rule pack_T_N[OF _ b], simp)
  have tagla: "tag_T ?la N"
    by (rule tag_T_N[OF la])
  have sucN: "T_SUC N"
    by simp
  have predN: "T_PRED N"
    by simp
  have ifzN: "T_IFZ N"
    by simp

  have g1B: "(?a = ?z \<and> ?b = ?z) B"
    using eqBool[OF a z] eqBool[OF b z] by auto

  have pr_ba: "\<langle>?b, ?a\<rangle> N"
    using b a by simp
  have pf2: "pack_F F_EQ \<langle>?b, ?a\<rangle> N"
    by (rule pack_F_N[OF _ pr_ba], simp)
  have j2: "(?G \<tturnstile> pack_F F_EQ \<langle>?b, ?a\<rangle>) N"
    using G pf2 by simp
  have g2B:
    "mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?a\<rangle>) rest B"
    by (rule mem_bool[OF j2 rest])

  have pr_lalb: "\<langle>?la, ?lb\<rangle> N"
    using la lb by simp
  have pf3: "pack_F F_EQ \<langle>?la, ?lb\<rangle> N"
    by (rule pack_F_N[OF _ pr_lalb], simp)
  have j3: "(?G \<tturnstile> pack_F F_EQ \<langle>?la, ?lb\<rangle>) N"
    using G pf3 by simp
  have m3B:
    "mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?lb\<rangle>) rest B"
    by (rule mem_bool[OF j3 rest])
  have g3B:
    "(tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and>
    mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?lb\<rangle>) rest) B"
    using eqBool[OF taga sucN] eqBool[OF tagb sucN] m3B by auto

  have pr_ss:
    "\<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle> N"
    using suca sucb by simp
  have pf4:
    "pack_F F_EQ
    \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle> N"
    by (rule pack_F_N[OF _ pr_ss], simp)
  have j4:
    "(?G \<tturnstile>
    pack_F F_EQ
      \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) N"
    using G pf4 by simp
  have g4B:
    "mem
    (?G \<tturnstile>
      pack_F F_EQ
        \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>)
    rest B"
    by (rule mem_bool[OF j4 rest])

  have pr_bb: "\<langle>?b, ?b\<rangle> N"
    using b by simp
  have pfbb: "pack_F F_EQ \<langle>?b, ?b\<rangle> N"
    by (rule pack_F_N[OF _ pr_bb], simp)
  have jrr: "(?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) N"
    using G pfbb by simp
  have mrrB:
    "mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest B"
    by (rule mem_bool[OF jrr rest])

  have pr_cz: "\<langle>?c, ?z\<rangle> N"
    using c z by simp
  have pf6: "pack_F F_NEQ \<langle>?c, ?z\<rangle> N"
    by (rule pack_F_N[OF _ pr_cz], simp)
  have j6a:
    "(?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) N"
    using G pf6 by simp
  have m6aB:
    "mem (?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) rest B"
    by (rule mem_bool[OF j6a rest])

  have pf7: "pack_F F_EQ \<langle>?c, ?z\<rangle> N"
    by (rule pack_F_N[OF _ pr_cz], simp)
  have j7a:
    "(?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) N"
    using G pf7 by simp
  have m7aB:
    "mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest B"
    by (rule mem_bool[OF j7a rest])
  have g6B:
    "(tag_T ?a = T_IFZ \<and>
      ?b = ?r \<and>
      mem (?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) rest \<and>
      mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest) B"
    using eqBool[OF taga ifzN] eqBool[OF b r]
      mem_bool[OF j6a rest] mrrB by auto
  have g7B:
    "(tag_T ?a = T_IFZ \<and>
      ?b = ?l \<and>
      mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest \<and>
      mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest) B"
    using eqBool[OF taga ifzN] eqBool[OF b l]
      mem_bool[OF j7a rest] mrrB by auto
  have pr_bb: "\<langle>?b, ?b\<rangle> N"
    using b by simp
  have pfbb: "pack_F F_EQ \<langle>?b, ?b\<rangle> N"
    by (rule pack_F_N[OF _ pr_bb], simp)
  have jrr:
    "(?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) N"
    using G pfbb by simp
  have mrrB:
    "mem
    (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>)
    rest B"
    by (rule mem_bool[OF jrr rest])
  have g5B:
    "(tag_T ?a = T_PRED \<and>
    tag_T ?la = T_SUC \<and>
    load_T ?la = ?b \<and>
    mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest) B"
    using eqBool[OF taga predN] eqBool[OF tagla sucN] eqBool[OF lla b] mrrB  by auto
  have R0:
    "if ?a = ?z \<and> ?b = ?z then True
     else if mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?a\<rangle>) rest then True
     else if tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and>
       mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?lb\<rangle>) rest
     then True
     else if mem (?G \<tturnstile>
       pack_F F_EQ
         \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest
     then True
     else if tag_T ?a = T_PRED \<and>
       tag_T ?la = T_SUC \<and> load_T ?la = ?b \<and>
       mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
     then True
     else if tag_T ?a = T_IFZ \<and> ?b = ?r \<and>
       mem (?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) rest \<and>
       mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
     then True
     else if tag_T ?a = T_IFZ \<and> ?b = ?l \<and>
       mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest \<and>
       mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
     then True
     else False"
    using chk
    by (rule defI[OF check_eq_rules_def])

  show ?thesis
  proof (rule cases_bool[where q="?a = ?z \<and> ?b = ?z"])
    show "(?a = ?z \<and> ?b = ?z) B"
      by (rule g1B)
  next
    assume g1: "?a = ?z \<and> ?b = ?z"
    have az: "?a = ?z"
      by (rule conjE1[OF g1])
    have bz: "?b = ?z"
      by (rule conjE2[OF g1])
    have evz: "evals ?z A 0"
      by (rule evals_zeroI[OF A])
    have eva: "evals ?a A 0"
      using eqSym[OF az] evz
      by (rule eqSubst[where Q="\<lambda>t. evals t A 0"])
    have evb: "evals ?b A 0"
      using eqSym[OF bz] evz
      by (rule eqSubst[where Q="\<lambda>t. evals t A 0"])
    show ?thesis
      by (rule sat_fuel_formula_eqI[OF f A nat0 tg eva evb])
  next
    assume n1: "\<not> (?a = ?z \<and> ?b = ?z)"
    have R1:
      "if mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?a\<rangle>) rest then True
       else if tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and>
         mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?lb\<rangle>) rest
       then True
       else if mem (?G \<tturnstile>
         pack_F F_EQ
           \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest
       then True
       else if tag_T ?a = T_PRED \<and>
         tag_T ?la = T_SUC \<and> load_T ?la = ?b \<and>
         mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
       then True
       else if tag_T ?a = T_IFZ \<and> ?b = ?r \<and>
         mem (?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) rest \<and>
         mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
       then True
       else if tag_T ?a = T_IFZ \<and> ?b = ?l \<and>
         mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest \<and>
         mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
       then True
       else False"
      using n1 R0 by (rule notcond_thenE)
    show ?thesis
    proof (rule cases_bool[
          where q="mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?a\<rangle>) rest"])
      show "mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?a\<rangle>) rest B"
        by (rule g2B)
    next
      assume g2:
        "mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?a\<rangle>) rest"
      obtain q where q: "q N"
        and evb: "evals ?b A q"
        and eva: "evals ?a A q"
        by (rule eq_prem_fuel[
              OF G rest b a A g2 prev satG])
      show ?thesis
        by (rule sat_fuel_formula_eqI[OF f A q tg eva evb])
    next
      assume n2:
        "\<not> mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?a\<rangle>) rest"
      have R2:
        "if tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and>
          mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?lb\<rangle>) rest
         then True
         else if mem (?G \<tturnstile>
           pack_F F_EQ
             \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest
         then True
         else if tag_T ?a = T_PRED \<and>
           tag_T ?la = T_SUC \<and> load_T ?la = ?b \<and>
           mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
         then True
         else if tag_T ?a = T_IFZ \<and> ?b = ?r \<and>
           mem (?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) rest \<and>
           mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
         then True
         else if tag_T ?a = T_IFZ \<and> ?b = ?l \<and>
           mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest \<and>
           mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
         then True
         else False"
        using n2 R1 by (rule notcond_thenE)
      show ?thesis
      proof (rule cases_bool[
          where q="tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and>
            mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?lb\<rangle>) rest"])
        show
          "(tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and>
            mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?lb\<rangle>) rest) B"
          by (rule g3B)
      next
        assume g3:
          "tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and>
            mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?lb\<rangle>) rest"
        have g3l: "tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC"
          by (rule conjE1[OF g3])
        have ma:
          "mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?lb\<rangle>) rest"
          by (rule conjE2[OF g3])
        have tagaS: "tag_T ?a = T_SUC"
          by (rule conjE1[OF g3l])
        have tagbS: "tag_T ?b = T_SUC"
          by (rule conjE2[OF g3l])
        obtain q where q: "q N"
            and eva0: "evals ?la A q"
            and evb0: "evals ?lb A q"
          by (rule eq_prem_fuel[
                OF G rest la lb A ma prev satG])
        have eva: "evals ?a A (S q)"
          by (rule evals_suc_tagI[OF a A q tagaS eva0])
        have evb: "evals ?b A (S q)"
          by (rule evals_suc_tagI[OF b A q tagbS evb0])
        show ?thesis
          by (rule sat_fuel_formula_eqI[
                OF f A natS[OF q] tg eva evb])
      next
        assume n3:
          "\<not> (tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and>
            mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?lb\<rangle>) rest)"
        have R3:
          "if mem (?G \<tturnstile>
            pack_F F_EQ
              \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest
           then True
           else if tag_T ?a = T_PRED \<and>
             tag_T ?la = T_SUC \<and> load_T ?la = ?b \<and>
             mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
           then True
           else if tag_T ?a = T_IFZ \<and> ?b = ?r \<and>
             mem (?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) rest \<and>
             mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
           then True
           else if tag_T ?a = T_IFZ \<and> ?b = ?l \<and>
             mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest \<and>
             mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
           then True
           else False"
          using n3 R2 by (rule notcond_thenE)
        show ?thesis
        proof (rule cases_bool[
            where q="mem (?G \<tturnstile>
              pack_F F_EQ
                \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest"])
          show
            "mem (?G \<tturnstile>
              pack_F F_EQ
                \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest B"
            by (rule g4B)
        next
          assume g4:
            "mem (?G \<tturnstile>
              pack_F F_EQ
                \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest"
          obtain q where q: "q N"
              and evaS: "evals (pack_T T_SUC ?a) A q"
              and evbS: "evals (pack_T T_SUC ?b) A q"
            by (rule eq_prem_fuel[OF G rest suca sucb A g4 prev satG])
          obtain x where x: "x N"
            and eva: "evals ?a A x"
            and qx: "q = S x"
            by (rule evals_sucE[OF a A evaS])
          obtain y where y: "y N"
            and evb0: "evals ?b A y"
            and qy: "q = S y"
            by (rule evals_sucE[OF b A evbS])
          have sxq: "S x = q"
            by (rule eqSym[OF qx])
          have sxy: "S x = S y"
            by (rule eq_trans[OF sxq qy])
          have xy: "x = y"
            by (rule sucInj[OF sxy])
          have evb: "evals ?b A x"
            using eqSym[OF xy] evb0
            by (rule eqSubst[
                  where a=y and b=x
                    and Q="\<lambda>v. evals ?b A v"])
          show ?thesis
            by (rule sat_fuel_formula_eqI[
                  OF f A x tg eva evb])
        next
          assume n4:
            "\<not> mem (?G \<tturnstile>
              pack_F F_EQ
                \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest"
          have R4:
            "if tag_T ?a = T_PRED \<and>
              tag_T ?la = T_SUC \<and> load_T ?la = ?b \<and>
              mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
             then True
             else if tag_T ?a = T_IFZ \<and> ?b = ?r \<and>
               mem (?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) rest \<and>
               mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
             then True
             else if tag_T ?a = T_IFZ \<and> ?b = ?l \<and>
               mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest \<and>
               mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
             then True
             else False"
            using n4 R3 by (rule notcond_thenE)
          show ?thesis
          proof (rule cases_bool[
              where q="tag_T ?a = T_PRED \<and>
                tag_T ?la = T_SUC \<and> load_T ?la = ?b \<and>
                mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest"])
            show
              "(tag_T ?a = T_PRED \<and>
                tag_T ?la = T_SUC \<and> load_T ?la = ?b \<and>
                mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest) B"
              by (rule g5B)
          next
            assume g5:
              "tag_T ?a = T_PRED \<and>
                tag_T ?la = T_SUC \<and> load_T ?la = ?b \<and>
                mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest"
            have g5l:
              "(tag_T ?a = T_PRED \<and> tag_T ?la = T_SUC) \<and>
                load_T ?la = ?b"
              by (rule conjE1[OF g5])
            have m:
              "mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest"
              by (rule conjE2[OF g5])
            have g5ll: "tag_T ?a = T_PRED \<and> tag_T ?la = T_SUC"
              by (rule conjE1[OF g5l])
            have body: "load_T ?la = ?b"
              by (rule conjE2[OF g5l])
            have pred: "tag_T ?a = T_PRED"
              by (rule conjE1[OF g5ll])
            have suc: "tag_T ?la = T_SUC"
              by (rule conjE2[OF g5ll])
            obtain q where q: "q N"
                and evb: "evals ?b A q"
                and evb2: "evals ?b A q"
              by (rule eq_prem_fuel[
                    OF G rest b b A m prev satG])
            have eva: "evals ?a A q"
              by (rule evals_pred_suc_tagI[
                    OF a A q pred suc body b evb])
            show ?thesis
              by (rule sat_fuel_formula_eqI[
                    OF f A q tg eva evb2])
          next
            assume n5:
              "\<not> (tag_T ?a = T_PRED \<and>
                tag_T ?la = T_SUC \<and> load_T ?la = ?b \<and>
                mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest)"
            have R5:
              "if tag_T ?a = T_IFZ \<and> ?b = ?r \<and>
                mem (?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) rest \<and>
                mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
               then True
               else if tag_T ?a = T_IFZ \<and> ?b = ?l \<and>
                 mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest \<and>
                 mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
               then True
               else False"
              using n5 R4 by (rule notcond_thenE)
            show ?thesis
            proof (rule cases_bool[
                where q="tag_T ?a = T_IFZ \<and> ?b = ?r \<and>
                  mem (?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) rest \<and>
                  mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest"])
              show
                "(tag_T ?a = T_IFZ \<and> ?b = ?r \<and>
                  mem (?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) rest \<and>
                  mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest) B"
                by (rule g6B)
            next
              assume g6:
                "tag_T ?a = T_IFZ \<and> ?b = ?r \<and>
                  mem (?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) rest \<and>
                  mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest"
              have g6l:
                "(tag_T ?a = T_IFZ \<and> ?b = ?r) \<and>
                  mem (?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) rest"
                by (rule conjE1[OF g6])
              have mb:
                "mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest"
                by (rule conjE2[OF g6])
              have g6ll: "tag_T ?a = T_IFZ \<and> ?b = ?r"
                by (rule conjE1[OF g6l])
              have mc:
                "mem (?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) rest"
                by (rule conjE2[OF g6l])
              have tagaI: "tag_T ?a = T_IFZ"
                by (rule conjE1[OF g6ll])
              have br: "?b = ?r"
                by (rule conjE2[OF g6ll])
              obtain v w where v: "v N" and w: "w N"
                  and evc: "evals ?c A v"
                  and evz: "evals ?z A w"
                  and vw: "v \<noteq> w"
                by (rule neq_prem_fuel[
                      OF G rest c z A mc prev satG])
              have evzero: "evals ?z A 0"
                by (rule evals_zeroI[OF A])
              have w0: "w = 0"
                by (rule evals_functional[OF z A evz evzero])
              have v0: "v \<noteq> 0"
                using w0 vw
                by (rule eqSubst[
                      where Q="\<lambda>q. v \<noteq> q"])
              obtain q where q: "q N"
                  and evb: "evals ?b A q"
                  and evb2: "evals ?b A q"
                by (rule eq_prem_fuel[
                      OF G rest b b A mb prev satG])
              have evr: "evals ?r A q"
                using br evb2
                by (rule eqSubst[
                      where a="?b" and b="?r"
                        and Q="\<lambda>t. evals t A q"])
              have eva: "evals ?a A q"
                by (rule evals_ifz_nonzero_tagI[
                      OF a A v q tagaI evc v0 evr])
              show ?thesis
                by (rule sat_fuel_formula_eqI[
                      OF f A q tg eva evb])
            next
              assume n6:
                "\<not> (tag_T ?a = T_IFZ \<and> ?b = ?r \<and>
                  mem (?G \<tturnstile> pack_F F_NEQ \<langle>?c, ?z\<rangle>) rest \<and>
                  mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest)"
              have R6:
                "if tag_T ?a = T_IFZ \<and> ?b = ?l \<and>
                  mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest \<and>
                  mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest
                 then True
                 else False"
                using n6 R5 by (rule notcond_thenE)
              show ?thesis
              proof (rule cases_bool[
                  where q="tag_T ?a = T_IFZ \<and> ?b = ?l \<and>
                    mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest \<and>
                    mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest"])
                show
                  "(tag_T ?a = T_IFZ \<and> ?b = ?l \<and>
                    mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest \<and>
                    mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest) B"
                  by (rule g7B)
              next
                assume g7:
                  "tag_T ?a = T_IFZ \<and> ?b = ?l \<and>
                    mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest \<and>
                    mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest"
                have g7l:
                  "(tag_T ?a = T_IFZ \<and> ?b = ?l) \<and>
                    mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest"
                  by (rule conjE1[OF g7])
                have mb:
                  "mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest"
                  by (rule conjE2[OF g7])
                have g7ll: "tag_T ?a = T_IFZ \<and> ?b = ?l"
                  by (rule conjE1[OF g7l])
                have mc:
                  "mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest"
                  by (rule conjE2[OF g7l])
                have tagaI: "tag_T ?a = T_IFZ"
                  by (rule conjE1[OF g7ll])
                have bl: "?b = ?l"
                  by (rule conjE2[OF g7ll])
                obtain q0 where q0: "q0 N"
                    and evc0: "evals ?c A q0"
                    and evz0: "evals ?z A q0"
                  by (rule eq_prem_fuel[
                        OF G rest c z A mc prev satG])
                have evzero: "evals ?z A 0"
                  by (rule evals_zeroI[OF A])
                have q00: "q0 = 0"
                  by (rule evals_functional[OF z A evz0 evzero])
                have evc: "evals ?c A 0"
                  using q00 evc0
                  by (rule eqSubst[
                        where Q="\<lambda>q. evals ?c A q"])
                obtain q where q: "q N"
                    and evb: "evals ?b A q"
                    and evb2: "evals ?b A q"
                  by (rule eq_prem_fuel[
                        OF G rest b b A mb prev satG])
                have evl: "evals ?l A q"
                  using bl evb2
                  by (rule eqSubst[
                        where a="?b" and b="?l"
                          and Q="\<lambda>t. evals t A q"])
                have eva: "evals ?a A q"
                  by (rule evals_ifz_zero_tagI[
                        OF a A q tagaI evc evl])
                show ?thesis
                  by (rule sat_fuel_formula_eqI[
                        OF f A q tg eva evb])
              next
                assume n7:
                  "\<not> (tag_T ?a = T_IFZ \<and> ?b = ?l \<and>
                    mem (?G \<tturnstile> pack_F F_EQ \<langle>?c, ?z\<rangle>) rest \<and>
                    mem (?G \<tturnstile> pack_F F_EQ \<langle>?b, ?b\<rangle>) rest)"
                have bot: "False"
                  using n7 R6 by (rule notcond_thenE)
                have contra: "S 0 = 0"
                  by (rule bot[unfolded False_def])
                show ?thesis
                  by (rule exF[
                        OF contra sucNonZero[OF nat0, unfolded neq_def]])
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma check_app_bool [auto]:
  assumes J: "J N" and r: "rest N"
  shows "check_app J rest B"
proof -
  have oneN: "(1::num) N" 
    by simp
  have ld1: "len dfns - 1 N" 
    by (rule sub_terminates[OF len_nat[OF dfns_N] oneN])
  show ?thesis
    apply (rule defE[OF check_app_def[where J=J and rest=rest]])
    apply (rule app_d_bool[OF J ld1 r])
    done
qed


lemma find_struct_bool [auto]:
  assumes J: "J N" and G: "G N" and ptr: "ptr N"
  shows "find_struct J G ptr B"
proof (rule list_induct[OF ptr])
  show "find_struct J G Nil B" by (rule defE[OF find_struct_def[where ptr=Nil]], simp)
next
  fix h t assume h: "h N" and t: "t N" and IH: "find_struct J G t B"
  show "find_struct J G (Cons h t) B"
    by (rule defE[OF find_struct_def[where ptr="Cons h t"]], insert J G h t IH, simp+)
qed

lemma find_cut_bool [auto]:
  assumes J: "J N" and rest: "rest N" and ptr: "ptr N"
  shows "find_cut J rest ptr B"
proof (rule list_induct[OF ptr])
  show "find_cut J rest Nil B"
    apply (rule defE[OF find_cut_def[where J=J and rest=rest and ptr=Nil]])
    apply simp
    done
next
  fix h t assume h: "h N" and t: "t N" and IH: "find_cut J rest t B"
  show "find_cut J rest (Cons h t) B"
  proof -
    have htN: "h \<triangleright> t N" 
      using h t by simp
    have g0: "(h \<triangleright> t = \<emptyset>) B" 
      apply (rule eqBool[OF htN]) 
      apply simp 
      done
    have g1: "(hyp_of h = hyp_of J) B" 
      using h J by simp
    have cc: "conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J N" 
      using h J by simp
    have m: "mem (conc_of h \<triangleright> hyp_of J \<tturnstile> conc_of J) rest B"
      by (rule mem_bool[OF cc rest])
    show "find_cut J rest (h \<triangleright> t) B"
      apply (rule defE[OF find_cut_def[where J=J and rest=rest and ptr="h \<triangleright> t"]])
      apply (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
      apply (rule condTB[OF g0 false_bool])
      apply (rule condTB[OF g1 _ IH])
      apply (rule condTB[OF m true_bool IH])
      done
  qed
qed

lemma check_cut_bool [auto]:
  assumes J: "J N" and rest: "rest N"
  shows "check_cut J rest B"
  apply (rule defE[OF check_cut_def[where J=J and rest=rest]])
  apply (rule find_cut_bool[OF J rest rest])
  done

lemma find_eq_bool [auto]:
  assumes J: "J N" and rest: "rest N" and ptr: "ptr N"
  shows "find_eq J rest ptr B"
proof (rule list_induct[OF ptr])
  show "find_eq J rest Nil B"
    apply (rule defE[OF find_eq_def[where J=J and rest=rest and ptr=Nil]])
    apply simp
    done
next
  fix h t assume h: "h N" and t: "t N" and IH: "find_eq J rest t B"
  show "find_eq J rest (Cons h t) B"
  proof -
    have htN: "h \<triangleright> t N" 
      using h t by simp
    have g0: "(h \<triangleright> t = \<emptyset>) B" 
      apply (rule eqBool[OF htN]) 
      apply simp 
      done
    have ch: "conc_of h N" 
      using h by simp
    have eqh: "(hyp_of h = hyp_of J) B" 
      using h J by simp
    have tgh: "tag_F (conc_of h) N" 
      by (rule tag_F_N[OF ch])
    have feqN: "F_EQ N" 
      by simp
    have eqtg: "(tag_F (conc_of h) = F_EQ) B" 
      by (rule eqBool[OF tgh feqN])
    have g1: "(hyp_of h = hyp_of J \<and> tag_F (conc_of h) = F_EQ) B"
      using eqh eqtg by simp

    have Lch: "load_F (conc_of h) N" 
      by (rule load_F_N[OF ch])
    have cxh: "cpx (load_F (conc_of h)) N" 
      by (rule cpx_terminates[OF Lch])
    have cyh: "cpy (load_F (conc_of h)) N" 
      by (rule cpy_terminates[OF Lch])
    have gphi: "find_phi J (cpx (load_F (conc_of h))) (cpy (load_F (conc_of h))) rest B"
      by (rule find_phi_bool[OF J cxh cyh rest])

    show "find_eq J rest (h \<triangleright> t) B"
      apply (rule defE[OF find_eq_def[where J=J and rest=rest and ptr="h \<triangleright> t"]])
      apply (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
      apply (rule condTB[OF g0 false_bool])
      apply (rule condTB[OF g1 _ IH])
      apply (rule condTB[OF gphi true_bool IH])
      done
  qed
qed

lemma check_subst_bool [auto]:
  assumes J: "J N" and rest: "rest N"
  shows "check_subst J rest B"
  apply (rule defE[OF check_subst_def[where J=J and rest=rest]])
  apply (rule find_eq_bool[OF J rest rest])
  done

lemma check_struct_bool [auto]:
  assumes J: "J N" and rest: "rest N"
  shows "check_struct J rest B"
proof -
  have hj: "hyp_of J N" 
    using J by simp
  show ?thesis
    apply (rule defE[OF check_struct_def[where J=J and rest=rest]])
    apply (rule find_struct_bool[OF J hj rest])
    done
qed

lemma find_ind_base_bool [auto]:
  assumes J: "J N" and a: "a N" and rest: "rest N" and ptr: "ptr N"
  shows "find_ind_base J a rest ptr B"
proof (rule list_induct[OF ptr])
  show "find_ind_base J a rest Nil B"
    apply (rule defE[OF find_ind_base_def[where J=J and a=a and rest=rest and ptr=Nil]])
    apply simp
    done
next
  fix h t assume h: "h N" and t: "t N" and IH: "find_ind_base J a rest t B"
  show "find_ind_base J a rest (Cons h t) B"
  proof -
    have htN: "h \<triangleright> t N" 
      using h t by simp
    have g0: "(h \<triangleright> t = \<emptyset>) B" 
      apply (rule eqBool[OF htN]) 
      apply simp 
      done
    have cJ: "conc_of J N" 
      using J by simp
    have ch: "conc_of h N" 
      using h by simp
    have hj: "hyp_of J N" 
      using J by simp
    have SJ: "J + 1 N" 
      using J by simp
    have eqh: "(hyp_of h = hyp_of J) B" 
      using h J by simp
    have rep: "rep_vars_F (conc_of J) (J + 1) N" 
      by (rule rep_vars_F_N[OF cJ SJ])
    have git: "check_ind_template (conc_of J) (conc_of h) a (hyp_of J)
                 (rep_vars_F (conc_of J) (J + 1)) (J + 1) rest B"
      by (rule check_ind_template_bool[OF cJ ch a hj rep SJ rest])
    show "find_ind_base J a rest (h \<triangleright> t) B"
      apply (rule defE[OF find_ind_base_def[where J=J and a=a and rest=rest and ptr="h \<triangleright> t"]])
      apply (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
      apply (rule condTB[OF g0 false_bool])
      apply (rule condTB[OF eqh _ IH])
      apply (rule condTB[OF git true_bool IH])
      done
  qed
qed

lemma check_ind_bool [auto]:
  assumes J: "J N" and r: "rest N"
  shows "check_ind J rest B"
proof -
  have cJ: "conc_of J N" 
    using J by simp
  have hj: "hyp_of J N" 
    using J by simp
  have LcJ: "load_F (conc_of J) N" 
    by (rule load_F_N[OF cJ])
  have cx: "cpx (load_F (conc_of J)) N" 
    by (rule cpx_terminates[OF LcJ])
  have xx: "\<langle>cpx (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle> N" 
    using cx by simp
  have pf: "pack_F F_EQ \<langle>cpx (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle> N"
    by (rule pack_F_N[OF _ xx], simp)
  have jN: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) N"
    using hj pf by simp
  have m: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest B"
    by (rule mem_bool[OF jN r])
  have SJ: "J + 1 N"
    using J by simp
  have fresh: "fresh_H (J + 1) (hyp_of J) B"
    by (rule fresh_H_bool[OF SJ hj])
  have guard: "(fresh_H (J + 1) (hyp_of J) \<and> mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest) B"
    using fresh m by auto
  have fib: "find_ind_base J (cpx (load_F (conc_of J))) rest rest B"
    by (rule find_ind_base_bool[OF J cx r r])
  show ?thesis
    apply (rule defE[OF check_ind_def[where J=J and rest=rest]])
    apply (rule condTB[OF guard fib false_bool])
    done
qed

lemma check_neq_rules_sound_fuel:
  assumes J: "J N" and rest: "rest N" and A: "A N"
      and tg: "\<not> tag_F (conc_of J) = F_EQ"
      and chk: "check_neq_rules (hyp_of J) (cpx (load_F (conc_of J))) (cpy (load_F (conc_of J)))
        (tag_T (cpx (load_F (conc_of J)))) (tag_T (cpy (load_F (conc_of J)))) rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow> sat_hyp_fuel (hyp_of K) A \<Longrightarrow> sat_fuel (conc_of K) A"
      and satG: "sat_hyp_fuel (hyp_of J) A"
  shows "sat_fuel (conc_of J) A"
proof -
  let ?f = "conc_of J"
  let ?G = "hyp_of J"
  let ?a = "cpx (load_F ?f)"
  let ?b = "cpy (load_F ?f)"
  let ?z = "pack_T T_ZERO 0"
  let ?la = "load_T ?a"
  let ?lb = "load_T ?b"
  have f: "?f N"
    using J by simp
  have G: "?G N"
    using J by simp
  have lf: "load_F ?f N"
    by (rule load_F_N[OF f])
  have a: "?a N"
    by (rule cpx_terminates[OF lf])
  have b: "?b N"
    by (rule cpy_terminates[OF lf])
  have taga: "tag_T ?a N"
    by (rule tag_T_N[OF a])
  have tagb: "tag_T ?b N"
    by (rule tag_T_N[OF b])
  have z: "?z N"
    by (rule pack_T_N[OF _ nat0], simp)
  have la: "?la N"
    by (rule load_T_N[OF a])
  have lb: "?lb N"
    by (rule load_T_N[OF b])
  have suca: "pack_T T_SUC ?a N"
    by (rule pack_T_N[OF _ a], simp)
  have sucb: "pack_T T_SUC ?b N"
    by (rule pack_T_N[OF _ b], simp)
  have sucN: "T_SUC N"
    by simp
  have pr_ba: "\<langle>?b, ?a\<rangle> N"
    using b a by simp
  have pf1: "pack_F F_NEQ \<langle>?b, ?a\<rangle> N"
    by (rule pack_F_N[OF _ pr_ba], simp)
  have j1: "(?G \<tturnstile> pack_F F_NEQ \<langle>?b, ?a\<rangle>) N"
    using G pf1 by simp
  have g1B: "mem (?G \<tturnstile> pack_F F_NEQ \<langle>?b, ?a\<rangle>) rest B"
    by (rule mem_bool[OF j1 rest])
  have pr_lala: "\<langle>?la, ?la\<rangle> N"
    using la by simp
  have pf2: "pack_F F_EQ \<langle>?la, ?la\<rangle> N"
    by (rule pack_F_N[OF _ pr_lala], simp)
  have j2: "(?G \<tturnstile> pack_F F_EQ \<langle>?la, ?la\<rangle>) N"
    using G pf2 by simp
  have m2B: "mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?la\<rangle>) rest B"
    by (rule mem_bool[OF j2 rest])
  have g2B: "(tag_T ?a = T_SUC \<and> ?b = ?z \<and> mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?la\<rangle>) rest) B"
    using eqBool[OF taga sucN] eqBool[OF b z] m2B by auto
  have pr_lalb: "\<langle>?la, ?lb\<rangle> N"
    using la lb by simp
  have pf3: "pack_F F_NEQ \<langle>?la, ?lb\<rangle> N"
    by (rule pack_F_N[OF _ pr_lalb], simp)
  have j3: "(?G \<tturnstile> pack_F F_NEQ \<langle>?la, ?lb\<rangle>) N"
    using G pf3 by simp
  have m3B: "mem (?G \<tturnstile> pack_F F_NEQ \<langle>?la, ?lb\<rangle>) rest B"
    by (rule mem_bool[OF j3 rest])
  have g3B: "(tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and> mem (?G \<tturnstile> pack_F F_NEQ \<langle>?la, ?lb\<rangle>) rest) B"
    using eqBool[OF taga sucN] eqBool[OF tagb sucN] m3B by auto
  have pr_ss: "\<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle> N"
    using suca sucb by simp
  have pf4: "pack_F F_NEQ \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle> N"
    by (rule pack_F_N[OF _ pr_ss], simp)
  have j4: "(?G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) N"
    using G pf4 by simp
  have g4B: "mem (?G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest B"
    by (rule mem_bool[OF j4 rest])
  have R0: "if mem (?G \<tturnstile> pack_F F_NEQ \<langle>?b, ?a\<rangle>) rest then True
    else if tag_T ?a = T_SUC \<and> ?b = ?z \<and> mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?la\<rangle>) rest then True
    else if tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and> mem (?G \<tturnstile> pack_F F_NEQ \<langle>?la, ?lb\<rangle>) rest then True
    else if mem (?G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest then True
    else False"
    using chk by (rule defI[OF check_neq_rules_def])
  show ?thesis
  proof (rule cases_bool[where q="mem (?G \<tturnstile> pack_F F_NEQ \<langle>?b, ?a\<rangle>) rest"])
    show "mem (?G \<tturnstile> pack_F F_NEQ \<langle>?b, ?a\<rangle>) rest B"
      by (rule g1B)
  next
    assume g1: "mem (?G \<tturnstile> pack_F F_NEQ \<langle>?b, ?a\<rangle>) rest"
    obtain y x where y: "y N" and x: "x N" and evb: "evals ?b A y" and eva: "evals ?a A x" and yx: "y \<noteq> x"
      by (rule neq_prem_fuel[OF G rest b a A g1 prev satG])
    have xy: "x \<noteq> y"
      by (rule neq_sym[OF y x yx])
    show ?thesis
      by (rule sat_fuel_formula_neqI[OF f A x y tg eva evb xy])
  next
    assume n1: "\<not> mem (?G \<tturnstile> pack_F F_NEQ \<langle>?b, ?a\<rangle>) rest"
    have R1: "if tag_T ?a = T_SUC \<and> ?b = ?z \<and> mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?la\<rangle>) rest then True
      else if tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and> mem (?G \<tturnstile> pack_F F_NEQ \<langle>?la, ?lb\<rangle>) rest then True
      else if mem (?G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest then True
      else False"
      using n1 R0 by (rule notcond_thenE)
    show ?thesis
    proof (rule cases_bool[where q="tag_T ?a = T_SUC \<and> ?b = ?z \<and> mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?la\<rangle>) rest"])
      show "(tag_T ?a = T_SUC \<and> ?b = ?z \<and> mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?la\<rangle>) rest) B"
        by (rule g2B)
    next
      assume g2: "tag_T ?a = T_SUC \<and> ?b = ?z \<and> mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?la\<rangle>) rest"
      have g2l: "tag_T ?a = T_SUC \<and> ?b = ?z"
        by (rule conjE1[OF g2])
      have m: "mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?la\<rangle>) rest"
        by (rule conjE2[OF g2])
      have tagaS: "tag_T ?a = T_SUC"
        by (rule conjE1[OF g2l])
      have bz: "?b = ?z"
        by (rule conjE2[OF g2l])
      obtain q where q: "q N" and evla: "evals ?la A q" and evla2: "evals ?la A q"
        by (rule eq_prem_fuel[OF G rest la la A m prev satG])
      have eva: "evals ?a A (S q)"
        by (rule evals_suc_tagI[OF a A q tagaS evla])
      have evzero: "evals ?z A 0"
        by (rule evals_zeroI[OF A])
      have evb: "evals ?b A 0"
        by (rule eqSubst[where a="?z" and b="?b" and Q="\<lambda>t. evals t A 0", OF eqSym[OF bz] evzero])
      have neq: "S q \<noteq> 0"
        by (rule sucNonZero[OF q])
      show ?thesis
        by (rule sat_fuel_formula_neqI[OF f A natS[OF q] nat0 tg eva evb neq])
    next
      assume n2: "\<not> (tag_T ?a = T_SUC \<and> ?b = ?z \<and> mem (?G \<tturnstile> pack_F F_EQ \<langle>?la, ?la\<rangle>) rest)"
      have R2: "if tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and> mem (?G \<tturnstile> pack_F F_NEQ \<langle>?la, ?lb\<rangle>) rest then True
        else if mem (?G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest then True
        else False"
        using n2 R1 by (rule notcond_thenE)
      show ?thesis
      proof (rule cases_bool[where q="tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and> mem (?G \<tturnstile> pack_F F_NEQ \<langle>?la, ?lb\<rangle>) rest"])
        show "(tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and> mem (?G \<tturnstile> pack_F F_NEQ \<langle>?la, ?lb\<rangle>) rest) B"
          by (rule g3B)
      next
        assume g3: "tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and> mem (?G \<tturnstile> pack_F F_NEQ \<langle>?la, ?lb\<rangle>) rest"
        have g3l: "tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC"
          by (rule conjE1[OF g3])
        have m: "mem (?G \<tturnstile> pack_F F_NEQ \<langle>?la, ?lb\<rangle>) rest"
          by (rule conjE2[OF g3])
        have tagaS: "tag_T ?a = T_SUC"
          by (rule conjE1[OF g3l])
        have tagbS: "tag_T ?b = T_SUC"
          by (rule conjE2[OF g3l])
        obtain x y where x: "x N" and y: "y N" and evla: "evals ?la A x" and evlb: "evals ?lb A y" and xy: "x \<noteq> y"
          by (rule neq_prem_fuel[OF G rest la lb A m prev satG])
        have eva: "evals ?a A (S x)"
          by (rule evals_suc_tagI[OF a A x tagaS evla])
        have evb: "evals ?b A (S y)"
          by (rule evals_suc_tagI[OF b A y tagbS evlb])
        have sxy: "S x \<noteq> S y"
          by (rule neq_monotone_suc[OF x y xy[unfolded neq_def], folded neq_def])
        show ?thesis
          by (rule sat_fuel_formula_neqI[OF f A natS[OF x] natS[OF y] tg eva evb sxy])
      next
        assume n3: "\<not> (tag_T ?a = T_SUC \<and> tag_T ?b = T_SUC \<and> mem (?G \<tturnstile> pack_F F_NEQ \<langle>?la, ?lb\<rangle>) rest)"
        have R3: "if mem (?G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest then True else False"
          using n3 R2 by (rule notcond_thenE)
        show ?thesis
        proof (rule cases_bool[where q="mem (?G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest"])
          show "mem (?G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest B"
            by (rule g4B)
        next
          assume g4: "mem (?G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest"
          obtain u v where u: "u N" and v: "v N" and evsa: "evals (pack_T T_SUC ?a) A u"
              and evsb: "evals (pack_T T_SUC ?b) A v" and uv: "u \<noteq> v"
            by (rule neq_prem_fuel[OF G rest suca sucb A g4 prev satG])
          obtain x where x: "x N" and eva: "evals ?a A x" and ux: "u = S x"
            by (rule evals_sucE[OF a A evsa])
          obtain y where y: "y N" and evb: "evals ?b A y" and vy: "v = S y"
            by (rule evals_sucE[OF b A evsb])
          have sxv: "S x \<noteq> v"
            by (rule eqSubst[where a=u and b="S x" and Q="\<lambda>w. w \<noteq> v", OF ux uv])
          have sxy: "S x \<noteq> S y"
            by (rule eqSubst[where a=v and b="S y" and Q="\<lambda>w. S x \<noteq> w", OF vy sxv])
          have eqB: "(x = y) B"
            by (rule eqBool[OF x y])
          have xy: "x \<noteq> y"
          proof (rule cases_bool[where q="x = y"])
            show "(x = y) B"
              by (rule eqB)
          next
            assume eq: "x = y"
            have seq: "S x = S y"
              by (rule sucCong[OF eq])
            show "x \<noteq> y"
              by (rule exF[OF seq sxy[unfolded neq_def]])
          next
            assume neq: "\<not> x = y"
            show "x \<noteq> y"
              unfolding neq_def by (rule neq)
          qed
          show ?thesis
            by (rule sat_fuel_formula_neqI[OF f A x y tg eva evb xy])
        next
          assume n4: "\<not> mem (?G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC ?a, pack_T T_SUC ?b\<rangle>) rest"
          have bot: "False"
            using n4 R3 by (rule notcond_thenE)
          have contra: "S 0 = 0"
            by (rule bot[unfolded False_def])
          show ?thesis
            by (rule exF[OF contra sucNonZero[OF nat0, unfolded neq_def]])
        qed
      qed
    qed
  qed
qed

lemma valid_step_sound_fuel:
  assumes J: "J N" and rest: "rest N" and A: "A N"
      and vs: "valid_step J rest"
      and prev:
        "\<And>K A2. A2 N \<Longrightarrow> K N \<Longrightarrow> mem K rest \<Longrightarrow>
          sat_hyp_fuel (hyp_of K) A2 \<Longrightarrow>
          sat_fuel (conc_of K) A2"
      and satG: "sat_hyp_fuel (hyp_of J) A"
  shows "sat_fuel (conc_of J) A"
proof -
  have cJ: "conc_of J N"
    using J by simp
  have hJ: "hyp_of J N"
    using J by simp
  have feqN: "F_EQ N"
    by simp
  have prevA:
    "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
      sat_hyp_fuel (hyp_of K) A \<Longrightarrow>
      sat_fuel (conc_of K) A"
  proof -
    fix K
    assume K: "K N" and mK: "mem K rest"
        and satK: "sat_hyp_fuel (hyp_of K) A"
    show "sat_fuel (conc_of K) A"
      by (rule prev[OF A K mK satK])
  qed
  have R0:
    "if mem (conc_of J) (hyp_of J) then True
     else if check_cut J rest then True
     else if check_subst J rest then True
     else if check_ind J rest then True
     else if check_app J rest then True
     else if check_struct J rest then True
     else if tag_F (conc_of J) = F_EQ then
       check_eq_rules (hyp_of J)
         (cpx (load_F (conc_of J)))
         (cpy (load_F (conc_of J)))
         (tag_T (cpx (load_F (conc_of J))))
         (tag_T (cpy (load_F (conc_of J)))) rest
     else
       check_neq_rules (hyp_of J)
         (cpx (load_F (conc_of J)))
         (cpy (load_F (conc_of J)))
         (tag_T (cpx (load_F (conc_of J))))
         (tag_T (cpy (load_F (conc_of J)))) rest"
    using vs
    by (rule defI[OF valid_step_def])
  show ?thesis
  proof (rule cases_bool[
      where q="mem (conc_of J) (hyp_of J)"])
    show "mem (conc_of J) (hyp_of J) B"
      by (rule mem_bool[OF cJ hJ])
  next
    assume g0: "mem (conc_of J) (hyp_of J)"
    show ?thesis
      by (rule sat_hyp_fuel_mem[OF cJ g0 satG])
  next
    assume n0: "\<not> mem (conc_of J) (hyp_of J)"
    have R1:
      "if check_cut J rest then True
       else if check_subst J rest then True
       else if check_ind J rest then True
       else if check_app J rest then True
       else if check_struct J rest then True
       else if tag_F (conc_of J) = F_EQ then
         check_eq_rules (hyp_of J)
           (cpx (load_F (conc_of J)))
           (cpy (load_F (conc_of J)))
           (tag_T (cpx (load_F (conc_of J))))
           (tag_T (cpy (load_F (conc_of J)))) rest
       else
         check_neq_rules (hyp_of J)
           (cpx (load_F (conc_of J)))
           (cpy (load_F (conc_of J)))
           (tag_T (cpx (load_F (conc_of J))))
           (tag_T (cpy (load_F (conc_of J)))) rest"
      using n0 R0 by (rule notcond_thenE)
    show ?thesis
    proof (rule cases_bool[where q="check_cut J rest"])
      show "check_cut J rest B"
        by (rule check_cut_bool[OF J rest])
    next
      assume g1: "check_cut J rest"
      show ?thesis
        by (rule check_cut_sound_fuel[
              OF J rest A g1 prevA satG])
    next
      assume n1: "\<not> check_cut J rest"
      have R2:
        "if check_subst J rest then True
         else if check_ind J rest then True
         else if check_app J rest then True
         else if check_struct J rest then True
         else if tag_F (conc_of J) = F_EQ then
           check_eq_rules (hyp_of J)
             (cpx (load_F (conc_of J)))
             (cpy (load_F (conc_of J)))
             (tag_T (cpx (load_F (conc_of J))))
             (tag_T (cpy (load_F (conc_of J)))) rest
         else
           check_neq_rules (hyp_of J)
             (cpx (load_F (conc_of J)))
             (cpy (load_F (conc_of J)))
             (tag_T (cpx (load_F (conc_of J))))
             (tag_T (cpy (load_F (conc_of J)))) rest"
        using n1 R1 by (rule notcond_thenE)
      show ?thesis
      proof (rule cases_bool[where q="check_subst J rest"])
        show "check_subst J rest B"
          by (rule check_subst_bool[OF J rest])
      next
        assume g2: "check_subst J rest"
        show ?thesis
          by (rule check_subst_sound_fuel[
                OF J rest A g2 prevA satG])
      next
        assume n2: "\<not> check_subst J rest"
        have R3:
          "if check_ind J rest then True
           else if check_app J rest then True
           else if check_struct J rest then True
           else if tag_F (conc_of J) = F_EQ then
             check_eq_rules (hyp_of J)
               (cpx (load_F (conc_of J)))
               (cpy (load_F (conc_of J)))
               (tag_T (cpx (load_F (conc_of J))))
               (tag_T (cpy (load_F (conc_of J)))) rest
           else
             check_neq_rules (hyp_of J)
               (cpx (load_F (conc_of J)))
               (cpy (load_F (conc_of J)))
               (tag_T (cpx (load_F (conc_of J))))
               (tag_T (cpy (load_F (conc_of J)))) rest"
          using n2 R2 by (rule notcond_thenE)
        show ?thesis
        proof (rule cases_bool[where q="check_ind J rest"])
          show "check_ind J rest B"
            by (rule check_ind_bool[OF J rest])
        next
          assume g3: "check_ind J rest"
          show ?thesis
            by (rule check_ind_sound_fuel[
                  OF J rest A g3 prev satG])
        next
          assume n3: "\<not> check_ind J rest"
          have R4:
            "if check_app J rest then True
             else if check_struct J rest then True
             else if tag_F (conc_of J) = F_EQ then
               check_eq_rules (hyp_of J)
                 (cpx (load_F (conc_of J)))
                 (cpy (load_F (conc_of J)))
                 (tag_T (cpx (load_F (conc_of J))))
                 (tag_T (cpy (load_F (conc_of J)))) rest
             else
               check_neq_rules (hyp_of J)
                 (cpx (load_F (conc_of J)))
                 (cpy (load_F (conc_of J)))
                 (tag_T (cpx (load_F (conc_of J))))
                 (tag_T (cpy (load_F (conc_of J)))) rest"
            using n3 R3 by (rule notcond_thenE)
          show ?thesis
          proof (rule cases_bool[where q="check_app J rest"])
            show "check_app J rest B"
              by (rule check_app_bool[OF J rest])
          next
            assume g4: "check_app J rest"
            show ?thesis
              by (rule check_app_sound_fuel[
                    OF J rest A g4 prevA satG])
          next
            assume n4: "\<not> check_app J rest"
            have R5:
              "if check_struct J rest then True
               else if tag_F (conc_of J) = F_EQ then
                 check_eq_rules (hyp_of J)
                   (cpx (load_F (conc_of J)))
                   (cpy (load_F (conc_of J)))
                   (tag_T (cpx (load_F (conc_of J))))
                   (tag_T (cpy (load_F (conc_of J)))) rest
               else
                 check_neq_rules (hyp_of J)
                   (cpx (load_F (conc_of J)))
                   (cpy (load_F (conc_of J)))
                   (tag_T (cpx (load_F (conc_of J))))
                   (tag_T (cpy (load_F (conc_of J)))) rest"
              using n4 R4 by (rule notcond_thenE)
            show ?thesis
            proof (rule cases_bool[
                where q="check_struct J rest"])
              show "check_struct J rest B"
                by (rule check_struct_bool[OF J rest])
            next
              assume g5: "check_struct J rest"
              show ?thesis
                by (rule check_struct_sound_fuel[
                      OF J rest A g5 prevA satG])
            next
              assume n5: "\<not> check_struct J rest"
              have R6:
                "if tag_F (conc_of J) = F_EQ then
                   check_eq_rules (hyp_of J)
                     (cpx (load_F (conc_of J)))
                     (cpy (load_F (conc_of J)))
                     (tag_T (cpx (load_F (conc_of J))))
                     (tag_T (cpy (load_F (conc_of J)))) rest
                 else
                   check_neq_rules (hyp_of J)
                     (cpx (load_F (conc_of J)))
                     (cpy (load_F (conc_of J)))
                     (tag_T (cpx (load_F (conc_of J))))
                     (tag_T (cpy (load_F (conc_of J)))) rest"
                using n5 R5 by (rule notcond_thenE)
              show ?thesis
              proof (rule cases_bool[
                  where q="tag_F (conc_of J) = F_EQ"])
                show "(tag_F (conc_of J) = F_EQ) B"
                  by (rule eqBool[
                        OF tag_F_N[OF cJ] feqN])
              next
                assume g6: "tag_F (conc_of J) = F_EQ"
                have C6:
                  "check_eq_rules (hyp_of J)
                    (cpx (load_F (conc_of J)))
                    (cpy (load_F (conc_of J)))
                    (tag_T (cpx (load_F (conc_of J))))
                    (tag_T (cpy (load_F (conc_of J)))) rest"
                  using g6 R6 by (rule cond_thenE)
                show ?thesis
                  by (rule check_eq_rules_sound_fuel[
                        OF J rest A g6 C6 prevA satG])
              next
                assume n6: "\<not> tag_F (conc_of J) = F_EQ"
                have C6:
                  "check_neq_rules (hyp_of J)
                    (cpx (load_F (conc_of J)))
                    (cpy (load_F (conc_of J)))
                    (tag_T (cpx (load_F (conc_of J))))
                    (tag_T (cpy (load_F (conc_of J)))) rest"
                  using n6 R6 by (rule notcond_thenE)
                show ?thesis
                  by (rule check_neq_rules_sound_fuel[OF J rest A n6 C6 prevA satG])
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma check_list_induct_N:
  assumes pf: "pf N"
      and base: "\<And>J A. A N \<Longrightarrow> check_list Nil \<Longrightarrow> J N \<Longrightarrow> mem J Nil \<Longrightarrow>
                   sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
      and step: "\<And>h t. h N \<Longrightarrow> t N \<Longrightarrow>
                   (\<And>J A. A N \<Longrightarrow> check_list t \<Longrightarrow> J N \<Longrightarrow> mem J t \<Longrightarrow>
                      sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A) \<Longrightarrow>
                   (\<And>J A. A N \<Longrightarrow> check_list (Cons h t) \<Longrightarrow>
                      J N \<Longrightarrow> mem J (Cons h t) \<Longrightarrow>
                      sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A)"
  shows "\<And>J A. A N \<Longrightarrow> check_list pf \<Longrightarrow> J N \<Longrightarrow> mem J pf \<Longrightarrow>
                sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
proof -
  have all: "\<forall>A. \<forall>K. check_list pf \<turnstile> (mem K pf \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
  proof (rule list_induct[OF pf])
    show "\<forall>A. \<forall>K. check_list Nil \<turnstile> (mem K Nil \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
    proof (rule forallI) 
      fix A
      assume A: "A N"
      show "\<forall>K. check_list Nil \<turnstile> (mem K Nil \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
      proof (rule forallI)
        fix K
        assume K: "K N"
        show "check_list Nil \<turnstile> (mem K Nil \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
        proof (rule entailsI)
          assume chk0: "check_list Nil"
          show "mem K Nil \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A)"
          proof (rule entailsI)
            assume Km: "mem K Nil"
            show "sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A"
            proof (rule entailsI)
              assume satK: "sat_hyp (hyp_of K) A"
              show "sat (conc_of K) A"
                using A chk0 K Km satK by (rule base)
            qed
          qed
        qed
      qed
    qed
  next
    fix h t
    assume h: "h N"
       and t: "t N"
       and IH: "\<forall>A. \<forall>K. check_list t \<turnstile> (mem K t \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
    show "\<forall>A. \<forall>K. check_list (Cons h t) \<turnstile> (mem K (Cons h t) \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
    proof (rule forallI)
      fix A
      assume A: "A N"
      show "\<forall>K. check_list (Cons h t) \<turnstile> (mem K (Cons h t) \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
      proof (rule forallI)
        fix K
        assume K: "K N"
        show "check_list (Cons h t) \<turnstile> (mem K (Cons h t) \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
        proof (rule entailsI)
          assume chkht: "check_list (Cons h t)"
          show "mem K (Cons h t) \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A)"
          proof (rule entailsI)
            assume Km: "mem K (Cons h t)"
            show "sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A"
            proof (rule entailsI)
              assume satK: "sat_hyp (hyp_of K) A"
              have tail:
                "\<And>L A2. A2 N \<Longrightarrow> check_list t \<Longrightarrow> L N \<Longrightarrow> mem L t \<Longrightarrow>
                   sat_hyp (hyp_of L) A2 \<Longrightarrow> sat (conc_of L) A2"
              proof -
                fix L A2
                assume A2: "A2 N"
                   and chkt: "check_list t"
                   and L: "L N"
                   and Lm: "mem L t"
                   and satL: "sat_hyp (hyp_of L) A2"
                have IA:
                  "\<forall>K. check_list t \<turnstile>
                     (mem K t \<turnstile>
                       (sat_hyp (hyp_of K) A2 \<turnstile> sat (conc_of K) A2))"
                  using IH A2 by (rule forallE)
                have LI:
                  "check_list t \<turnstile>
                    (mem L t \<turnstile>
                      (sat_hyp (hyp_of L) A2 \<turnstile> sat (conc_of L) A2))"
                  using IA L by (rule forallE)
                have LI1: "mem L t \<turnstile> (sat_hyp (hyp_of L) A2 \<turnstile> sat (conc_of L) A2)"
                  using LI chkt by (rule entailsE)
                have LI2: "sat_hyp (hyp_of L) A2 \<turnstile> sat (conc_of L) A2"
                  using LI1 Lm by (rule entailsE)
                show "sat (conc_of L) A2"
                  using LI2 satL by (rule entailsE)
              qed
              show "sat (conc_of K) A"
                using h t tail A chkht K Km satK by (rule step)
            qed
          qed
        qed
      qed
    qed
  qed
  fix J A
  assume A: "A N"
     and chk: "check_list pf"
     and J: "J N"
     and Jm: "mem J pf"
     and satG: "sat_hyp (hyp_of J) A"
  have IA: 
    "\<forall>K. check_list pf \<turnstile> (mem K pf \<turnstile> (sat_hyp (hyp_of K) A \<turnstile> sat (conc_of K) A))"
    using all A by (rule forallE)
  have one:
    "check_list pf \<turnstile>
      (mem J pf \<turnstile>
        (sat_hyp (hyp_of J) A \<turnstile> sat (conc_of J) A))"
    using IA J by (rule forallE)
  have two:
    "mem J pf \<turnstile>
      (sat_hyp (hyp_of J) A \<turnstile> sat (conc_of J) A)"
    using one chk by (rule entailsE)
  have three:
    "sat_hyp (hyp_of J) A \<turnstile> sat (conc_of J) A"
    using two Jm by (rule entailsE)
  show "sat (conc_of J) A"
    using three satG by (rule entailsE)
qed

lemma check_eq_rules_bool [auto]:
  assumes G: "G N" and lhs: "lhs N" and rhs: "rhs N"
      and tg_L: "tg_L N" and tg_R: "tg_R N" and rest: "rest N"
  shows "check_eq_rules G lhs rhs tg_L tg_R rest B"
proof -
  have sucN: "T_SUC N" 
    by simp
  have predN: "T_PRED N" 
    by simp
  have ifzN: "T_IFZ N" 
    by simp
  have ztz: "pack_T T_ZERO 0 N" 
    by (rule pack_T_N[OF _ nat0], simp)
  have Ll: "load_T lhs N" 
    by (rule load_T_N[OF lhs])
  have Lr: "load_T rhs N" 
    by (rule load_T_N[OF rhs])
  have LLl: "load_T (load_T lhs) N" 
    by (rule load_T_N[OF Ll])
  have cxLLl: "cpx (load_T (load_T lhs)) N" 
    by (rule cpx_terminates[OF LLl])
  have cyLl: "cpy (load_T lhs) N" 
    by (rule cpy_terminates[OF Ll])
  have cycyLl: "cpy (cpy (load_T lhs)) N" 
    by (rule cpy_terminates[OF cyLl])
  have cxcyLl: "cpx (cpy (load_T lhs)) N" 
    by (rule cpx_terminates[OF cyLl])
  have cxLl: "cpx (load_T lhs) N" 
    by (rule cpx_terminates[OF Ll])
  have sucl: "pack_T T_SUC lhs N" 
    by (rule pack_T_N[OF _ lhs], simp)
  have sucr: "pack_T T_SUC rhs N" 
    by (rule pack_T_N[OF _ rhs], simp)
  have tgLL: "tag_T (load_T lhs) N" 
    by (rule tag_T_N[OF Ll])

  have e_lz: "(lhs = pack_T T_ZERO 0) B" 
    by (rule eqBool[OF lhs ztz])
  have e_rz: "(rhs = pack_T T_ZERO 0) B" 
    by (rule eqBool[OF rhs ztz])
  have g1: "(lhs = pack_T T_ZERO 0 \<and> rhs = pack_T T_ZERO 0) B" 
    using e_lz e_rz by auto

  have pr_rl: "\<langle>rhs, lhs\<rangle> N" 
    using rhs lhs by simp
  have pf2: "pack_F F_EQ \<langle>rhs, lhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_rl], simp)
  have j2: "(G \<tturnstile> pack_F F_EQ \<langle>rhs, lhs\<rangle>) N" 
    using G pf2 by simp
  have g2: "mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, lhs\<rangle>) rest B" 
    by (rule mem_bool[OF j2 rest])

  have pr_LlLr: "\<langle>load_T lhs, load_T rhs\<rangle> N" 
    using Ll Lr by simp
  have pf3: "pack_F F_EQ \<langle>load_T lhs, load_T rhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_LlLr], simp)
  have j3: "(G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T rhs\<rangle>) N" 
    using G pf3 by simp
  have m3: "mem (G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T rhs\<rangle>) rest B" 
    by (rule mem_bool[OF j3 rest])
  have e_tgLs: "(tg_L = T_SUC) B" 
    by (rule eqBool[OF tg_L sucN])
  have e_tgRs: "(tg_R = T_SUC) B" 
    by (rule eqBool[OF tg_R sucN])
  have g3: "(tg_L = T_SUC \<and> tg_R = T_SUC \<and>
             mem (G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T rhs\<rangle>) rest) B"
    using e_tgLs e_tgRs m3 by auto

  have pr_ss: "\<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle> N" 
    using sucl sucr by simp
  have pf4: "pack_F F_EQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_ss], simp)
  have j4: "(G \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle>) N" 
    using G pf4 by simp
  have g4: "mem (G \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle>) rest B"
    by (rule mem_bool[OF j4 rest])

  have pr_rr: "\<langle>rhs, rhs\<rangle> N" 
    using rhs by simp
  have pfrr: "pack_F F_EQ \<langle>rhs, rhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_rr], simp)
  have jrr: "(G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) N" 
    using G pfrr by simp
  have mrr: "mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) rest B" 
    by (rule mem_bool[OF jrr rest])

  have e_tgLp: "(tg_L = T_PRED) B" 
    by (rule eqBool[OF tg_L predN])
  have e_tgLLs: "(tag_T (load_T lhs) = T_SUC) B" 
    by (rule eqBool[OF tgLL sucN])
  have e_cx_r: "(load_T (load_T lhs) = rhs) B" 
    by (rule eqBool[OF LLl rhs])
  have g5: "(tg_L = T_PRED \<and> tag_T (load_T lhs) = T_SUC \<and>
             (load_T (load_T lhs)) = rhs \<and>
             mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) rest) B"
    using e_tgLp e_tgLLs e_cx_r mrr by auto

  have pr_cxZ: "\<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle> N" 
    using cxLl ztz by simp
  have pf_neq_cxZ: "pack_F F_NEQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle> N"
    by (rule pack_F_N[OF _ pr_cxZ], simp)
  have j_neq_cxZ: "(G \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) N"
    using G pf_neq_cxZ by simp
  have m6a: "mem (G \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) rest B"
    by (rule mem_bool[OF j_neq_cxZ rest])
  have pf_eq_cxZ: "pack_F F_EQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle> N"
    by (rule pack_F_N[OF _ pr_cxZ], simp)
  have j_eq_cxZ: "(G \<tturnstile> pack_F F_EQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) N"
    using G pf_eq_cxZ by simp
  have m7a: "mem (G \<tturnstile> pack_F F_EQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) rest B"
    by (rule mem_bool[OF j_eq_cxZ rest])

  have e_tgLi: "(tg_L = T_IFZ) B" 
    by (rule eqBool[OF tg_L ifzN])
  have e_r_cycy: "(rhs = cpy (cpy (load_T lhs))) B" 
    by (rule eqBool[OF rhs cycyLl])
  have g6: "(tg_L = T_IFZ \<and> rhs = cpy (cpy (load_T lhs)) \<and>
             mem (G \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) rest \<and>
             mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) rest) B"
    using e_tgLi e_r_cycy m6a mrr by auto

  have e_r_cxcy: "(rhs = cpx (cpy (load_T lhs))) B" 
    by (rule eqBool[OF rhs cxcyLl])
  have g7: "(tg_L = T_IFZ \<and> rhs = cpx (cpy (load_T lhs)) \<and>
             mem (G \<tturnstile> pack_F F_EQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) rest \<and>
             mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) rest) B"
    using e_tgLi e_r_cxcy m7a mrr by auto

  show ?thesis
    apply (rule defE[OF check_eq_rules_def[where G=G and lhs=lhs and rhs=rhs
                                             and tg_L=tg_L and tg_R=tg_R and rest=rest]])
    apply (rule condTB[OF g1 true_bool])
    apply (rule condTB[OF g2 true_bool])
    apply (rule condTB[OF g3 true_bool])
    apply (rule condTB[OF g4 true_bool])
    apply (rule condTB[OF g5 true_bool])
    apply (rule condTB[OF g6 true_bool])
    apply (rule condTB[OF g7 true_bool false_bool])
    done
qed

lemma check_neq_rules_bool [auto]:
  assumes G: "G N" and lhs: "lhs N" and rhs: "rhs N"
      and tg_L: "tg_L N" and tg_R: "tg_R N" and rest: "rest N"
  shows "check_neq_rules G lhs rhs tg_L tg_R rest B"
proof -
  have sucN: "T_SUC N" 
    by simp
  have ztz: "pack_T T_ZERO 0 N" 
    by (rule pack_T_N[OF _ nat0], simp)
  have Ll: "load_T lhs N" 
    by (rule load_T_N[OF lhs])
  have Lr: "load_T rhs N" 
    by (rule load_T_N[OF rhs])
  have sucl: "pack_T T_SUC lhs N" 
    by (rule pack_T_N[OF _ lhs], simp)
  have sucr: "pack_T T_SUC rhs N" 
    by (rule pack_T_N[OF _ rhs], simp)
  have pr_rl: "\<langle>rhs, lhs\<rangle> N" 
    using rhs lhs by simp
  have pf1: "pack_F F_NEQ \<langle>rhs, lhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_rl], simp)
  have j1: "(G \<tturnstile> pack_F F_NEQ \<langle>rhs, lhs\<rangle>) N" 
    using G pf1 by simp
  have g1: "mem (G \<tturnstile> pack_F F_NEQ \<langle>rhs, lhs\<rangle>) rest B" 
    by (rule mem_bool[OF j1 rest])
  have pr_ll: "\<langle>load_T lhs, load_T lhs\<rangle> N" 
    using Ll by simp
  have pf2: "pack_F F_EQ \<langle>load_T lhs, load_T lhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_ll], simp)
  have j2: "(G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T lhs\<rangle>) N" 
    using G pf2 by simp
  have m2: "mem (G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T lhs\<rangle>) rest B" 
    by (rule mem_bool[OF j2 rest])
  have e_tgLs: "(tg_L = T_SUC) B" 
    by (rule eqBool[OF tg_L sucN])
  have e_rz: "(rhs = pack_T T_ZERO 0) B" 
    by (rule eqBool[OF rhs ztz])
  have g2: "(tg_L = T_SUC \<and> rhs = pack_T T_ZERO 0 \<and>
             mem (G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T lhs\<rangle>) rest) B"
    using e_tgLs e_rz m2 by auto

  have pr_lr: "\<langle>load_T lhs, load_T rhs\<rangle> N" 
    using Ll Lr by simp
  have pf3: "pack_F F_NEQ \<langle>load_T lhs, load_T rhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_lr], simp)
  have j3: "(G \<tturnstile> pack_F F_NEQ \<langle>load_T lhs, load_T rhs\<rangle>) N" 
    using G pf3 by simp
  have m3: "mem (G \<tturnstile> pack_F F_NEQ \<langle>load_T lhs, load_T rhs\<rangle>) rest B" 
    by (rule mem_bool[OF j3 rest])
  have e_tgRs: "(tg_R = T_SUC) B" 
    by (rule eqBool[OF tg_R sucN])
  have g3: "(tg_L = T_SUC \<and> tg_R = T_SUC \<and>
             mem (G \<tturnstile> pack_F F_NEQ \<langle>load_T lhs, load_T rhs\<rangle>) rest) B"
    using e_tgLs e_tgRs m3 by auto

  have pr_ss: "\<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle> N" 
    using sucl sucr by simp
  have pf4: "pack_F F_NEQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle> N" 
    by (rule pack_F_N[OF _ pr_ss], simp)
  have j4: "(G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle>) N" 
    using G pf4 by simp
  have g4: "mem (G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle>) rest B"
    by (rule mem_bool[OF j4 rest])

  show ?thesis
    apply (rule defE[OF check_neq_rules_def[where G=G and lhs=lhs and rhs=rhs
                                             and tg_L=tg_L and tg_R=tg_R and rest=rest]])
    apply (rule condTB[OF g1 true_bool])
    apply (rule condTB[OF g2 true_bool])
    apply (rule condTB[OF g3 true_bool])
    apply (rule condTB[OF g4 true_bool false_bool])
    done
qed

lemma valid_step_bool [auto]:
  assumes J: "J N" and r: "rest N"
  shows "valid_step J rest B"
proof -
  have cJ: "conc_of J N" 
    using J by simp
  have hj: "hyp_of J N" 
    using J by simp
  have LcJ: "load_F (conc_of J) N" 
    by (rule load_F_N[OF cJ])
  have cx: "cpx (load_F (conc_of J)) N" 
    by (rule cpx_terminates[OF LcJ])
  have cy: "cpy (load_F (conc_of J)) N" 
    by (rule cpy_terminates[OF LcJ])
  have tgx: "tag_T (cpx (load_F (conc_of J))) N" 
    by (rule tag_T_N[OF cx])
  have tgy: "tag_T (cpy (load_F (conc_of J))) N" 
    by (rule tag_T_N[OF cy])
  have feqN: "F_EQ N" 
    by simp

  have g1: "mem (conc_of J) (hyp_of J) B" 
    by (rule mem_bool[OF cJ hj])
  have g2: "check_cut J rest B" 
    by (rule check_cut_bool[OF J r])
  have g3: "check_subst J rest B" 
    by (rule check_subst_bool[OF J r])
  have g4: "check_ind J rest B" 
    by (rule check_ind_bool[OF J r])
  have g5: "check_app J rest B" 
    by (rule check_app_bool[OF J r])
  have g6: "check_struct J rest B" 
    by (rule check_struct_bool[OF J r])
  have g7: "(tag_F (conc_of J) = F_EQ) B" 
    by (rule eqBool[OF tag_F_N[OF cJ] feqN])
  have beq: "check_eq_rules (hyp_of J) (cpx (load_F (conc_of J))) (cpy (load_F (conc_of J)))
               (tag_T (cpx (load_F (conc_of J)))) (tag_T (cpy (load_F (conc_of J)))) rest B"
    by (rule check_eq_rules_bool[OF hj cx cy tgx tgy r])
  have bneq: "check_neq_rules (hyp_of J) (cpx (load_F (conc_of J))) (cpy (load_F (conc_of J)))
               (tag_T (cpx (load_F (conc_of J)))) (tag_T (cpy (load_F (conc_of J)))) rest B"
    by (rule check_neq_rules_bool[OF hj cx cy tgx tgy r])

  show ?thesis
    apply (rule defE[OF valid_step_def[where J=J and rest=rest]])
    apply (rule condTB[OF g1 true_bool])
    apply (rule condTB[OF g2 true_bool])
    apply (rule condTB[OF g3 true_bool])
    apply (rule condTB[OF g4 true_bool])
    apply (rule condTB[OF g5 true_bool])
    apply (rule condTB[OF g6 true_bool])
    apply (rule condTB[OF g7 beq bneq])
    done
qed

lemma check_list_sound_fuel_N:
  assumes pf: "pf N"
  shows "\<And>J A. A N \<Longrightarrow> check_list pf \<Longrightarrow>
    J N \<Longrightarrow> mem J pf \<Longrightarrow>
    sat_hyp_fuel (hyp_of J) A \<Longrightarrow>
    sat_fuel (conc_of J) A"
proof (rule check_list_induct_N[OF pf])
  show "\<And>J A. A N \<Longrightarrow> check_list Nil \<Longrightarrow>
    J N \<Longrightarrow> mem J Nil \<Longrightarrow>
    sat_hyp_fuel (hyp_of J) A \<Longrightarrow>
    sat_fuel (conc_of J) A"
  proof -
    fix J A
    assume A: "A N" and chk: "check_list Nil"
        and J: "J N" and m: "mem J Nil"
        and satG: "sat_hyp_fuel (hyp_of J) A"
    show "sat_fuel (conc_of J) A"
      by (rule exF[OF m mem_nil])
  qed
next
  fix h t
  assume h: "h N" and t: "t N"
      and IH:
        "\<And>J A. A N \<Longrightarrow> check_list t \<Longrightarrow>
          J N \<Longrightarrow> mem J t \<Longrightarrow>
          sat_hyp_fuel (hyp_of J) A \<Longrightarrow>
          sat_fuel (conc_of J) A"
  show "\<And>J A. A N \<Longrightarrow> check_list (Cons h t) \<Longrightarrow>
    J N \<Longrightarrow> mem J (Cons h t) \<Longrightarrow>
    sat_hyp_fuel (hyp_of J) A \<Longrightarrow>
    sat_fuel (conc_of J) A"
  proof -
    fix J A
    assume A: "A N"
        and cl: "check_list (Cons h t)"
        and J: "J N"
        and mJ: "mem J (Cons h t)"
        and satG: "sat_hyp_fuel (hyp_of J) A"
    have hne: "\<not> Cons h t = Nil"
      using h t by simp
    have R0:
      "if Cons h t = Nil then True
       else if valid_step
         (list_hd (Cons h t)) (list_tl (Cons h t))
       then check_list (list_tl (Cons h t))
       else False"
      using cl
      by (rule defI[OF check_list_def[
            where pf="Cons h t"]])
    have R:
      "if Cons h t = Nil then True
       else if valid_step h t then check_list t
       else False"
      using R0
      by (simp only:
            list_hd_cons[OF h t]
            list_tl_cons[OF h t])
    have R1:
      "if valid_step h t then check_list t else False"
      using hne R by (rule notcond_thenE)
    show "sat_fuel (conc_of J) A"
    proof (rule cases_bool[where q="valid_step h t"])
      show "valid_step h t B"
        by (rule valid_step_bool[OF h t])
    next
      assume vs: "valid_step h t"
      have clt: "check_list t"
        using vs R1 by (rule cond_thenE)
      have mJ':
        "if h = J then True else mem J t"
        using mJ h t J
        by (simp add: mem_cons[OF h t J])
      show "sat_fuel (conc_of J) A"
      proof (rule cases_bool[where q="h = J"])
        show "(h = J) B"
          by (rule eqBool[OF h J])
      next
        assume hJ: "h = J"
        have Jh: "J = h"
          by (rule eqSym[OF hJ])
        have satGh: "sat_hyp_fuel (hyp_of h) A"
          using Jh satG
          by (rule eqSubst[
                where Q="\<lambda>z.
                  sat_hyp_fuel (hyp_of z) A"])
        have sh: "sat_fuel (conc_of h) A"
        proof (rule valid_step_sound_fuel[
            OF h t A vs])
          fix K A2
          assume A2: "A2 N" and K: "K N"
              and mK: "mem K t"
              and satK:
                "sat_hyp_fuel (hyp_of K) A2"
          show "sat_fuel (conc_of K) A2"
            by (rule IH[OF A2 clt K mK satK])
        next
          show "sat_hyp_fuel (hyp_of h) A"
            by (rule satGh)
        qed
        show "sat_fuel (conc_of J) A"
          using hJ sh
          by (rule eqSubst[
                where Q="\<lambda>z.
                  sat_fuel (conc_of z) A"])
      next
        assume nhJ: "\<not> h = J"
        have mJt: "mem J t"
          using nhJ mJ'
          by (rule notcond_thenE)
        show "sat_fuel (conc_of J) A"
          by (rule IH[OF A clt J mJt satG])
      qed
    next
      assume nvs: "\<not> valid_step h t"
      have bot: "False"
        using nvs R1 by (rule notcond_thenE)
      show "sat_fuel (conc_of J) A"
        by (rule exF[OF bot not_false])
    qed
  qed
qed

lemma soundness_bridge_fuel:
  assumes vp: "is_valid_proof p J"
      and satG: "sat_hyp_fuel (hyp_of J) A"
      and AN: "A N"
  shows "sat_fuel (conc_of J) A"
proof -
  have vpB: "is_valid_proof p J B"
    using vp by simp
  have RB: "(if p = Nil then False else if list_hd p = J then check_list p else False) B"
    using vpB by (rule defI[OF is_valid_proof_def])
  have pnilB: "(p = Nil) B"
    by (rule condE3B[OF RB])
  have PN: "(p N) \<and> (Nil N)"
    by (rule eqE[OF pnilB])
  have p: "p N"
    using PN by (rule conjE1)
  have R: "if p = Nil then False else if list_hd p = J then check_list p else False"
    using vp by (rule defI[OF is_valid_proof_def])
  show ?thesis
  proof (rule cases_bool[where q="p = Nil"])
    show "(p = Nil) B"
      by (rule pnilB)
  next
    assume pe: "p = Nil"
    have F: "False"
      using pe R by (rule cond_thenE)
    show ?thesis
      by (rule exF[OF F not_false])
  next
    assume pne: "\<not> p = Nil"
    have inner: "if list_hd p = J then check_list p else False"
      using pne R by (rule notcond_thenE)
    have innerB: "(if list_hd p = J then check_list p else False) B"
      using inner by simp
    have hJB: "(list_hd p = J) B"
      by (rule condE3B[OF innerB])
    have HN: "(list_hd p N) \<and> (J N)"
      by (rule eqE[OF hJB])
    have hN: "list_hd p N"
      using HN by (rule conjE1)
    have JN: "J N"
      using HN by (rule conjE2)
    show ?thesis
    proof (rule cases_bool[where q="list_hd p = J"])
      show "(list_hd p = J) B"
        by (rule hJB)
    next
      assume hJ: "list_hd p = J"
      have cp: "check_list p"
        using hJ inner by (rule cond_thenE)
      have tpN: "list_tl p N"
        by (rule list_tl_nat[OF p])
      have rec: "list_hd p \<triangleright> list_tl p = p"
        by (rule cons_reconstr[OF p pne])
      have mh0: "list_hd p \<in> (list_hd p \<triangleright> list_tl p)"
        by (rule mem_cons_head[OF hN tpN])
      have mh: "list_hd p \<in> p"
        using rec mh0 by (rule eqSubst[where Q="\<lambda>L. list_hd p \<in> L"])
      have mJ: "J \<in> p"
        using hJ mh by (rule eqSubst[where Q="\<lambda>x. x \<in> p"])
      show ?thesis
        using p AN cp JN mJ satG by (rule check_list_sound_fuel_N)
    next
      assume nhJ: "\<not> list_hd p = J"
      have F: "False"
        using nhJ inner by (rule notcond_thenE)
      show ?thesis
        by (rule exF[OF F not_false])
    qed
  qed
qed

definition mk_eq :: "num \<Rightarrow> num \<Rightarrow> num" where
    "mk_eq a b \<equiv> pack_F 0 \<langle>a, b\<rangle>"

definition mk_neq :: "num \<Rightarrow> num \<Rightarrow> num" where
    "mk_neq a b \<equiv> pack_F 1 \<langle>a, b\<rangle>"

lemma mk_eq_N':
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  shows "mk_eq a b N"
  unfolding mk_eq_def  apply (rule pack_F_N)
  using a_nat b_nat  apply simp+
  done

lemma mk_neq_N':
  assumes a: "a N" and b: "b N"
  shows "mk_neq a b N"
proof -
  have ab: "\<langle>a, b\<rangle> N"
    using a b by simp
  show ?thesis
    unfolding mk_neq_def
    by (rule pack_F_N[OF _ ab], simp)
qed

lemma check_list_bool [auto]:
  assumes pfn: "pf N"
  shows "check_list pf B"
proof (rule list_induct[OF pfn])
  show "check_list Nil B"
    apply (rule defE[OF check_list_def[where pf=Nil]])
    apply simp
    done
next
  fix h t assume h: "h N" and t: "t N" and IH: "check_list t B"
  show "check_list (Cons h t) B"
  proof -
    have htN: "h \<triangleright> t N" 
      using h t by simp
    have g0: "(h \<triangleright> t = \<emptyset>) B" 
      apply (rule eqBool[OF htN]) 
      apply simp 
      done
    have vs: "valid_step h t B" 
      by (rule valid_step_bool[OF h t])
    show "check_list (h \<triangleright> t) B"
      apply (rule defE[OF check_list_def[where pf="h \<triangleright> t"]])
      apply (simp only: list_hd_cons[OF h t] list_tl_cons[OF h t])
      apply (rule condTB[OF g0 true_bool])
      apply (rule condTB[OF vs IH false_bool])
      done
  qed
qed

lemma proof_is_bool: "p N \<Longrightarrow> J N \<Longrightarrow> is_valid_proof p J B"
proof -
  assume p: "p N" and J: "J N"
  have g0: "(p = Nil) B" 
    by (rule eqBool[OF p nil_nat])
  have g1: "(list_hd p = J) B" 
    by (rule eqBool[OF list_hd_nat[OF p] J])
  have cl: "check_list p B" 
    by (rule check_list_bool[OF p])
  show "is_valid_proof p J B"
    apply (rule defE[OF is_valid_proof_def[where pf=p and J=J]])
    apply (rule condTB[OF g0 false_bool])
    apply (rule condTB[OF g1 cl false_bool])
    done
qed

lemma sat_fuel_mk_eqE:
  assumes a: "a N" and b: "b N" and sat: "sat_fuel (mk_eq a b) A"
  obtains q where "q N" and "evals a A q" and "evals b A q"
proof -
  have ab: "\<langle>a, b\<rangle> N"
    using a b by simp
  have f: "mk_eq a b N"
    by (rule mk_eq_N'[OF a b])
  have tg: "tag_F (mk_eq a b) = F_EQ"
    unfolding mk_eq_def by (rule tag_pack_F[OF _ ab], simp)
  have ld: "load_F (mk_eq a b) = \<langle>a, b\<rangle>"
    unfolding mk_eq_def by (rule load_pack_F[OF _ ab], simp)
  have pa: "hyp_of \<langle>a, b\<rangle> = a"
    by (rule cpx_proj[OF a b])
  have pb: "conc_of \<langle>a, b\<rangle> = b"
    by (rule cpy_proj[OF a b])
  have leftSel: "hyp_of (load_F (mk_eq a b)) = a"
    by (rule eqSubst[where a="\<langle>a, b\<rangle>" and b="load_F (mk_eq a b)" and Q="\<lambda>z. hyp_of z = a", OF eqSym[OF ld] pa])
  have rightSel: "conc_of (load_F (mk_eq a b)) = b"
    by (rule eqSubst[where a="\<langle>a, b\<rangle>" and b="load_F (mk_eq a b)" and Q="\<lambda>z. conc_of z = b", OF eqSym[OF ld] pb])
  show thesis
    using sat
  proof (rule sat_fuelE)
    fix x y
    assume x: "x N" and y: "y N" and evx0: "evals (hyp_of (load_F (mk_eq a b))) A x"
        and evy0: "evals (conc_of (load_F (mk_eq a b))) A y"
        and rel: "if tag_F (mk_eq a b) = F_EQ then x = y else x \<noteq> y"
    have evx: "evals a A x"
      by (rule eqSubst[where a="hyp_of (load_F (mk_eq a b))" and b=a and Q="\<lambda>t. evals t A x", OF leftSel evx0])
    have evy: "evals b A y"
      by (rule eqSubst[where a="conc_of (load_F (mk_eq a b))" and b=b and Q="\<lambda>t. evals t A y", OF rightSel evy0])
    have xy: "x = y"
      using x y tg rel by simp
    have evb: "evals b A x"
      by (rule eqSubst[where a=y and b=x and Q="\<lambda>q. evals b A q", OF eqSym[OF xy] evy])
    show thesis
      by (rule that[OF x evx evb])
  qed
qed

lemma sat_fuel_mk_neqE:
  assumes a: "a N" and b: "b N" and sat: "sat_fuel (mk_neq a b) A"
  obtains x y where "x N" and "y N" and "evals a A x" and "evals b A y" and "x \<noteq> y"
proof -
  have ab: "\<langle>a, b\<rangle> N"
    using a b by simp
  have f: "mk_neq a b N"
    by (rule mk_neq_N'[OF a b])
  have tg: "tag_F (mk_neq a b) = F_NEQ"
    unfolding mk_neq_def by (rule tag_pack_F[OF _ ab], simp)
  have ntg: "\<not> tag_F (mk_neq a b) = F_EQ"
    using tg by simp
  have ld: "load_F (mk_neq a b) = \<langle>a, b\<rangle>"
    unfolding mk_neq_def by (rule load_pack_F[OF _ ab], simp)
  have pa: "hyp_of \<langle>a, b\<rangle> = a"
    by (rule cpx_proj[OF a b])
  have pb: "conc_of \<langle>a, b\<rangle> = b"
    by (rule cpy_proj[OF a b])
  have leftSel: "hyp_of (load_F (mk_neq a b)) = a"
    by (rule eqSubst[where a="\<langle>a, b\<rangle>" and b="load_F (mk_neq a b)" and Q="\<lambda>z. hyp_of z = a", OF eqSym[OF ld] pa])
  have rightSel: "conc_of (load_F (mk_neq a b)) = b"
    by (rule eqSubst[where a="\<langle>a, b\<rangle>" and b="load_F (mk_neq a b)" and Q="\<lambda>z. conc_of z = b", OF eqSym[OF ld] pb])
  show thesis
    using sat
  proof (rule sat_fuelE)
    fix x y
    assume x: "x N" and y: "y N" and evx0: "evals (hyp_of (load_F (mk_neq a b))) A x"
        and evy0: "evals (conc_of (load_F (mk_neq a b))) A y"
        and rel: "if tag_F (mk_neq a b) = F_EQ then x = y else x \<noteq> y"
    have evx: "evals a A x"
      by (rule eqSubst[where a="hyp_of (load_F (mk_neq a b))" and b=a and Q="\<lambda>t. evals t A x", OF leftSel evx0])
    have evy: "evals b A y"
      by (rule eqSubst[where a="conc_of (load_F (mk_neq a b))" and b=b and Q="\<lambda>t. evals t A y", OF rightSel evy0])
    have xy: "x \<noteq> y"
      using ntg rel by (rule notcond_thenE)
    show thesis
      by (rule that[OF x y evx evy xy])
  qed
qed

lemma syntactically_consistent_fuel:
  assumes a: "a N" and b: "b N" and p1: "p1 N" and p2: "p2 N"
  shows "\<not> (is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>)"
  apply (rule contradiction[where p="\<not> (is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>)"])
   apply simp
proof -
  have eqN: "mk_eq a b N"
    by (rule mk_eq_N'[OF a b])
  have neqN: "mk_neq a b N"
    by (rule mk_neq_N'[OF a b])
  have Jeq: "\<langle>Nil, mk_eq a b\<rangle> N"
    using eqN by simp
  have Jneq: "\<langle>Nil, mk_neq a b\<rangle> N"
    using neqN by simp
  show "is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> B"
    by (rule proof_is_bool[OF p1 Jeq])
  show "is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle> B"
    by (rule proof_is_bool[OF p2 Jneq])
  show "\<not> \<not> (is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>) \<Longrightarrow> False"
  proof -
    assume nn: "\<not> \<not> (is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>)"
    have both: "is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>"
      by (rule dNegE[OF nn])
    have eqpf: "is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle>"
      by (rule conjE1[OF both])
    have neqpf: "is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>"
      by (rule conjE2[OF both])
    have satNil: "sat_hyp_fuel Nil 0"
      by (rule sat_hyp_fuel_nil)
    have nilN: "Nil N"
      by (rule nil_nat)
    have hEq: "hyp_of (Nil \<tturnstile> mk_eq a b) = Nil"
      by (rule cpx_proj[OF nilN eqN])
    have hNeq: "hyp_of (Nil \<tturnstile> mk_neq a b) = Nil"
      by (rule cpx_proj[OF nilN neqN])
    have satEqH: "sat_hyp_fuel (hyp_of (Nil \<tturnstile> mk_eq a b)) 0"
      by (rule eqSubst[where a=Nil and b="hyp_of (Nil \<tturnstile> mk_eq a b)"
            and Q="\<lambda>G. sat_hyp_fuel G 0", OF eqSym[OF hEq] satNil])
    have satNeqH: "sat_hyp_fuel (hyp_of (Nil \<tturnstile> mk_neq a b)) 0"
      by (rule eqSubst[where a=Nil and b="hyp_of (Nil \<tturnstile> mk_neq a b)"
            and Q="\<lambda>G. sat_hyp_fuel G 0", OF eqSym[OF hNeq] satNil])
    have eqSat0: "sat_fuel (conc_of (Nil \<tturnstile> mk_eq a b)) 0"
      by (rule soundness_bridge_fuel[OF eqpf satEqH nat0])
    have neqSat0: "sat_fuel (conc_of (Nil \<tturnstile> mk_neq a b)) 0"
      by (rule soundness_bridge_fuel[OF neqpf satNeqH nat0])
    have eqSat: "sat_fuel (mk_eq a b) 0"
      using eqN eqSat0 by simp
    have neqSat: "sat_fuel (mk_neq a b) 0"
      using neqN neqSat0 by simp
    obtain q where q: "q N" and evaq: "evals a 0 q" and evbq: "evals b 0 q"
      by (rule sat_fuel_mk_eqE[OF a b eqSat])
    obtain x y where x: "x N" and y: "y N" and evax: "evals a 0 x" and evby: "evals b 0 y" and xy: "x \<noteq> y"
      by (rule sat_fuel_mk_neqE[OF a b neqSat])
    have xq: "x = q"
      by (rule evals_functional[OF a nat0 evax evaq])
    have yq: "y = q"
      by (rule evals_functional[OF b nat0 evby evbq])
    have xqy: "x = y"
      by (rule eq_trans[OF xq eqSym[OF yq]])
    show "False"
      by (rule exF[OF xqy xy[unfolded neq_def]])
  qed
qed

(* The step-indexed semantics is a model of the abstract `consistent`
   locale, so `syntactically_consistent` transfers to it. *)
sublocale consistent mk_eq mk_neq dfns is_valid_proof evals sat_fuel sat_hyp_fuel
proof (unfold_locales)
  show "\<And>a b. a N \<Longrightarrow> b N \<Longrightarrow> mk_eq a b N"
    by (rule mk_eq_N')
  show "\<And>a b. a N \<Longrightarrow> b N \<Longrightarrow> mk_neq a b N"
    by (rule mk_neq_N')
  show "\<And>p J. p N \<Longrightarrow> J N \<Longrightarrow> is_valid_proof p J B"
    by (rule proof_is_bool)
  show "\<And>A. sat_hyp_fuel Nil A"
    by (rule sat_hyp_fuel_nil)
  show "\<And>t A r q. t N \<Longrightarrow> A N \<Longrightarrow> evals t A r \<Longrightarrow> evals t A q \<Longrightarrow> r = q"
    by (rule evals_functional)
  show "\<And>a b A R. a N \<Longrightarrow> b N \<Longrightarrow> sat_fuel (mk_eq a b) A \<Longrightarrow>
        (\<And>q. q N \<Longrightarrow> evals a A q \<Longrightarrow> evals b A q \<Longrightarrow> R) \<Longrightarrow> R"
    by (rule sat_fuel_mk_eqE)
  show "\<And>a b A R. a N \<Longrightarrow> b N \<Longrightarrow> sat_fuel (mk_neq a b) A \<Longrightarrow>
        (\<And>x y. x N \<Longrightarrow> y N \<Longrightarrow> evals a A x \<Longrightarrow> evals b A y \<Longrightarrow> x \<noteq> y \<Longrightarrow> R) \<Longrightarrow> R"
    by (rule sat_fuel_mk_neqE)
  show "\<And>p J A. is_valid_proof p J \<Longrightarrow> sat_hyp_fuel (hyp_of J) A \<Longrightarrow> A N \<Longrightarrow> sat_fuel (conc_of J) A"
    by (rule soundness_bridge_fuel)
qed

end
end