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
  fixes eval :: "tm \<Rightarrow> asn \<Rightarrow> val"
  fixes sat_fm :: "fm \<Rightarrow> asn \<Rightarrow> o"
  fixes sat_hyp :: "hyp \<Rightarrow> asn \<Rightarrow> o"

  assumes sat_hyp_nil: "sat_hyp Nil A"

  (*What Equations mean in the model *)
  assumes sat_eqE:  "\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow>sat_fm (mk_eq a b) A \<Longrightarrow> eval a A = eval b A"
  assumes sat_neqE: "\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow>sat_fm (mk_neq a b) A \<Longrightarrow> eval a A \<noteq> eval b A"

locale consistent =  suff_semantics +
  (* Valid proofs yield satisfied formulas *)
  assumes soundness: "\<lbrakk>is_valid_proof p J; sat_hyp (hyp_of J) A\<rbrakk> \<Longrightarrow> sat_fm (conc_of J) A"
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
      done

    have eq_sat1: "sat_fm (mk_eq a b) zero"
      using eq_sat mk_eq_nat apply simp
      done

    have neq_sat: "sat_fm  (conc_of \<langle>Nil, mk_neq a b\<rangle>) zero"
      apply (rule soundness)
       apply (rule neq_pf)
      using mk_neq_nat apply simp
      apply (rule sat_hyp_nil)
      done
    have neq_sat1: "sat_fm (mk_neq a b) zero"
      using neq_sat mk_neq_nat apply simp
      done

    have eq_val: "eval a zero = eval b zero"
      apply (rule sat_eqE)
      using a_nat b_nat apply simp+
      apply (rule eq_sat1)
      done

    have neq_val: "eval a zero  \<noteq> eval b zero"
      apply (rule sat_neqE)
      using a_nat b_nat apply simp+
      apply (rule neq_sat1)
      done

    show "False"
      apply (rule exF[where P="eval a zero  = eval b zero "])
       apply (rule eq_val)
      apply (fold neq_def)
      apply (rule neq_val)
      done
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
  assumes mono_pack_T: "(x \<le> y = 1) \<Longrightarrow> (pack_T tg x \<le> pack_T tg y =1)"
  assumes mono_pack_F: "(x \<le> y = 1) \<Longrightarrow> (pack_F tg x \<le> pack_F tg y =1)"
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
      eval (nth (cpx (load_T t)) dfns) 
           ((eval (cpx (cpy (load_T t))) A)\<triangleright> ((eval (cpy (cpy (load_T t))) A) \<triangleright> Nil))"
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





locale bga_subst_semantics = bga_semantics + bga_subst +
  fixes asn_put :: "asn \<Rightarrow> num \<Rightarrow> val \<Rightarrow> asn"
  assumes  asn_put_def:  "asn_put A i v :=  
              if i = 0 then
                   if A = Nil then v \<triangleright> Nil
                   else v \<triangleright> list_tl A
              else if A = Nil then 0 \<triangleright> asn_put Nil (i - 1) v
              else list_hd A \<triangleright> asn_put (list_tl A) (i - 1) v"
  assumes sat_subst_F: "\<lbrakk>f N; i N; s N\<rbrakk> \<Longrightarrow> sat (subst_F f i s) A \<longleftrightarrow> sat f (asn_put A i (eval s A))" 
  assumes sat_hyp_put: "\<lbrakk>G N; i N; v N; fresh_H i G; sat_hyp G A\<rbrakk> \<Longrightarrow> sat_hyp G (asn_put A i v)" 
  assumes eval_var_put: "\<lbrakk>i N; v N\<rbrakk> \<Longrightarrow> eval (pack_T T_VAR i) (asn_put A i v) = v" 
  assumes asn_put_overwrite: "\<lbrakk>i N; v N; w N\<rbrakk> \<Longrightarrow> asn_put (asn_put A i v) i w = asn_put A i w"
begin

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

definition asn_puts :: "asn \<Rightarrow> List \<Rightarrow> asn" where
  "asn_puts A us \<equiv>  list_rec A (\<lambda>u C. asn_put C (cpx u) (cpy u)) us"

lemma asn_puts_nil: "asn_puts A Nil = A"
  unfolding asn_puts_def by (rule list_rec_nil)

lemma asn_put_N:
  assumes i: "i N"
      and v: "v N"
  shows "asn_put A i v N"
proof -
  have ow:
    "asn_put (asn_put A i v) i v = asn_put A i v"
    using i v v by (rule asn_put_overwrite)
  show ?thesis
    using ow by (rule eq_impl_term2)
qed

lemma asn_puts_cons:
  assumes i: "i N"
      and v: "v N"
      and us: "us N"
  shows "asn_puts A (\<langle>i, v\<rangle> \<triangleright> us) =  asn_put (asn_puts A us) i v"
proof -
  have iv: "\<langle>i, v\<rangle> N"
    using i v by simp
  have rec:
    "list_rec A (\<lambda>u C. asn_put C (cpx u) (cpy u)) (\<langle>i, v\<rangle> \<triangleright> us) =
     (\<lambda>u C. asn_put C (cpx u) (cpy u)) \<langle>i, v\<rangle> (list_rec A (\<lambda>u C. asn_put C (cpx u) (cpy u)) us)"
    using iv us by (rule list_rec_cons)
  have putN:
    "asn_put (list_rec A  (\<lambda>u C. asn_put C (hyp_of u) (conc_of u)) us) i v N"
    using i v by (rule asn_put_N)
  show ?thesis
    unfolding asn_puts_def
    using rec i v putN by simp
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
        by (rule eval_var_put[OF i m])
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
        by (rule asn_put_overwrite[OF i m Sm])
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
        by (rule eval_var_put[OF i m])
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
        by (rule asn_put_overwrite[OF i m Sm])
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
proof -
  have R: "Q (if tag_T t = T_VAR then nth (load_T t) A
     else if tag_T t = T_ZERO then 0
     else if tag_T t = T_SUC then S (eval (load_T t) A)
     else if tag_T t = T_PRED then P (eval (load_T t) A)
     else if tag_T t = T_IFZ then
       (if eval (cpx (load_T t)) A = 0
        then eval (cpx (cpy (load_T t))) A
        else eval (cpy (cpy (load_T t))) A)
     else
       eval (nth (cpx (load_T t)) dfns)
         (eval (cpx (cpy (load_T t))) A \<triangleright>
          eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using H by (rule defI[OF eval_def])
  show ?thesis
    using tg R by (rule cond_thenQ_E)
qed

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
  have R: "Q (if tag_T t = T_VAR then nth (load_T t) A
     else if tag_T t = T_ZERO then 0
     else if tag_T t = T_SUC then S (eval (load_T t) A)
     else if tag_T t = T_PRED then P (eval (load_T t) A)
     else if tag_T t = T_IFZ then
       (if eval (cpx (load_T t)) A = 0
        then eval (cpx (cpy (load_T t))) A
        else eval (cpy (cpy (load_T t))) A)
     else
       eval (nth (cpx (load_T t)) dfns)
         (eval (cpx (cpy (load_T t))) A \<triangleright>
          eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using H by (rule defI[OF eval_def])
  show ?thesis 
    using tg R by simp
qed

lemma eval_zeroI:
  assumes t: "t N" and tg: "tag_T t = T_ZERO"
      and H: "Q 0"
  shows "Q (eval t A)"
proof -
  show ?thesis
    apply (rule defE[OF eval_def[where t=t and A=A]])
    using tg H by simp
qed

lemma eval_sucD:
  assumes t: "t N"
      and tg: "tag_T t = T_SUC"
      and H: "Q (eval t A)"
  shows "Q (S (eval (load_T t) A))"
proof -
  have R:
    "Q (if tag_T t = T_VAR then nth (load_T t) A
       else if tag_T t = T_ZERO then 0
       else if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using H by (rule defI[OF eval_def])
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have R1:
    "Q (if tag_T t = T_ZERO then 0
       else if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nvar R by (rule cond_elseQ_E)
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have R2:
    "Q (if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
            eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nzero R1 by (rule cond_elseQ_E)
  show ?thesis
    using tg R2 by (rule cond_thenQ_E)
qed

lemma eval_sucI:
  assumes t: "t N"
      and tg: "tag_T t = T_SUC"
      and H: "Q (S (eval (load_T t) A))"
  shows "Q (eval t A)"
proof -
  have R2:
    "Q (if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
            eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using tg H by (rule cond_thenQ_I)
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have R1:
    "Q (if tag_T t = T_ZERO then 0
       else if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nzero R2 by (rule cond_elseQ_I)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have R:
    "Q(if tag_T t = T_VAR then nth (load_T t) A
       else if tag_T t = T_ZERO then 0
       else if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nvar R1 by (rule cond_elseQ_I)
  show ?thesis
    apply (rule defE[OF eval_def[where t=t and A=A]])
    using R .
qed

lemma eval_predD:
  assumes t: "t N"
      and tg: "tag_T t = T_PRED"
      and H: "Q (eval t A)"
  shows "Q (P (eval (load_T t) A))"
proof -
  have R:
    "Q (if tag_T t = T_VAR then nth (load_T t) A
       else if tag_T t = T_ZERO then 0
       else if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using H by (rule defI[OF eval_def])
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have R1:
    "Q (if tag_T t = T_ZERO then 0
       else if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nvar R by (rule cond_elseQ_E)
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have R2:
    "Q (if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nzero R1 by (rule cond_elseQ_E)
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have R3:
    "Q (if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nsuc R2 by (rule cond_elseQ_E)
  show ?thesis
    using tg R3 by (rule cond_thenQ_E)
qed

lemma eval_predI:
  assumes t: "t N"
      and tg: "tag_T t = T_PRED"
      and H: "Q (P (eval (load_T t) A))"
  shows "Q (eval t A)"
proof -
  have R3:
    "Q (if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using tg H by (rule cond_thenQ_I)
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have R2:
    "Q (if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nsuc R3 by (rule cond_elseQ_I)
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have R1:
    "Q (if tag_T t = T_ZERO then 0
       else if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nzero R2 by (rule cond_elseQ_I)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have R:
    "Q (if tag_T t = T_VAR then nth (load_T t) A
       else if tag_T t = T_ZERO then 0
       else if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nvar R1 by (rule cond_elseQ_I)
  show ?thesis
    apply (rule defE[OF eval_def[where t=t and A=A]])
    using R .
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
  have R:
    "Q (if tag_T t = T_VAR then nth (load_T t) A
       else if tag_T t = T_ZERO then 0
       else if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using H by (rule defI[OF eval_def])
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have R1:
    "Q (if tag_T t = T_ZERO then 0
       else if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nvar R by (rule cond_elseQ_E)
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have R2:
    "Q (if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nzero R1 by (rule cond_elseQ_E)
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have R3:
    "Q (if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nsuc R2 by (rule cond_elseQ_E)
  have npred: "\<not> tag_T t = T_PRED"
    using tg by simp
  have R4:
    "Q (if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using npred R3 by (rule cond_elseQ_E)
  show ?thesis
    using tg R4 by (rule cond_thenQ_E)
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
  have R4:
    "Q (if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using tg H by (rule cond_thenQ_I)
  have npred: "\<not> tag_T t = T_PRED"
    using tg by simp
  have R3:
    "Q (if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using npred R4 by (rule cond_elseQ_I)
  have nsuc: "\<not> tag_T t = T_SUC"
    using tg by simp
  have R2:
    "Q
      (if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nsuc R3 by (rule cond_elseQ_I)
  have nzero: "\<not> tag_T t = T_ZERO"
    using tg by simp
  have R1:
    "Q (if tag_T t = T_ZERO then 0
       else if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nzero R2 by (rule cond_elseQ_I)
  have nvar: "\<not> tag_T t = T_VAR"
    using tg by simp
  have R:
    "Q (if tag_T t = T_VAR then nth (load_T t) A
       else if tag_T t = T_ZERO then 0
       else if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nvar R1 by (rule cond_elseQ_I)
  show ?thesis
    apply (rule defE[OF eval_def[where t=t and A=A]])
    using R .
qed

lemma eval_appD:
  assumes t: "t N"
      and nvar: "\<not> tag_T t = T_VAR"
      and nzero: "\<not> tag_T t = T_ZERO"
      and nsuc: "\<not> tag_T t = T_SUC"
      and npred: "\<not> tag_T t = T_PRED"
      and nifz: "\<not> tag_T t = T_IFZ"
      and H: "Q (eval t A)"
  shows "Q (eval (nth (cpx (load_T t)) dfns)
            (eval (cpx (cpy (load_T t))) A \<triangleright>
             eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
proof -
  have R:
  "Q (if tag_T t = T_VAR then nth (load_T t) A
     else if tag_T t = T_ZERO then 0
     else if tag_T t = T_SUC then S (eval (load_T t) A)
     else if tag_T t = T_PRED then P (eval (load_T t) A)
     else if tag_T t = T_IFZ then
       (if eval (cpx (load_T t)) A = 0
        then eval (cpx (cpy (load_T t))) A
        else eval (cpy (cpy (load_T t))) A)
     else
       eval (nth (cpx (load_T t)) dfns)
         (eval (cpx (cpy (load_T t))) A \<triangleright>
          eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
  using H by (rule defI[OF eval_def])
  have R1: 
    "Q (if tag_T t = T_ZERO then 0
     else if tag_T t = T_SUC then S (eval (load_T t) A)
     else if tag_T t = T_PRED then P (eval (load_T t) A)
     else if tag_T t = T_IFZ then
       (if eval (cpx (load_T t)) A = 0
        then eval (cpx (cpy (load_T t))) A
        else eval (cpy (cpy (load_T t))) A)
     else
       eval (nth (cpx (load_T t)) dfns)
         (eval (cpx (cpy (load_T t))) A \<triangleright>
          eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
  proof (rule cond_elseQ_E[where c="tag_T t = T_VAR" and a="nth (load_T t) A"])
    show "\<not> tag_T t = T_VAR"
      by (rule nvar)
    show 
      "Q (if tag_T t = T_VAR then nth (load_T t) A
         else if tag_T t = T_ZERO then 0
         else if tag_T t = T_SUC then S (eval (load_T t) A)
         else if tag_T t = T_PRED then P (eval (load_T t) A)
         else if tag_T t = T_IFZ then
           (if eval (cpx (load_T t)) A = 0
            then eval (cpx (cpy (load_T t))) A
            else eval (cpy (cpy (load_T t))) A)
         else
           eval (nth (cpx (load_T t)) dfns)
             (eval (cpx (cpy (load_T t))) A \<triangleright>
              eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
      by (rule R)
  qed
  have R2:
    "Q (if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nzero R1 by (rule cond_elseQ_E)
  have R3:
    "Q (if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nsuc R2 by (rule cond_elseQ_E)
  have R4:
    "Q (if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using npred R3 by (rule cond_elseQ_E)
  show ?thesis
    using nifz R4 by (rule cond_elseQ_E)
qed

lemma eval_appI:
  assumes t: "t N"
      and tg: "tag_T t = T_APP"
      and H:
        "Q
          (eval (nth (cpx (load_T t)) dfns)
            (eval (cpx (cpy (load_T t))) A \<triangleright>
             eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
  shows "Q (eval t A)"
proof -
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
  have R4:
    "Q (if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nifz H  by (rule cond_elseQ_I)
  have R3:
    "Q (if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using npred R4 by (rule cond_elseQ_I)
  have R2:
    "Q (if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nsuc R3 by (rule cond_elseQ_I)
  have R1:
    "Q (if tag_T t = T_ZERO then 0
       else if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nzero R2 by (rule cond_elseQ_I)
  have R:
    "Q (if tag_T t = T_VAR then nth (load_T t) A
       else if tag_T t = T_ZERO then 0
       else if tag_T t = T_SUC then S (eval (load_T t) A)
       else if tag_T t = T_PRED then P (eval (load_T t) A)
       else if tag_T t = T_IFZ then
         (if eval (cpx (load_T t)) A = 0
          then eval (cpx (cpy (load_T t))) A
          else eval (cpy (cpy (load_T t))) A)
       else
         eval (nth (cpx (load_T t)) dfns)
           (eval (cpx (cpy (load_T t))) A \<triangleright>
            eval (cpy (cpy (load_T t))) A \<triangleright> Nil))"
    using nvar R1 by (rule cond_elseQ_I)
  show ?thesis
    apply (rule defE[OF eval_def[where t=t and A=A]])
    using R .
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
          using i m by (rule asn_put_N)
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
        using q i a G fresh satG base step an
        by (rule nat_ind_sound_put)
      show "sat ?f A"
        using qa sq
        by (rule eqSubst[where Q="\<lambda>r. sat r A"])
    qed
  qed
qed

lemma check_app_sound:
  assumes J: "J N" and rest: "rest N"
      and chk: "check_app J rest"
      and prev: "\<And>K. K N \<Longrightarrow> mem K rest \<Longrightarrow>
                   sat_hyp (hyp_of K) A \<Longrightarrow> sat (conc_of K) A"
      and satG: "sat_hyp (hyp_of J) A"
  shows "sat (conc_of J) A"
  sorry

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
            by (rule check_ind_sound[OF J rest g3 prev prevN satG])
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

lemma check_list_sound:
  assumes pf: "pf N"
  shows "\<And>J A. check_list pf \<Longrightarrow> J N \<Longrightarrow> mem J pf \<Longrightarrow>
                sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
proof (rule check_list_induct[OF pf])
  show "\<And>J A. check_list Nil \<Longrightarrow> J N \<Longrightarrow> mem J Nil \<Longrightarrow>
               sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
  proof -
    fix J A
    assume chk: "check_list Nil"
       and J: "J N"
       and m: "mem J Nil"
       and satG: "sat_hyp (hyp_of J) A"
    show "sat (conc_of J) A"
      by (rule exF[OF m mem_nil])
  qed
next
  fix h t A
  assume h: "h N"
     and t: "t N"
     and IH:
       "\<And>J. check_list t \<Longrightarrow> J N \<Longrightarrow> mem J t \<Longrightarrow>
          sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
  show "\<And>J. check_list (Cons h t) \<Longrightarrow> J N \<Longrightarrow>
               mem J (Cons h t) \<Longrightarrow>
               sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
  proof -
    fix J
    assume cl: "check_list (Cons h t)"
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
    have R1:
      "if valid_step h t then check_list t else False"
      using hne R by (rule notcond_thenE)
    show "sat (conc_of J) A"
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
            using clt K mK satK by (rule IH)
        next
          fix K A2
          assume A2: "A2 N"
             and K: "K N"
             and mK: "mem K t"
             and satK: "sat_hyp (hyp_of K) A2"
          show "sat (conc_of K) A2"
            using A2 clt K mK satK
            by (rule check_list_sound_N[OF t])
        next
          show "sat_hyp (hyp_of h) A"
            by (rule satGh)
        qed
        show "sat (conc_of J) A"
          using hJ sh
          by (rule eqSubst[where Q="\<lambda>z. sat (conc_of z) A"])
      next
        assume nhJ: "\<not> h = J"
        have mJt: "mem J t"
          using nhJ mJ' by (rule notcond_thenE)
        show "sat (conc_of J) A"
          using clt J mJt satG by (rule IH)
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
        using p cp JN mJ satG by (rule check_list_sound)
    next
      assume nhJ: "\<not> list_hd p = J"
      have F: "False" using nhJ inner by (rule notcond_thenE)
      show ?thesis by (rule exF[OF F not_false])
    qed
  qed
qed


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
  show "\<And>p J A. is_valid_proof p J \<Longrightarrow> sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
    by (rule soundness_bridge)
qed

end
end