theory GD
imports Pure
keywords
  "declaretype" :: diag (* and
  "recdef" :: thy_decl *)
begin

text \<open>The following theory development formalizes the Grounded Deduction Logic.\<close>

named_theorems auto "Lemmas of shape simp \<Longrightarrow> comp"
named_theorems cond "Conditionally applied if P can be solved: P \<Longrightarrow> simp \<Longrightarrow> comp"

section \<open>Axiomatization of truth in GD\<close>

typedecl o

judgment
  Trueprop :: \<open>o \<Rightarrow> prop\<close>  (\<open>_\<close> 5)

axiomatization
  disj :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close>  (infixr \<open>\<or>\<close> 30) and
  not :: \<open>o \<Rightarrow> o\<close> (\<open>\<not> _\<close> [40] 40)
where
  disjI1: \<open>P \<Longrightarrow> P \<or> Q\<close> and
  disjI2: \<open>Q \<Longrightarrow> P \<or> Q\<close> and
  disjI3: \<open>\<lbrakk>\<not>P; \<not>Q\<rbrakk> \<Longrightarrow> \<not>(P \<or> Q)\<close> and
  disjE1: \<open>\<lbrakk>P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R\<close> and
  disjE2: \<open>\<not>(P \<or> Q) \<Longrightarrow> \<not>P\<close> and
  disjE3: \<open>\<not>(P \<or> Q) \<Longrightarrow> \<not>Q\<close> and
  dNegI: \<open>P \<Longrightarrow> (\<not>\<not>P)\<close> and
  dNegE: \<open>(\<not>\<not>P) \<Longrightarrow> P\<close> and
  exF: \<open>\<lbrakk>P; \<not>P\<rbrakk> \<Longrightarrow> Q\<close>

lemma mp:
  assumes H1: "a \<Longrightarrow> b"
  assumes H2: "a"
  shows "b"
apply (rule disjE1[where P="a" and Q="a"])
apply (rule disjI1)
apply (rule H2)
apply (rule H1)
apply (assumption)
apply (rule H1)
apply (assumption)
done

section \<open>Axiomatization of naturals in GD\<close>

typedecl num

axiomatization
  eq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> o\<close>  (infixl \<open>=\<close> 45)
where
  eqSubst: \<open>\<lbrakk>a = b; Q a\<rbrakk> \<Longrightarrow> Q b\<close> and
  eqSym: \<open>a = b \<Longrightarrow> b = a\<close> and
  eq_reflection: \<open>x = y \<Longrightarrow> x \<equiv> y\<close>

lemma eq_trans: "a = b \<Longrightarrow> b = c \<Longrightarrow> a = c"
by (rule eqSubst[where a="b" and b="c"], assumption)

definition neq :: \<open>num \<Rightarrow> num \<Rightarrow> o\<close> (infixl \<open>\<noteq>\<close> 45)
  where \<open>a \<noteq> b \<equiv> \<not> (a = b)\<close>
definition bJudg :: \<open>o \<Rightarrow> o\<close> (\<open>_ B\<close> [21] 20)
  where \<open>(p B) \<equiv> (p \<or> \<not>p)\<close>
definition isNat :: \<open>num \<Rightarrow> o\<close> (\<open>_ N\<close> [21] 20)
where "x N \<equiv> x = x"
definition conj :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> (infixl \<open>\<and>\<close> 35)
  where \<open>p \<and> q \<equiv> \<not>(\<not>p \<or> \<not>q)\<close>
definition impl :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> (infixl \<open>\<longrightarrow>\<close> 25)
  where \<open>p \<longrightarrow> q \<equiv> \<not>p \<or> q\<close>

lemma conjE1:
  assumes p_and_q: "p \<and> q"
  shows "p"
apply (rule dNegE)
apply (rule disjE2[where Q="\<not>q"])
apply (fold conj_def)
apply (rule p_and_q)
done

lemma conjE2:
  assumes p_and_q: "p \<and> q"
  shows "q"
apply (rule dNegE)
apply (rule disjE3[where P="\<not>p"])
apply (fold conj_def)
apply (rule p_and_q)
done

lemma conjI [auto]:
  assumes p: "p"
  assumes q: "q"
  shows "p \<and> q"
apply (unfold conj_def)
apply (rule disjI3)
apply (rule dNegI)
apply (rule p)
apply (rule dNegI)
apply (rule q)
done

axiomatization
  num_zero :: \<open>num\<close>                        and
  num_suc :: \<open>num \<Rightarrow> num\<close>     (\<open>S(_)\<close> [800]) and
  num_pred :: \<open>num \<Rightarrow> num\<close>    (\<open>P(_)\<close> [800])
where
  nat0: \<open>num_zero N\<close> and
  sucInj: \<open>S a = S b \<Longrightarrow> a = b\<close> and
  sucCong: \<open>a = b \<Longrightarrow> S a = S b\<close> and
  predCong: \<open>a = b \<Longrightarrow> P a = P b\<close> and
  eqBool: \<open>\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow> (a = b) B\<close> and
  sucNonZero: \<open>a N \<Longrightarrow> S a \<noteq> num_zero\<close> and
  predSucInv: \<open>a N \<Longrightarrow> P(S(a)) = a\<close> and
  pred0: \<open>P(num_zero) = num_zero\<close>

lemma zeroRefl [auto]: "num_zero = num_zero"
apply (fold isNat_def)
apply (rule nat0)
done

lemma natS [auto]:
  assumes a_nat: "a N"
  shows "S a N"
apply (unfold isNat_def)
apply (rule sucCong)
apply (fold isNat_def)
apply (rule a_nat)
done

lemma natP [auto]:
  assumes a_nat: "a N"
  shows "P a N"
apply (unfold isNat_def)
apply (rule predCong)
apply (fold isNat_def)
apply (rule a_nat)
done

lemma implI [auto]:
  assumes a_bool: "a B"
  assumes a_deduce_b: "a \<Longrightarrow> b"
  shows "a \<longrightarrow> b"
proof (unfold impl_def, rule disjE1[where P="a" and Q="\<not>a"])
  show "a \<or> \<not>a"
    apply (fold GD.bJudg_def)
    apply (rule a_bool)
    done
  next
    assume a_holds: "a"
    have b_holds: "b"
      apply (rule mp[where a="a"])
      apply (rule a_deduce_b)
      apply (assumption)
      apply (rule a_holds)
      done
    show "\<not>a \<or> b" by (rule disjI2, rule b_holds)
  next
    assume not_a: "\<not>a"
    show "\<not>a \<or> b" by (rule disjI1, rule not_a)
qed

lemma implE:
  assumes H1: "a \<longrightarrow> b"
  assumes H2: "a"
  shows "b"
proof (rule disjE1[where P="\<not>a" and Q="b"])
  show "\<not>a \<or> b"
    apply (fold impl_def)
    apply (rule H1)
    done
  next
    assume not_a: "\<not>a"
    show "b"
    apply (rule exF[where P="a"])
    apply (rule H2)
    apply (rule not_a)
    done
  next
    show "b \<Longrightarrow> b"
    apply (assumption)
    done
qed

lemma grounded_contradiction:
  assumes p_bool: \<open>p B\<close>
  assumes notp_q: \<open>\<not>p \<Longrightarrow> q\<close>
  assumes notp_notq: \<open>\<not>p \<Longrightarrow> \<not>q\<close>
  shows \<open>p\<close>
proof (rule GD.disjE1[where P="p" and Q="\<not>p"])
  show "p \<or> \<not>p"
    using p_bool unfolding GD.bJudg_def .
  show "p \<Longrightarrow> p" by assumption
  show "\<not>p \<Longrightarrow> p"
  proof -
    assume not_p: "\<not>p"
    have q: "q" using notp_q[OF not_p] .
    have not_q: "\<not>q" using notp_notq[OF not_p] .
    from q and not_q show "p"
      by (rule exF)
  qed
qed

syntax
  "_gd_num" :: "num_token \<Rightarrow> num"    ("_")

ML_file "peano_numerals.ML"

parse_translation \<open>
  [(@{syntax_const "_gd_num"}, Peano_Syntax.parse_gd_numeral)]
\<close>

definition True
  where \<open>True \<equiv> 0 = 0\<close>
definition False
  where \<open>False \<equiv> S(0) = 0\<close>

lemma contradiction:
  assumes p_bool: "p B"
  assumes contr: "\<not>p \<Longrightarrow> False"
  shows "p"
apply (rule grounded_contradiction[where q="False"])
apply (rule p_bool)
proof -
  assume not_p: "\<not>p"
  show "False"
    apply (rule contr)
    apply (rule not_p)
    done
  show "\<not>False"
    apply (unfold False_def)
    apply (fold neq_def)
    apply (rule sucNonZero)
    apply (rule nat0)
    done
qed

(* Entailment reduces to almost the same as object-level implication \<longrightarrow>.
 * The difference is that the \<longrightarrow> introduction rule requires 'a' to be
 * proven boolean first ('a B'), while entailment does not. It is a
 * direct object-level mirroring of the meta-level a \<Longrightarrow> b.
 * Meta-level just means that it is of type prop \<Rightarrow> prop \<Rightarrow> prop,
 * while entailment mirrors this at the object level, that is, it's
 * of type o \<Rightarrow> o \<Rightarrow> o.
 * With entailment, GD can reason about deducability at the object level,
 * which adds a lot of expressive power.
 *)
axiomatization
  entails :: "o \<Rightarrow> o \<Rightarrow> o"    (infixr "\<turnstile>" 10)
where
  entailsI: "\<lbrakk>a \<Longrightarrow> b\<rbrakk> \<Longrightarrow> (a \<turnstile> b)" and
  entailsE: "\<lbrakk>a \<turnstile> b; a\<rbrakk> \<Longrightarrow> b"

axiomatization
  forall :: "(num \<Rightarrow> o) \<Rightarrow> o"  (binder "\<forall>" [8] 9) and
  exists :: "(num \<Rightarrow> o) \<Rightarrow> o"  (binder "\<exists>" [8] 9)
where
  forallI: "\<lbrakk>\<And>x. x N \<Longrightarrow> Q x\<rbrakk> \<Longrightarrow> \<forall>x. Q x" and
  forallE: "\<lbrakk>\<forall>c'. Q c'; a N\<rbrakk> \<Longrightarrow> Q a" and
  existsI: "\<lbrakk>a N; Q a\<rbrakk> \<Longrightarrow> \<exists>x. Q x" and
  existsE: "\<lbrakk>\<exists>i. Q i; \<And>a. a N \<Longrightarrow> Q a \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" and
  ind [case_names HQ Zero Suc]: \<open>\<lbrakk>a N; Q 0; \<forall>x.(Q x \<turnstile> Q S(x))\<rbrakk> \<Longrightarrow> Q a\<close>
  (*
  forAllNeg: "\<lbrakk>\<not>(\<forall>x. Q x); (Q x) B\<rbrakk> \<Longrightarrow> \<exists>x. \<not>(Q x)" and
  existsNeg: "\<lbrakk>\<not>(\<exists>x. Q x); (Q x) B\<rbrakk> \<Longrightarrow> \<forall>x. \<not>(Q x)" and
   *)

section \<open>Axiomatization of conditional evaluation in GD\<close>

consts
  cond :: \<open>o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
syntax
  "_cond" :: \<open>o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (\<open>if _ then _ else _\<close> [25, 24, 24] 24)
translations
  "if c then a else b" \<rightleftharpoons> "CONST cond c a b"

axiomatization
where
  condI1: \<open>\<lbrakk>c; a N\<rbrakk> \<Longrightarrow> (if c then a else b) = a\<close> and
  condI2: \<open>\<lbrakk>\<not>c; b N\<rbrakk> \<Longrightarrow> (if c then a else b) = b\<close> and
  condT: \<open>\<lbrakk>c B; c \<Longrightarrow> a N; \<not>c \<Longrightarrow> b N\<rbrakk> \<Longrightarrow> if c then a else b N\<close> and
  condI1B: \<open>\<lbrakk>c; d B\<rbrakk> \<Longrightarrow> (if c then d else e) = d\<close> and
  condI2B: \<open>\<lbrakk>\<not>c; e B\<rbrakk> \<Longrightarrow> (if c then d else e) = e\<close> and
  condTB: \<open>\<lbrakk>c B; c \<Longrightarrow> d B; \<not>c \<Longrightarrow> e B\<rbrakk> \<Longrightarrow> if c then d else e B\<close>

lemma condI1BEq:
  assumes c_holds: "c"
  assumes d_bool: "d B"
  assumes a_eq_d: "a = d"
  shows "(if c then a else b) = d"
apply (rule eqSubst[where a="d" and b="a"])
apply (rule eqSym)
apply (rule a_eq_d)
apply (rule condI1B)
apply (rule c_holds)
apply (rule d_bool)
done

lemma condI2BEq:
  assumes not_c: "\<not>c"
  assumes d_bool: "d B"
  assumes a_eq_d: "b = d"
  shows "(if c then a else b) = d"
apply (rule eqSubst[where a="d" and b="b"])
apply (rule eqSym)
apply (rule a_eq_d)
apply (rule condI2B)
apply (rule not_c)
apply (rule d_bool)
done

lemma condI3B:
  shows "a B \<Longrightarrow> c B \<Longrightarrow> (if c then a else a) = a"
apply (rule disjE1[where P="c" and Q="\<not>c"])
apply (fold GD.bJudg_def, simp)
apply (rule condI1B, simp+)
apply (rule condI2B, simp+)
done

lemma condI3BEq:
  assumes a_bool: "a B"
  assumes c_bool: "c B"
  assumes d_eq_a: "d = a"
  assumes e_eq_a: "e = a"
  shows "(if c then d else e) = a"
apply (rule disjE1[where P="c" and Q="\<not>c"])
apply (fold GD.bJudg_def)
apply (rule c_bool)
apply (rule eqSubst[where a="a" and b="d"])
apply (rule eqSym)
apply (rule d_eq_a)
apply (rule condI1B)
apply (assumption)
apply (rule a_bool)
apply (rule eqSubst[where a="a" and b="e"])
apply (rule eqSym)
apply (rule e_eq_a)
apply (rule condI2B)
apply (assumption)
apply (rule a_bool)
done

lemma condI1Eq:
  assumes c_holds: "c"
  assumes d_nat: "d N"
  assumes a_eq_d: "a = d"
  shows "(if c then a else b) = d"
apply (rule eqSubst[where a="d" and b="a"])
apply (rule eqSym)
apply (rule a_eq_d)
apply (rule condI1)
apply (rule c_holds)
apply (rule d_nat)
done

lemma condI2Eq:
  assumes not_c: "\<not>c"
  assumes d_nat: "d N"
  assumes a_eq_d: "b = d"
  shows "(if c then a else b) = d"
apply (rule eqSubst[where a="d" and b="b"])
apply (rule eqSym)
apply (rule a_eq_d)
apply (rule condI2)
apply (rule not_c)
apply (rule d_nat)
done

lemma condI3:
  shows "a N \<Longrightarrow> c B \<Longrightarrow> (if c then a else a) = a"
apply (rule disjE1[where P="c" and Q="\<not>c"])
apply (fold GD.bJudg_def, simp)
apply (rule condI1, simp+)
apply (rule condI2, simp+)
done

lemma condI3Eq:
  assumes a_nat: "a N"
  assumes c_bool: "c B"
  assumes d_eq_a: "c \<Longrightarrow> d = a"
  assumes e_eq_a: "\<not> c \<Longrightarrow> e = a"
  shows "(if c then d else e) = a"
apply (rule disjE1[where P="c" and Q="\<not>c"])
apply (fold GD.bJudg_def)
apply (rule c_bool)
apply (rule eqSubst[where a="a" and b="d"])
apply (rule eqSym)
apply (rule d_eq_a)
apply (assumption)
apply (rule condI1)
apply (assumption)
apply (rule a_nat)
apply (rule eqSubst[where a="a" and b="e"])
apply (rule eqSym)
apply (rule e_eq_a)
apply (assumption)
apply (rule condI2)
apply (assumption)
apply (rule a_nat)
done

ML_file "gd_auto.ML"
ML_file "gd_subst.ML"

section \<open>Definitional Mechanism in GD\<close>

axiomatization
  def :: \<open>'a \<Rightarrow> 'a \<Rightarrow> o\<close> (infix \<open>:=\<close> 10)
where
  defE: \<open>\<lbrakk>a := b; Q b\<rbrakk> \<Longrightarrow> Q a\<close>

ML_file "gd_simp.ML"

lemmas [simp] = predSucInv neq_def pred0 condI1 condI1B condI2 condI2B condI3B condI3 
lemmas [auto] = nat0 sucNonZero predSucInv pred0 eqBool disjI3 dNegI
declare sucCong [cond]

lemma [simp]: "(a = a) \<equiv> (a N)"
  unfolding isNat_def by (rule Pure.reflexive)

ML_file \<open>unfold_def.ML\<close>

section \<open>Deductions of non-elementary inference rules.\<close>

lemma true [auto]: "True"
  unfolding True_def by auto

lemma true_bool [auto]: "True B"
  unfolding bJudg_def by (rule disjI1, rule true)

lemma bool_refl [cond]: "a B \<Longrightarrow> a = a"
apply (rule eqSubst[where a="(if True then a else a)" and b="a"])
apply (rule condI1B, simp)
apply (rule condI1BEq, simp)
apply (rule condTB, simp)
apply (rule eqSym)
apply (rule condI1B, simp)
done

lemma [cond]: "\<not>c \<and> (d N) \<Longrightarrow> b = d \<Longrightarrow> (if c then a else b) = d"
apply (simp)
apply (rule condI2)
apply (rule conjE1, simp)
apply (rule conjE2, simp)
done

lemma [cond]: "c \<and> (d N) \<Longrightarrow> a = d \<Longrightarrow> (if c then a else b) = d"
apply (simp)
apply (rule condI1)
apply (rule conjE1, simp)
apply (rule conjE2, simp)
done

lemma [cond]: "\<not>c \<and> (d B) \<Longrightarrow> b = d \<Longrightarrow> (if c then a else b) = d"
apply (simp)
apply (rule condI2B)
apply (rule conjE1, simp)
apply (rule conjE2, simp)
done

lemma [cond]: "c \<and> (d B) \<Longrightarrow> a = d \<Longrightarrow> (if c then a else b) = d"
apply (simp)
apply (rule condI1B)
apply (rule conjE1, simp)
apply (rule conjE2, simp)
done

lemma [cond]: "c \<Longrightarrow> if c then True else b"
by simp

lemma [cond]: "\<not>c \<Longrightarrow> if c then a else True"
by simp

lemma [cond]: "a \<Longrightarrow> a B"
  unfolding bJudg_def by (rule disjI1, simp)

lemma [cond]: "\<not>a \<Longrightarrow> a B"
  unfolding bJudg_def by (rule disjI2, simp)

lemma [cond]: "\<not>c \<Longrightarrow> b \<Longrightarrow> if c then a else b"
apply (rule eqSubst[where a="b"])
apply (rule eqSym)
apply (rule condI2B)
apply (simp+)
done

lemma [cond]: "c \<Longrightarrow> a \<Longrightarrow> if c then a else b"
apply (rule eqSubst[where a="a"])
apply (rule eqSym)
apply (rule condI1B, simp)
done

lemma if_trueI [auto]: "c \<Longrightarrow> if c then True else False"
  by simp

lemma [auto]: "True = True"
  by simp

lemma not_false [auto]: "\<not>False"
proof (unfold False_def)
  show "\<not>(S(0) = 0)"
  proof -
    have "S(0) \<noteq> 0" by (rule sucNonZero) (rule nat0)
    then show ?thesis by (unfold neq_def)
  qed
qed

lemma false_bool [auto]: "False B"
proof (unfold bJudg_def)
  show "False \<or> \<not>False"
  proof -
    have "\<not>False" by (rule not_false)
    then show ?thesis by (rule disjI2[where Q="\<not>False" and P="False"])
  qed
qed

lemma disj_comm:
  assumes q_or_r: "Q \<or> R"
  shows "R \<or> Q"
proof (rule disjE1[where P="Q" and Q="R" and R="R \<or> Q"])
  show "Q \<or> R" by (rule q_or_r)
  show "Q \<Longrightarrow> R \<or> Q"
    proof -
      assume Q
      then show "R \<or> Q" by (rule disjI2[where Q="Q" and P="R"])
    qed
  show "R \<Longrightarrow> R \<or> Q"
    proof -
      assume R
      then show "R \<or> Q" by (rule disjI1[where P="R" and Q="Q"])
    qed
qed

lemma not_bool [auto]:
  assumes a_bool: "a B"
  shows "(\<not>a) B"
apply (unfold GD.bJudg_def)
apply (rule disjE1[where P="\<not>a" and Q="a"])
apply (rule disj_comm)
apply (fold GD.bJudg_def)
apply (rule a_bool)
apply (unfold GD.bJudg_def)
apply (rule disjI1)
apply (assumption)
apply (rule disjI2)
apply (rule dNegI)
apply (assumption)
done

lemma neq_sym:
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  assumes ab_neq: "a \<noteq> b"
  shows "b \<noteq> a"
proof (unfold neq_def, rule grounded_contradiction[where q="a=b"])
  show "(\<not>(b=a)) B"
    apply (auto)
    apply (rule b_nat)
    apply (rule a_nat)
    done
  next
    assume H: "\<not> \<not> b = a"
    show "a = b"
    apply (rule eqSym)
    apply (rule dNegE)
    apply (rule H)
    done
  next
    assume H: "\<not> \<not> b = a"
    show "\<not> a = b"
    apply (fold neq_def)
    apply (rule ab_neq)
    done
qed

lemma neq_bool [auto]:
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  shows "(a \<noteq> b) B"
apply (unfold neq_def)
apply (auto)
apply (rule a_nat)
apply (rule b_nat)
done

lemma sucNotEqual [auto]:
  assumes a_nat: "a N"
  shows "a \<noteq> S(a)"
proof (rule ind[where a="a"])
  show "a N" by (rule a_nat)
  show "0 \<noteq> S(0)"
    apply (rule neq_sym)
    apply (auto)
    done
  show "\<forall>x. (x\<noteq>S(x)) \<turnstile> (S(x) \<noteq> S(S(x)))"
    proof (rule forallI entailsI)+
      fix x
      assume x_nat: "x N"
      assume x_neq_s: "x \<noteq> S(x)"
      show "S(x) \<noteq> S(S(x))"
      proof (rule grounded_contradiction[where q="False"])
        show "(S(x) \<noteq> S(S(x))) B"
          apply (rule neq_bool)
          apply (rule natS)
          apply (rule x_nat)
          apply (auto)
          apply (rule x_nat)
          done
        next
          assume H: "\<not> (S(x) \<noteq> S(S(x)))"
          have eq_suc: "x = S(x)"
            apply (rule sucInj)
            apply (rule dNegE)
            apply (fold neq_def)
            apply (rule H)
            done
          then show "False"
            apply (rule exF)
            apply (fold neq_def)
            apply (rule x_neq_s)
            done
        next
          show "\<not> False"
          apply (auto)
          done
      qed
    qed
qed

section \<open>Definitions of basic arithmetic functions\<close>

(* Use the recursion mechanism to define the standard arithmetic functions to
 * be available in a global context.
 * Axiomatizing them simply means that the fact that they are defined with the
 * given definitions are axioms.
 * User-defined functions should be in locales,
 * not in axiomatization blocks.
 *)

(*
ML_file "gd_recdef.ML"

recdef add :: "num \<Rightarrow> num \<Rightarrow> num" where
  "add x y := if y = 0 then x else S(add x P(y))"
*)

axiomatization
  add   :: "num \<Rightarrow> num \<Rightarrow> num"  (infixl "+" 60) and
  sub   :: "num \<Rightarrow> num \<Rightarrow> num"  (infixl "-" 60) and
  mult  :: "num \<Rightarrow> num \<Rightarrow> num"  (infixl "*" 70) and
  div   :: "num \<Rightarrow> num \<Rightarrow> num"                  and
  less  :: "num \<Rightarrow> num \<Rightarrow> num"  (infix "<" 50)  and
  leq   :: "num \<Rightarrow> num \<Rightarrow> num"  (infix "\<le>" 50) and
  omega :: "'a"
where
  def_add:   "add x y  := if y = 0 then x else S(add x (P y))"       and
  def_sub:   "sub x y  := if y = 0 then x else P(sub x (P y))"       and
  def_mult:  "mult x y := if y = 0 then 0 else (x + mult x (P y))"   and
  def_leq:   "leq x y  := if x = 0 then 1
                          else if y = 0 then 0
                          else (leq (P x) (P y))"                    and
  def_less:  "less x y := if y = 0 then 0
                          else if x = 0 then 1
                          else (less (P x) (P y))"                   and
  def_div:   "div x y  := if x < y = 1 then 0 else S(div (x - y) y)" and
  def_omega: "omega    := omega"

definition greater :: "num \<Rightarrow> num \<Rightarrow> num" (infix ">" 50) where
  "greater x y \<equiv> 1 - (x \<le> y)"

definition geq :: "num \<Rightarrow> num \<Rightarrow> num" (infix "\<ge>" 50) where
  "geq x y \<equiv> 1 - (x < y)"

(* Returns y if S(y) > sqrt(x), else returns the greatest y s.t. y*y\<le>x. *)
axiomatization
  sqrt_h :: "num \<Rightarrow> num \<Rightarrow> num"
where
  def_sqrt_h: "sqrt_h := (\<lambda>x y. if (S(y) * S(y) > x = 1) then y else (sqrt_h x S(y)))"

definition floor_sqrt :: "num \<Rightarrow> num" where
  "floor_sqrt x \<equiv> sqrt_h x 0"

lemma less_0_false [simp, auto]: "(x < 0) = 0"
apply (unfold_def def_less)
apply (rule condI1)
apply (auto)
done

lemma add_terminates [auto]:
  assumes x_nat: \<open>x N\<close>
  assumes y_nat: \<open>y N\<close>
  shows \<open>add x y N\<close>
proof (rule ind[where a=y])
  show "y N" by (rule y_nat)
  show "add x 0 N"
    proof (unfold_def def_add)
      show "if (0 = 0) then x else S(add x P(0)) N"
        apply (rule eqSubst[where a="x"])
        apply (rule eqSym)
        apply (rule condI1)
        apply (rule zeroRefl)
        apply (rule x_nat)
        apply (rule x_nat)
        done
    qed
  show ind_step: "\<forall>a. ((x + a) N) \<turnstile> ((x + S(a)) N)"
    proof (rule forallI, rule entailsI, unfold_def def_add)
      fix a
      assume a_nat: "a N" and BC: "add x a N"
      show "if (S(a) = 0) then x else S(add x P(S(a))) N"
        proof (rule condT)
          show "S(a) = 0 B"
            apply (rule eqBool)
            apply (rule natS)
            apply (rule a_nat)
            apply (rule nat0)
            done
          show "x N" by (rule x_nat)
          show "S(add x P(S(a))) N"
            apply (rule GD.natS)
            apply (rule eqSubst[where a="x+a"])
            apply (rule eqSubst[where a="a" and b="P(S(a))"])
            apply (rule eqSym)
            apply (rule predSucInv)
            apply (rule a_nat)
            apply (fold isNat_def)
            apply (rule BC)
            apply (rule BC)
            done
        qed
    qed
qed

lemma cases_bool:
  assumes p_bool: "p B"
  assumes H: "p \<Longrightarrow> R"
  assumes H1: "\<not>p \<Longrightarrow> R"
  shows "R"
apply (rule disjE1[where P="p" and Q="\<not>p"])
apply (fold GD.bJudg_def)
apply (rule p_bool)
apply (rule H)
apply (assumption)
apply (rule H1)
apply (assumption)
done

declare [[simp_trace = true, simp_trace_depth_limit = 8]]

lemma [auto]: "c B \<Longrightarrow> if c then True else True"
  by simp

lemma [auto]: "c B \<Longrightarrow> \<not> (if c then False else False)"
  by simp

lemma mult_terminates [auto]:
  shows \<open>x N \<Longrightarrow> y N \<Longrightarrow> mult x y N\<close>
proof (rule ind[where a=y])
  show "y N \<Longrightarrow> y N" by (simp)
  show bc: "x N \<Longrightarrow> mult x 0 N"
    by (unfold_def def_mult, simp)
  show step: "x N \<Longrightarrow> y N \<Longrightarrow> \<forall>a. ((x * a) N) \<turnstile> ((x * S(a)) N)"
    proof (rule forallI, rule entailsI, unfold_def def_mult)
      fix a
      assume hyp: "mult x a N"
      show "a N \<Longrightarrow> x N \<Longrightarrow> y N \<Longrightarrow> if (S(a) = 0) then 0 else (add x (mult x P(S(a)))) N"
        by (rule condT, simp+, rule hyp)
    qed
qed

lemma [auto]: "x N \<Longrightarrow> \<not> S(x) = 0"
  by (fold neq_def, auto)

lemma add_zero [simp, auto]:
  assumes a_nat: "a N"
  shows "a + 0 = a"
apply (unfold_def def_add)
apply (rule condI1)
apply (rule zeroRefl)
apply (rule a_nat)
done

lemma zero_add [simp, auto]:
  shows "a N \<Longrightarrow> 0 + a = a"
apply (rule ind[where a="a"])
apply (assumption)
apply (simp)
proof (rule forallI, rule entailsI)
  fix x
  assume hyp: "0 + x = x"
  show "a N \<Longrightarrow> x N \<Longrightarrow> 0 + S x = S x"
    apply (unfold_def def_add)
    apply (simp add: hyp)
    done
qed

lemma add_succ [auto]:
  shows "a N \<Longrightarrow> b N \<Longrightarrow> a + S b = S (a + b)"
apply (rule eqSym)
apply (unfold_def def_add)
apply (rule eqSym)
apply (simp)+
done

lemma mult_zero [simp, auto]:
  shows "a * 0 = 0"
by (unfold_def def_mult, rule condI1, auto)

lemma zero_mult [simp, auto]:
  shows "a N \<Longrightarrow> 0 * a = 0"
proof (rule ind[where a="a"], auto, rule forallI, rule entailsI)
  fix x
  assume hyp: "0 * x = 0"
  show "a N \<Longrightarrow> x N \<Longrightarrow> 0 * S x = 0"
    apply (unfold_def def_mult)
    apply (simp)
    apply (rule hyp)
    done
qed

lemma mult_one [simp, auto]:
  shows "a N \<Longrightarrow> a * 1 = a"
by (unfold_def def_mult, simp)

lemma plus_one_suc [simp, auto]:
  shows "a N \<Longrightarrow> 1 + a = S a"
proof (rule ind[where a="a"], auto, rule forallI, rule entailsI)
  fix x
  assume hyp: "1+x = S x"
  show "a N \<Longrightarrow> x N \<Longrightarrow> 1+(S x) = S S x"
    apply (unfold_def def_add)
    apply (simp add: hyp)
    done
qed

lemma one_plus_suc [simp, auto]:
  shows "a N \<Longrightarrow> a + 1 = S a"
proof (rule ind[where a="a"], auto, rule forallI, rule entailsI)
  fix x
  assume hyp: "x+1 = S x"
  show "x N \<Longrightarrow> (S x)+1 = S S x"
    by (unfold_def def_add, simp)
qed

lemma [auto]: "x N \<Longrightarrow> x = x"
by (fold isNat_def)

lemma one_mult [simp, auto]:
  shows "a N \<Longrightarrow> 1 * a = a"
proof (rule ind[where a="a"], auto, rule forallI, rule entailsI)
  fix x
  assume hyp: "1*x = x"
  show "a N \<Longrightarrow> x N \<Longrightarrow> 1*(S x) = S x"
    by (unfold_def def_mult, simp add: hyp)
qed

lemma zero_leq_true [simp, auto]:
  assumes x_nat: "x N"
  shows "0 \<le> x = 1"
by (unfold_def def_leq, rule condI1Eq, auto)

lemma leq_terminates [auto]:
  shows "x N \<Longrightarrow> y N \<Longrightarrow> x \<le> y N"
proof -
  have H: "y N \<Longrightarrow> \<forall>x. x\<le>y N"
  proof (rule ind[where a="y"], simp)
    show "\<forall>x'. x' \<le> 0 N"
      proof (rule forallI)
        fix x'
        show "x' N \<Longrightarrow> x' \<le> 0 N"
          by (unfold_def def_leq, simp, rule condT, simp)
      qed
    show "\<forall>x. (\<forall>xa. xa \<le> x N) \<turnstile> (\<forall>xa. xa \<le> S(x) N)"
      proof (rule forallI, rule entailsI)+
        fix x
        assume H: "\<forall>xa. xa \<le> x N"
        show "x N \<Longrightarrow> \<forall>xa. xa \<le> S(x) N"
          proof (rule forallI)
            fix xa
            show "x N \<Longrightarrow> xa N \<Longrightarrow> xa \<le> S(x) N"
              apply (unfold_def def_leq)
              apply (rule condT)
              apply (simp+)
              apply (rule condT)
              apply (simp)
              apply (rule forallE[where a="P xa"])
              apply (rule H)
              apply (simp)
              done
          qed
      qed
  qed
  then show "x N \<Longrightarrow> y N \<Longrightarrow> x \<le> y N"
    by (rule forallE)
qed

lemma less_terminates [auto]:
  shows "x N \<Longrightarrow> y N \<Longrightarrow> x < y N"
proof -
  have q: "y N \<Longrightarrow> \<forall>x. x < y N"
  proof (rule ind[where a="y"], simp)
    show "\<forall>x. x < 0 N"
      by (rule forallI, simp)
    show "\<forall>x. (\<forall>xa. xa < x N) \<turnstile> (\<forall>xa. xa < S x N)"
      proof (rule forallI entailsI)+
        fix x y
        assume hyp: "\<forall>xa. xa < x N"
        show "x N \<Longrightarrow> y N \<Longrightarrow> y < S x N"
          apply (unfold_def def_less)
          apply (rule condT)
          apply (simp+)
          apply (rule condT)
          apply (simp+)
          apply (rule forallE[where a="P y"])
          apply (rule hyp)
          apply (simp)
          done
      qed
  qed
  show "x N \<Longrightarrow> y N \<Longrightarrow> x < y N"
    by (rule forallE[where a="x"], rule q, simp)
qed

lemma leq_refl [simp, auto]:
  shows "x N \<Longrightarrow> (x \<le> x) = 1"
proof (rule ind[where a="x"], simp)
  show "\<forall>x.(x \<le> x = 1) \<turnstile> (S(x) \<le> S(x) = 1)"
  proof (rule forallI entailsI)+
    fix x
    assume x_refl: "x \<le> x = 1"
    show "x N \<Longrightarrow> ((S(x)) \<le> S(x)) = 1"
      apply (unfold_def def_leq)
      apply (simp add: x_refl)+
      done
  qed
qed

lemma pred_leq [simp, auto]:
  assumes z_nat: "z N"
  shows "P(z) \<le> z = 1"
proof (rule ind[where a="z"])
  show "z N" by (rule z_nat)
  show "((P(0)) \<le> 0) = 1"
    by (unfold_def def_leq, simp)
  show "\<forall>x. ((P(x))\<le>x = 1) \<turnstile> (((P(S(x)))\<le>S(x)) = 1)"
    proof (rule forallI entailsI)+
      fix x
      assume ind_hyp: "((P(x)) \<le> x) = 1"
      show "x N \<Longrightarrow> ((P(S(x))) \<le> (S(x))) = 1"
        apply (unfold_def def_leq)
        apply (rule condI3Eq)
        apply (simp add: ind_hyp)+
        done
    qed
qed

lemma leq_suc [simp, auto]:
  assumes x_nat: "x N"
  shows "x \<le> S(x) = 1"
apply (rule ind[where a="x"])
apply (rule x_nat)
apply (auto)
apply (rule forallI entailsI)+
proof -
  fix x
  assume hyp: "x \<le> S x = 1"
  show "x N \<Longrightarrow> S x \<le> S S x = 1"
    by (unfold_def def_leq, simp, rule hyp)
qed

lemma less_suc [simp, auto]:
  shows "x N \<Longrightarrow> x < S(x) = 1"
apply (rule ind[where a="x"], simp)
apply (unfold_def def_less, simp)
apply (rule forallI entailsI)+
apply (unfold_def def_less, simp)
done

lemma [auto]: "x N \<Longrightarrow> \<not> 0 = S x"
apply (fold neq_def)
apply (rule neq_sym)
apply (simp)
done

lemma leq_0:
  shows "x N \<Longrightarrow> x \<le> 0 = 1 \<Longrightarrow> x = 0"
proof (rule grounded_contradiction[where q="False"])
  show "x N \<Longrightarrow> x = 0 B" by (simp)
  show "x N \<Longrightarrow> x \<le> 0 = 1 \<Longrightarrow> \<not> x = 0 \<Longrightarrow> False"
    apply (rule exF[where P="x \<le> 0 = 1"])
    apply (simp)
    apply (rule eqSubst[where a="0" and b="x \<le> 0"])
    apply (unfold_def def_leq)
    apply (simp+)
    done
  show "\<not>False" by (simp)
qed

lemma leq_monotone_suc [simp]:
  shows "x N \<Longrightarrow> y N \<Longrightarrow> x \<le> y = 1 \<Longrightarrow> S x \<le> S y = 1"
by (unfold_def def_leq, simp)

lemma num_cases:
  shows "x N \<Longrightarrow> x = 0 \<or> (\<exists>y. x = S y)"
proof (rule ind[where a="x"], simp)
  show "0 = 0 \<or> (\<exists>y. 0 = S y)" by (rule disjI1, simp)
  show "\<forall>x. x=0 \<or> (\<exists>y. x = S y) \<turnstile> S x = 0 \<or> (\<exists>y. S x = S y)"
    proof (rule forallI entailsI)+
      fix x
      show "x N \<Longrightarrow> S x = 0 \<or> (\<exists>y. S x = S y)"
        apply (rule disjI2)
        apply (rule existsI[where a="x"])
        apply (simp)
        done
    qed
qed

lemma num_non_zero [auto]:
  "x N \<Longrightarrow> \<not> x = 0 \<Longrightarrow> \<exists>y. x = S(y)"
proof -
  have "x N \<Longrightarrow> x = 0 \<or> (\<exists>y. x = S y)"
    by (rule num_cases, simp)
  then show "x N \<Longrightarrow> \<not> x = 0 \<Longrightarrow> \<exists>y. x = S(y)"
    apply (rule disjE1, simp)
    apply (rule exF[where P="x=0"], simp)
    done
qed

lemma leq_nz_monotone:
  shows "ya N \<Longrightarrow> \<not> xa = 0 \<Longrightarrow> xa \<le> ya = 1 \<Longrightarrow> ya \<noteq> 0"
proof (rule grounded_contradiction[where q="xa \<le> 0 = 1"])
  show "ya N \<Longrightarrow> ya \<noteq> 0 B" by (simp)
  show "\<not> ya \<noteq> 0 \<Longrightarrow> xa \<le> ya = 1 \<Longrightarrow> xa \<le> 0 = 1"
    proof -
      assume H: "\<not> ya \<noteq> 0"
      have ya_nz: "ya = 0" by (rule dNegE, fold neq_def, rule H)
      show "xa \<le> ya = 1 \<Longrightarrow> xa \<le> 0 = 1"
        apply (rule eqSubst[where a="ya" and b="0"])
        apply (rule ya_nz)
        apply (rule eqSubst[where a="1" and b="S ya"])
        apply (rule sucCong)
        apply (rule eqSym)
        apply (rule ya_nz)
        apply (simp)
        done
    qed
  show "\<not> xa = 0 \<Longrightarrow> \<not> xa \<le> 0 = 1"
    apply (rule eqSubst[where a="0" and b="xa \<le> 0"])
    apply (rule eqSym)
    apply (unfold_def def_leq)
    apply (simp)
    done
qed

lemma leq_0_if_nz [auto]:
  shows "\<not> x = 0 \<Longrightarrow> x \<le> 0 = 0"
by (unfold_def def_leq, simp)

lemma leq_suc_eq:
  shows "x N \<Longrightarrow> y N \<Longrightarrow> x \<le> y = S x \<le> S y"
proof (rule ind[where a="y"])
  show "y N \<Longrightarrow> y N" by (assumption)
  show "x N \<Longrightarrow> x \<le> 0 = S x \<le> S 0"
    apply (rule disjE1[where P="x = 0" and Q="\<not> x = 0"])
    apply (fold bJudg_def)
    apply (simp+)
    apply (rule eqSubst[where a="0"])
    apply (rule eqSym)
    apply (unfold_def def_leq)
    apply (simp+)
    done
  show "x N \<Longrightarrow> y N \<Longrightarrow> \<forall>xa. x \<le> xa = S(x) \<le> S(xa) \<turnstile> x \<le> S(xa) = S(x) \<le> S(S(xa))"
    proof (rule forallI entailsI)+
      fix xa
      assume H: "x \<le> xa = S x \<le> S xa"
      show "x N \<Longrightarrow> y N \<Longrightarrow> xa N \<Longrightarrow> x \<le> S xa = S x \<le> S S xa"
        by (unfold_def def_leq, simp)
    qed
qed

lemma suc_pred_inv [simp, auto]:
  shows "x N \<Longrightarrow> \<not> x = 0 \<Longrightarrow> S P x = x"
proof -
  have "x N \<Longrightarrow> \<not> x = 0 \<Longrightarrow> \<exists>u. x = S(u)" by (simp)
  then show "x N \<Longrightarrow> \<not> x = 0 \<Longrightarrow> S P x = x"
    proof (rule existsE)
      fix a
      show "a N \<Longrightarrow> x = S a \<Longrightarrow> S P x = x"
        by (simp)
    qed
qed

lemma cases_nat_2:
  assumes x_z: "x = 0 \<Longrightarrow> Q 0"
  assumes x_nz: "\<And>y. y N \<Longrightarrow> x = S(y) \<Longrightarrow> Q S(y)"
  shows "x N \<Longrightarrow> Q x"
apply (rule disjE1[where P="x = 0" and Q="\<not> x = 0"])
apply (fold bJudg_def)
apply (simp+)
apply (rule x_z)
apply (simp)
apply (rule existsE[where Q="\<lambda>c. x = S(c)"])
apply (simp)
apply (fold neq_def)
proof -
  fix a
  show "a N \<Longrightarrow> x = S a \<Longrightarrow> Q x"
    by (simp, rule x_nz)
qed

lemma cases_nat:
  assumes x_z: "x = 0 \<Longrightarrow> Q 0"
  assumes x_nz: "\<not> x = 0 \<Longrightarrow> Q x"
  shows "x N \<Longrightarrow> Q x"
apply (rule disjE1[where P="x = 0" and Q="\<not> x = 0"])
apply (fold bJudg_def)
apply (simp+)
apply (rule x_z, simp)+
apply (rule x_nz, simp)+
done

lemma leq_monotone_pred:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes H: "x \<le> y = 1"
  shows "P x \<le> P y = 1"
proof (rule cases_nat[where x="x"])
  show "x N" by (rule x_nat)
  show "x = 0 \<Longrightarrow> P 0 \<le> P y = 1"
    apply (rule eqSubst[where a="0" and b="P 0"])
    apply (rule eqSym)
    apply (auto)
    apply (rule y_nat)
    done
  show "\<not> x = 0 \<Longrightarrow> P x \<le> P y = 1"
  proof (rule cases_nat[where x="y"])
    show "y N" by (rule y_nat)
    show "\<not> x = 0 \<Longrightarrow> y = 0 \<Longrightarrow> P x \<le> P 0 = 1"
      apply (rule exF[where P="x \<le> y = 1"])
      apply (rule H)
      apply (rule eqSubst[where a="0" and b="x \<le> y"])
      apply (rule eqSym)
      apply (simp+)
      done
    show "\<not> x = 0 \<Longrightarrow> \<not> y = 0 \<Longrightarrow> P x \<le> P y = 1"
    proof -
      assume x_nz: "\<not> x = 0"
      assume y_nz: "\<not> y = 0"
      have H1: "P x \<le> P y = S P x \<le> S P y"
        apply (rule leq_suc_eq)
        apply (simp)
        apply (rule x_nat)
        apply (simp)
        apply (rule y_nat)
        done
      have H2: "P x \<le> P y = x \<le> y"
        apply (rule eqSubst[where a="S P x" and b="x"])
        apply (simp)
        apply (rule x_nat)
        apply (rule x_nz)
        apply (rule eqSubst[where a="S P y" and b="y"])
        apply (simp)
        apply (rule y_nat)
        apply (rule y_nz)
        apply (rule eqSubst[where a="P x" and b="P S P x"])
        apply (rule eqSym)
        apply (simp+)
        apply (rule x_nat)
        apply (rule eqSubst[where a="P y" and b="P S P y"])
        apply (rule eqSym)
        apply (rule predSucInv)
        apply (auto)
        apply (rule y_nat)
        apply (rule H1)
        done
      show ?thesis
        apply (rule eqSubst[where a="x \<le> y" and b="1"])
        apply (rule H)
        apply (rule H2)
        done
    qed
  qed
qed

lemma [auto]: "x N \<Longrightarrow> y N \<Longrightarrow> S x \<le> S y = x \<le> y"
apply (rule eqSym)
apply (unfold_def def_leq)
apply (rule eqSym, simp)
done

lemma suc_leq_mono: "x N \<Longrightarrow> y N \<Longrightarrow> S x \<le> S y = 1 \<Longrightarrow> x \<le> y = 1"
apply (rule eqSubst[where b="x \<le> y" and a="S x \<le> S y"])
apply (auto)
done

lemma leq_trans:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes z_nat: "z N"
  assumes x_leq_y: "x \<le> y = 1"
  assumes y_leq_z: "y \<le> z = 1"
  shows "x \<le> z = 1"
proof -
  have quantized: "\<forall>x y. (x \<le> y = 1) \<turnstile> (y \<le> z = 1) \<turnstile> (x \<le> z = 1)"
  proof (rule ind[where a="z"])
  show "z N" by (rule z_nat)
  show "\<forall>x y. x \<le> y = 1 \<turnstile>
    y \<le> 0 = 1 \<turnstile> x \<le> 0 = 1"
    proof (rule forallI entailsI)+
      fix xa ya
      assume xa_nat: "xa N"
      assume ya_nat: "ya N"
      assume H: "ya \<le> 0 = 1"
      assume H1: "xa \<le> ya = 1"
      have ya_zero: "ya = 0" by (rule leq_0, rule ya_nat, rule H)
      show "xa \<le> 0 = 1"
        apply (rule eqSubst[where a="ya" and b="0"])
        apply (rule eqSubst[where a="1" and b="S(ya)"])
        apply (rule sucCong)
        apply (rule eqSym)
        apply (rule ya_zero)+
        apply (rule eqSubst[where a="1" and b="S(ya)"])
        apply (simp add: ya_zero)
        apply (rule H1)
        done
    qed
  show "\<forall>x. (\<forall>xa y. xa \<le> y = 1 \<turnstile> y \<le> x = 1 \<turnstile> xa \<le> x = 1) \<turnstile>
     (\<forall>xa y. xa \<le> y = 1 \<turnstile> y \<le> S x = 1 \<turnstile> xa \<le> S x = 1)"
    proof (rule forallI, rule entailsI)+
      fix x
      show "x N \<Longrightarrow> \<forall>xa y. xa \<le> y = 1 \<turnstile> y \<le> x = 1 \<turnstile> xa \<le> x = 1 \<Longrightarrow>
            \<forall>xa y. xa \<le> y = 1 \<turnstile> y \<le> S x = 1 \<turnstile> xa \<le> S x = 1"
        proof -
          assume hyp: "\<forall>xa y. xa \<le> y = 1 \<turnstile> y \<le> x = 1 \<turnstile> xa \<le> x = 1"
          show "x N \<Longrightarrow> \<forall>xa y. xa \<le> y = 1 \<turnstile> y \<le> S x = 1 \<turnstile> xa \<le> S x = 1"
            proof (rule forallI entailsI)+
              fix xa ya
              assume xa_leq_ya: "xa \<le> ya = 1"
              assume ya_leq_sx: "ya \<le> S x = 1"
              show "x N \<Longrightarrow> xa N \<Longrightarrow> ya N \<Longrightarrow> xa \<le> S x = 1"
                apply (unfold_def def_leq)
                apply (rule condI3Eq)
                apply (simp+)
                apply (rule entailsE[where a="(P ya) \<le> x = 1"])
                apply (rule entailsE[where a="(P xa) \<le> (P ya) = 1"])
                apply (rule forallE[where Q="\<lambda>a. (P xa) \<le> a = 1 \<turnstile> a \<le> x = 1 \<turnstile> (P xa) \<le> x = 1"])
                apply (rule forallE[where Q="\<lambda>a. (\<forall>c'. a \<le> c' = 1 \<turnstile> c' \<le> x = 1 \<turnstile> a \<le> x = 1)"])
                apply (rule hyp, simp)
                apply (rule leq_monotone_pred, simp)
                apply (rule xa_leq_ya)
                apply (rule suc_leq_mono)
                apply (simp)
                apply (rule eqSubst[where a="ya" and b="S P ya"])
                apply (rule eqSym)
                apply (rule suc_pred_inv, simp)
                apply (fold neq_def)
                apply (rule leq_nz_monotone[where xa="xa"])
                apply (simp+)
                apply (rule xa_leq_ya)
                apply (rule ya_leq_sx)
                done
           qed
        qed
     qed
  qed
  then have "\<forall>y. (x \<le> y = 1) \<turnstile> (y \<le> z = 1) \<turnstile> (x \<le> z = 1)"
    apply (rule forallE)
    apply (rule x_nat)
    done
  then have "(x \<le> y = 1) \<turnstile> (y \<le> z = 1) \<turnstile> (x \<le> z = 1)"
    apply (rule forallE)
    apply (rule y_nat)
    done
  then have "(y \<le> z = 1) \<turnstile> (x \<le> z = 1)"
    apply (rule entailsE)
    apply (rule x_leq_y)
    done
  then show ?thesis
    apply (rule entailsE)
    apply (rule y_leq_z)
    done
qed

lemma zero_less_true [simp, auto]: "a N \<Longrightarrow> 0 < S(a) = 1"
by (unfold_def def_less, simp)

lemma sub_0 [simp, auto]: "x N \<Longrightarrow> x - 0 = x"
by (unfold_def def_sub, simp)

lemma zero_div [simp, auto]: "x N \<Longrightarrow> div 0 S(x) = 0"
by (unfold_def def_div, simp)

lemma div_1 [simp, auto]:
  assumes x_nat: "x N"
  shows "x N \<Longrightarrow> div x 1 = x"
proof (rule ind, simp, rule forallI, rule entailsI)
  fix xa
  assume ind_h: "div xa 1 = xa"
  show "xa N \<Longrightarrow> div S(xa) 1 = S(xa)"
    apply (unfold_def def_div)
    apply (rule eqSubst[where a="xa" and b="div ((S(xa))-1) 1"])
    apply (rule eqSubst[where a="xa" and b="(S(xa))-1"])
    apply (unfold_def def_sub)
    apply (simp+)
    apply (rule eqSym)
    apply (rule ind_h)
    apply (rule condI2)
    apply (rule eqSubst[where a="0" and b="S xa < 1"])
    apply (rule eqSym)
    apply (unfold_def def_less)
    apply (simp+)
    done
qed

lemma leq_0_then_0:
  shows "x N \<Longrightarrow> x \<le> 0 = 1 \<Longrightarrow> x = 0"
apply (rule grounded_contradiction[where q="x \<le> 0 = 1"])
apply (simp)
apply (rule eqSubst[where a="0" and b="x \<le> 0"])
apply (rule eqSym)
apply (unfold_def def_leq)
apply (simp+)
done

lemma neq_monotone_suc:
  shows "x N \<Longrightarrow> y N \<Longrightarrow> \<not> x = y \<Longrightarrow> \<not> S x = S y"
apply (rule grounded_contradiction[where q="x = y"])
apply (simp)
apply (rule sucInj)
apply (rule dNegE)
apply (simp)
done

lemma neq_monotone_pred:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes x_nz: "\<not> x = 0"
  assumes y_nz: "\<not> y = 0"
  assumes x_neq_y: "\<not> x = y"
  shows "\<not> P x = P y"
proof (rule GD.grounded_contradiction[where q="x = y"])
  show "\<not> P x = P y B" by (auto, rule x_nat, rule y_nat)
  show "\<not>\<not> P x = P y \<Longrightarrow> x = y"
    proof -
      assume H: "\<not> \<not> P x = P y"
      then have H2: "P x = P y"
        by (rule dNegE)
      then have H3: "S P x = S P y"
        by (rule sucCong)
      show ?thesis
        apply (rule eqSubst[where a="S P x" and b="x"])
        apply (rule suc_pred_inv)
        apply (rule x_nat)
        apply (rule x_nz)
        apply (rule eqSubst[where a="S P y" and b="y"])
        apply (rule suc_pred_inv)
        apply (rule y_nat)
        apply (rule y_nz)
        apply (rule H3)
        done
    qed
  show "\<not>\<not> P x = P y \<Longrightarrow> \<not> x = y" by (rule x_neq_y)
qed

lemma less_is_leq_neq:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes x_leq_y: "x \<le> y = 1"
  assumes x_neq_y: "\<not> x = y"
  shows "x < y = 1"
proof -
  have "\<forall>x. x \<le> y = 1 \<turnstile> \<not> x = y \<turnstile> x < y = 1"
  proof (rule ind[where a="y"])
    show "y N" by (rule y_nat)
    show "\<forall>x. x \<le> 0 = 1 \<turnstile> \<not> x = 0 \<turnstile> x < 0 = 1"
      proof (rule forallI entailsI)+
        fix x
        assume x_nat: "x N"
        assume x_leq_0: "x \<le> 0 = 1"
        assume x_nz: "\<not> x = 0"
        show "x N \<Longrightarrow> x \<le> 0 = 1 \<Longrightarrow> \<not>x = 0 \<Longrightarrow> x < 0 = 1"
          apply (rule exF[where P="x = 0"])
          apply (rule leq_0_then_0)
          apply (simp)
          done
      qed
    show "\<forall>x. (\<forall>xa. xa \<le> x = 1 \<turnstile> \<not> xa = x \<turnstile> xa < x = 1) \<turnstile>
     (\<forall>xa. xa \<le> S x = 1 \<turnstile> \<not> xa = S x \<turnstile> xa < S x = 1)"
      proof (rule forallI entailsI)+
        fix x xa
        assume x_nat: "x N"
        assume xa_nat: "xa N"
        assume hyp: "\<forall>xa. xa \<le> x = 1 \<turnstile> \<not> xa = x \<turnstile> xa < x = 1"
        assume xa_leq_sx: "xa \<le> S x = 1"
        assume xa_neq_sx: "\<not> xa = S x"
        have H: "P xa \<le> P S x = 1"
          by (rule leq_monotone_pred, rule xa_nat, rule natS, rule x_nat, rule xa_leq_sx)
        have p_xa_leq_x: "P xa \<le> x = 1"
          by (rule eqSubst[where a="P S x" and b="x"], auto, rule x_nat, rule H)
        show "xa < S x = 1 "
          apply (unfold_def def_less)
          apply (rule condI2Eq)
          apply (fold neq_def)
          apply (simp)
          apply (rule x_nat)
          apply (simp)
          apply (rule cases_nat[where x="xa"])
          apply (rule condI1)
          apply (rule zeroRefl)
          apply (simp)
          apply (rule eqSubst[where a="x" and b="P S x"])
          apply (rule eqSym)
          apply (auto)
          apply (rule x_nat)
          proof -
            show "xa N" by (rule xa_nat)
            assume xa_nz: "\<not> xa = 0"
            have H2: "\<not> P xa = P S x"
              apply (rule neq_monotone_pred)
              apply (rule xa_nat)
              apply (rule natS)
              apply (rule x_nat)
              apply (rule xa_nz)
              apply (fold neq_def)
              apply (auto)
              apply (rule x_nat)
              apply (unfold neq_def)
              apply (rule xa_neq_sx)
              done
            have pxa_neq_x: "\<not> P xa = x"
              apply (rule eqSubst[where a="P S x" and b="x"])
              apply (rule predSucInv)
              apply (rule x_nat)
              apply (rule H2)
              done
            have "P xa \<le> x = 1 \<turnstile> \<not> P xa = x \<turnstile> P xa < x = 1"
              apply (rule forallE[where a="P xa"])
              apply (rule hyp)
              apply (rule natP)
              apply (rule xa_nat)
              done
            then have "\<not> P xa = x \<turnstile> P xa < x = 1"
              apply (rule entailsE)
              apply (rule p_xa_leq_x)
              done
            then show "P xa < x = 1"
              apply (rule entailsE)
              apply (rule pxa_neq_x)
              done
        qed
      qed
  qed
  then have "x \<le> y = 1 \<turnstile> \<not> x = y \<turnstile> x < y = 1"
    apply (rule forallE)
    apply (rule x_nat)
    done
  then have "\<not> x = y \<turnstile> x < y = 1"
    apply (rule entailsE)
    apply (rule x_leq_y)
    done
  then show "x < y = 1"
    apply (rule entailsE)
    apply (rule x_neq_y)
    done
qed

lemma x_less_1_is_0:
  assumes x_nat: "x N"
  assumes H: "x < 1 = 1"
  shows "x = 0"
proof (rule grounded_contradiction[where q="x < 1 = 0"])
  show "x = 0 B"
    by (rule eqBool, rule x_nat, auto)
  show "\<not> x = 0 \<Longrightarrow> x < 1 = 0"
    apply (unfold_def def_less)
    apply (rule condI2Eq)
    apply (fold neq_def)
    apply (auto)
    apply (rule condI2Eq)
    apply (unfold neq_def)
    apply (auto)
    apply (rule eqSubst[where a="0" and b="P S 0"])
    apply (rule eqSym)
    apply (auto)
    done
  show "\<not> x = 0 \<Longrightarrow> \<not> x < 1 = 0"
      apply (rule eqSubst[where a="1" and b="x < 1"])
      apply (rule eqSym)
      apply (rule H)
      apply (fold neq_def)
      apply (auto)
      done
qed

lemma le_monotone_suc [auto]:
  shows "x < y = 1 \<Longrightarrow> x N \<Longrightarrow> y N \<Longrightarrow> S x < S y = 1"
by (unfold_def def_less, simp)

lemma le_monotone_pred:
  assumes x_nat: "x N"
  assumes x_nz: "\<not> x = 0"
  assumes y_nat: "y N"
  assumes x_le_y: "x < y = 1"
  shows "x N \<Longrightarrow> y N \<Longrightarrow> \<not> x = 0 \<Longrightarrow> x < y = 1 \<Longrightarrow> P x < P y = 1"
apply (rule grounded_contradiction[where q="x < y = 1"])
apply (simp)
apply (unfold_def def_less)
apply (rule cases_nat[where x="y"])
apply (rule eqSubst[where a="0" and b="(if 0 = 0 then 0 else
  if x = 0 then 1 else (P x < P 0))"])
apply (simp+)
done

lemma le_suc_implies_leq:
  assumes x_le_sy: "x < S y = 1"
  shows "x N \<Longrightarrow> y N \<Longrightarrow> x \<le> y = 1"
proof -
  have "x N \<Longrightarrow> y N \<Longrightarrow> \<forall>x. x < S y = 1 \<turnstile> x \<le> y = 1"
  proof (rule ind[where a="y"], auto)
    show "x N \<Longrightarrow> y N \<Longrightarrow> \<forall>x. x < 1 = 1 \<turnstile> x \<le> 0 = 1"
      proof (rule forallI entailsI)+
        fix x
        assume x_le_sy: "x < 1 = 1"
        show "x N \<Longrightarrow> x \<le> 0 = 1"
          apply (unfold_def def_leq)
          apply (rule condI1)
          apply (rule x_less_1_is_0)
          apply (auto)
          apply (rule x_le_sy)
          apply (auto)
          done
      qed
    show "\<forall>x. (\<forall>xa. xa < S x = 1 \<turnstile> xa \<le> x = 1) \<turnstile>
     (\<forall>xa. xa < S S x = 1 \<turnstile> xa \<le> S x = 1)"
      proof (rule forallI entailsI)+
        fix x xa
        assume x_nat: "x N"
        assume xa_nat: "xa N"
        assume hyp: "\<forall>xa. xa < S x = 1 \<turnstile> xa \<le> x = 1"
        have hyp_inst: "P xa < S x = 1 \<turnstile> P xa \<le> x = 1"
          apply (rule forallE[where a="P xa"])
          apply (rule hyp)
          apply (auto)
          apply (rule xa_nat)
          done
        assume xa_le_ssx: "xa < S S x = 1"
        show "x N \<Longrightarrow> xa N \<Longrightarrow> xa \<le> S x = 1"
          apply (unfold_def def_leq)
          apply (rule cases_nat[where x="xa"])
          apply (rule condI1)
          apply (simp+)
          apply (rule entailsE[where a="P xa < S x = 1"])
          apply (rule hyp_inst)
          apply (rule eqSubst[where a="P S S x" and b = "S x"])
          apply (simp)
          apply (rule le_monotone_pred)
          apply (rule xa_nat)
          apply (simp add: xa_le_ssx)+
          done
      qed
  qed
  then have "x N \<Longrightarrow> y N \<Longrightarrow> x < S y = 1 \<turnstile> x \<le> y = 1"
    by (rule forallE, simp)
  then show "x N \<Longrightarrow> y N \<Longrightarrow> x \<le> y = 1"
    apply (rule entailsE, simp)
    apply (rule x_le_sy)
    done
qed

lemma leq_suc_not_leq_implies_eq:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes x_ge_y: "\<not> x \<le> y = 1"
  assumes x_le_sy: "x \<le> S y = 1"
  shows "x = S y"
proof (rule contradiction)
  show "x = S(y) B" by (rule eqBool, rule x_nat, rule natS, rule y_nat)
  show "\<not> x = S(y) \<Longrightarrow> False"
    proof -
      assume x_neq_sy: "\<not> x = S y"
      have H: "x < S y = 1"
        apply (rule less_is_leq_neq)
        apply (rule x_nat)
        apply (rule natS)
        apply (rule y_nat)
        apply (rule x_le_sy)
        apply (rule x_neq_sy)
        done
      have H4: "x \<le> y = 1"
        apply (rule le_suc_implies_leq)
        apply (rule H)
        apply (rule x_nat, rule y_nat)
        done
      show "False"
        apply (rule exF[where P="x \<le> y = 1"])
        apply (rule H4)
        apply (rule x_ge_y)
        done
    qed
qed

lemma strong_induction:
  assumes a_nat: "a N"
  assumes bc: "Q 0"
  assumes step: "\<forall>x.((\<forall>y. y\<le>x = 1 \<turnstile> Q y) \<turnstile> (Q S(x)))"
  shows "Q a"
proof -
  have q: "\<forall>x. (x \<le> a = 1) \<turnstile> Q x"
    proof (rule ind[where a="a"])
      show "a N" by (rule a_nat)
      show "\<forall>x. x \<le> 0 = 1 \<turnstile> Q x"
        proof (rule forallI entailsI)+
          fix x
          assume x_nat: "x N"
          assume x_le_0: "x \<le> 0 = 1"
          have x_zero: "x = 0"
            apply (rule leq_0_then_0)
            apply (rule x_nat)
            apply (rule x_le_0)
            done
          show "Q x"
            apply (rule eqSubst[where a="0" and b="x"])
            apply (rule eqSym)
            apply (rule x_zero)
            apply (rule bc)
            done
        qed
      show "\<forall>x. (\<forall>xa. xa \<le> x = 1 \<turnstile> Q xa) \<turnstile> (\<forall>xa. xa \<le> S x = 1 \<turnstile> Q xa)"
        proof (rule forallI entailsI)+
          fix x xa
          assume x_nat: "x N"
          assume xa_nat: "xa N"
          assume hyp: "\<forall>x'. x' \<le> x = 1 \<turnstile> Q x'"
          assume xa_leq_sx: "xa \<le> S x = 1"
          have H: "xa \<le> x = 1 \<turnstile> Q xa"
            apply (rule forallE[where a="xa"])
            apply (rule hyp)
            apply (rule xa_nat)
            done
          show "Q xa"
            apply (rule disjE1[where P="xa \<le> x = 1" and Q="\<not> xa \<le> x = 1"])
            apply (fold GD.bJudg_def)
            apply (rule eqBool)
            apply (rule leq_terminates)
            apply (rule xa_nat)
            apply (rule x_nat)
            apply (auto)
            apply (rule entailsE[where a="xa \<le> x = 1"])
            apply (rule H)
            apply (assumption)
            proof -
              assume xa_not_leq_x: "\<not> xa \<le> x = 1"
              have xa_eq_sx: "xa = S x"
                apply (rule leq_suc_not_leq_implies_eq)
                apply (rule xa_nat)
                apply (rule x_nat)
                apply (rule xa_not_leq_x)
                apply (rule xa_leq_sx)
                done
              have "(\<forall>y. y\<le>x = 1 \<turnstile> Q y) \<turnstile> (Q S(x))"
                apply (rule forallE[where a="x"])
                apply (rule step)
                apply (rule x_nat)
                done
              then have q_sx: "Q S(x)"
                apply (rule entailsE)
                apply (rule hyp)
                done
              show "Q xa"
                apply (rule eqSubst[where a="S x" and b="xa"])
                apply (rule eqSym)
                apply (rule xa_eq_sx)
                apply (rule q_sx)
                done
            qed
        qed
    qed
    then have "a \<le> a = 1 \<turnstile> Q a"
      apply (rule forallE)
      apply (rule a_nat)
      done
    then show ?thesis
      apply (rule entailsE)
      apply (rule leq_refl)
      apply (rule a_nat)
      done
qed

lemma sub_terminates [auto]:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "x - y N"
proof (rule ind[where a=y])
  show habeas_quid_cond: "y N" by (rule y_nat)
  show base_case: "x - 0 N"
    apply (unfold_def def_sub)
    apply (rule eqSubst[where a="x"])
    apply (rule eqSym)
    apply (rule condI1)
    apply (rule zeroRefl)
    apply (rule x_nat)
    apply (rule x_nat)
    done
  show ind_step: "\<forall>a. ((x - a) N) \<turnstile> ((x - S(a)) N)"
    proof (rule forallI, rule entailsI, unfold_def def_sub)
      fix a
      assume HQ: "a N" and BC: "x - a N"
      show "if (S(a) = 0) then x else P(x - P(S(a))) N"
        proof (rule GD.condT)
          show "S(a) = 0 B"
            apply (rule GD.eqBool)
            apply (rule GD.natS)
            apply (rule HQ)
            apply (rule GD.nat0)
            done
          show "x N" by (rule x_nat)
          show "P(x - P(S(a))) N"
            apply (rule natP)
            apply (rule eqSubst[where a="x-a"])
            apply (rule eqSubst[where a="a" and b="P(S(a))"])
            apply (rule eqSym)
            apply (rule predSucInv)
            apply (rule HQ)
            apply (fold isNat_def)
            apply (rule BC)
            apply (rule BC)
            done
        qed
    qed
qed

lemma sub_nz_leq_pred:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "(S x) - (S y) \<le> x = 1"
proof -
  have "\<forall>x. (S x) - (S y) \<le> x = 1"
  proof (rule ind[where a="y"])
    show "y N" by (rule y_nat)
    show "\<forall>x. S x - 1 \<le> x = 1"
      proof (rule forallI)
        fix x
        assume x_nat: "x N"
        show "S x - 1 \<le> x = 1"
          apply (rule eqSubst[where a="x" and b="S x - 1"])
          apply (rule eqSym)
          apply (unfold_def def_sub)
          apply (rule condI2Eq)
          apply (fold neq_def)
          apply (auto)
          apply (rule x_nat)
          apply (rule eqSubst[where a="0" and b="P S 0"])
          apply (rule eqSym)
          apply (auto)
          apply (rule eqSubst[where a="S x" and b="S x - 0"])
          apply (rule eqSym)
          apply (auto)
          apply (rule x_nat)
          apply (auto)
          apply (rule x_nat)
          apply (auto)
          apply (rule x_nat)
          done
      qed
    show "\<forall>x. (\<forall>xa. S xa - S x \<le> xa = 1) \<turnstile> (\<forall>xa. S xa - S S x \<le> xa = 1)"
      proof (rule forallI entailsI)+
        fix x xa
        assume x_nat: "x N" and xa_nat: "xa N"
        assume hyp: "\<forall>xa. S xa - S x \<le> xa = 1"
        then have H: "S xa - S x \<le> xa = 1"
          apply (rule forallE)
          apply (rule xa_nat)
          done
        have H2: "P(S xa - S x) \<le> xa = 1"
          apply (rule leq_trans[where y="S xa - S x"])
          apply (auto)
          apply (rule xa_nat)
          apply (rule x_nat)
          apply (auto)
          apply (rule xa_nat)
          apply (rule x_nat)
          apply (rule xa_nat)
          apply (auto)
          apply (rule xa_nat)
          apply (rule x_nat)
          apply (rule H)
          done
        show "S xa - S S x \<le> xa = 1"
          apply (unfold_def def_sub)
          apply (rule eqSubst[where a="P(S xa - S x)" and b="(if S S x = num_zero then S xa else P(S xa - P S S x))"])
          apply (rule eqSym)
          apply (rule condI2Eq)
          apply (fold neq_def)
          apply (auto)
          apply (rule x_nat)
          apply (auto)
          apply (rule xa_nat)
          apply (rule x_nat)
          apply (rule eqSubst[where a="S x" and b="P S S x"])
          apply (rule eqSym)
          apply (auto)
          apply (rule x_nat)
          apply (fold isNat_def)
          apply (auto)
          apply (rule xa_nat)
          apply (rule x_nat)
          apply (rule H2)
          done
      qed
  qed
  then show ?thesis
    apply (rule forallE)
    apply (rule x_nat)
    done
qed

lemma div_terminates [auto]:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "div x S(y) N"
proof (rule strong_induction[where a="x"])
  show "x N" by (rule x_nat)
  show "div 0 S(y) N"
    apply (rule eqSubst[where a="0"])
    apply (rule eqSym)
    apply (unfold_def def_div)
    apply (rule condI1)
    apply (auto)
    apply (rule y_nat)
    apply (auto)
    done
  show "\<forall>x. (\<forall>ya. ya \<le> x = 1 \<turnstile> div ya (S y) N) \<turnstile> div (S x) (S y) N "
    proof (rule forallI entailsI)+
      fix x
      assume x_nat: "x N"
      assume hyp: "\<forall>ya. ya \<le> x = 1 \<turnstile> div ya (S y) N"
      then have "S x - S y \<le> x = 1 \<turnstile> div (S x - S y) (S y) N"
        apply (rule forallE)
        apply (rule sub_terminates)
        apply (auto)
        apply (rule x_nat)
        apply (auto)
        apply (rule y_nat)
        done
      then have H2: "div (S x - S y) (S y) N"
        apply (rule entailsE)
        apply (rule sub_nz_leq_pred)
        apply (rule x_nat)
        apply (rule y_nat)
        done
      show "div (S x) (S y) N"
        apply (unfold_def def_div)
        apply (rule condT)
        apply (auto)
        apply (rule x_nat)
        apply (rule y_nat)
        apply (auto)
        apply (rule H2)
        done
    qed
qed

lemma suc_sq_gr:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "S y * S x > x = 1"
proof -
  have "\<forall>y. S y * S x > x = 1"
    proof (rule ind[where a="x"])
      show "x N" by (rule x_nat)
      show "\<forall>y. S y * 1 > 0 = 1"
        proof (rule forallI)
          fix y
          assume y_nat: "y N"
          show "S y * 1 > 0 = 1"
            apply (rule eqSubst[where a="S y" and b="S y * 1"])
            apply (unfold_def def_mult)
            apply (rule eqSym)
            apply (rule condI2Eq)
            apply (fold neq_def)
            apply (auto)
            apply (rule y_nat)
            apply (rule eqSubst[where a="0" and b="S y * P S 0"])
            apply (rule eqSubst[where a="0" and b="P S 0"])
            apply (rule eqSym)
            apply (auto)
            apply (rule eqSym)
            apply (auto)
            apply (rule y_nat)
            apply (unfold greater_def)
            apply (rule eqSubst[where a="0" and b="S y\<le>0"])
            apply (rule eqSym)
            apply (auto)
            apply (rule y_nat)
            apply (auto)
            done
        qed
      show "\<forall>x. (\<forall>y. S y * S x > x = 1) \<turnstile> (\<forall>y. S y * S S x > S x = 1)"
        proof (rule forallI entailsI)+
          fix x y
          assume x_nat: "x N" and y_nat: "y N" and hyp: "\<forall>y. S y * S x > x = 1"
          show "S y * S S x > S x = 1"
            sorry
        qed
    qed
    then show "S y * S x > x = 1"
      sorry
qed

lemma sqrt_h_bounded:
  assumes x_nat: "x N"
  shows"\<exists>y. sqrt_h x y = y"
apply (rule existsI[where a="x"])
apply (rule x_nat)
apply (unfold_def def_sqrt_h)
apply (rule condI1Eq)
apply (rule suc_sq_gr)
apply (rule x_nat)
apply (rule x_nat)
apply (rule x_nat)
apply (fold isNat_def)
apply (rule x_nat)
done

lemma sqrt_h_terminates [auto]:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "sqrt_h x y N"
apply (rule existsE[where Q="\<lambda>a. sqrt_h x a = a"])
apply (rule sqrt_h_bounded)
apply (rule x_nat)
proof -
  fix a
  assume a_nat: "a N"
  assume "sqrt_h x a = a"
  let ?d = "a - y"
  have "?d = ?d \<turnstile> sqrt_h x y N"
    apply (rule ind[where a="a-y"])
    apply (auto)
    apply (rule a_nat)
    apply (rule y_nat)
    sorry
  then show ?thesis
    sorry
qed

lemma floor_sqrt_terminates [auto]:
  assumes x_nat: "x N"
  shows "floor_sqrt x N"
apply (unfold floor_sqrt_def)
apply (auto)
apply (rule x_nat)
done

definition cpair :: "num \<Rightarrow> num \<Rightarrow> num" where
  "cpair x y \<equiv> y + (div ((x+y) * (S(x+y))) 2)"

nonterminal cpair_args

syntax
  "_cpair"      :: "num \<Rightarrow> cpair_args \<Rightarrow> num"        ("\<langle>_,_\<rangle>")
  "_cpair_arg"  :: "num \<Rightarrow> cpair_args"               ("_")
  "_cpair_args" :: "num \<Rightarrow> cpair_args \<Rightarrow> cpair_args" ("_,_")
translations
  "\<langle>x, y\<rangle>" == "CONST cpair x y"
  "_cpair x (_cpair_args y z)" == "_cpair x (_cpair_arg (_cpair y z))"

lemma cpair_terminates [auto]:
  shows "x N \<Longrightarrow> y N \<Longrightarrow> \<langle>x, y\<rangle> N"
apply (unfold cpair_def)
apply (auto)
done

lemma cpair_0_0_0 [simp, auto]: "\<langle>0, 0\<rangle> = 0"
unfolding cpair_def by simp

(* recover w=x+y from the pair z *)
definition cpzw :: "num \<Rightarrow> num" where
  "cpzw z \<equiv> div (floor_sqrt (8 * z + 1) - 1) 2"

(* recover t from w *)
definition cpwt :: "num \<Rightarrow> num" where
  "cpwt w \<equiv> div (w * S(w)) 2"

(* recover y from a pair z *)
definition cpy :: "num \<Rightarrow> num" where
  "cpy z \<equiv> z - (cpwt (cpzw z))"

(* recover x from a pair z *)
definition cpx :: "num \<Rightarrow> num" where
  "cpx z \<equiv> cpzw z - cpy z"

lemma cpzw_terminates [auto]:
  shows "x N \<Longrightarrow> cpzw x N"
by (unfold cpzw_def, simp)

lemma cpwt_terminates [auto]:
  shows "x N \<Longrightarrow> cpwt x N"
by (unfold cpwt_def, simp)

lemma cpy_terminates [auto]:
  assumes x_nat: "x N"
  shows "x N \<Longrightarrow> cpy x N"
by (unfold cpy_def, simp)

lemma cpx_terminates [auto]:
  assumes x_nat: "x N"
  shows "x N \<Longrightarrow> cpx x N"
by (unfold cpx_def, simp)

lemma cpy_proj: "cpy \<langle>a, b\<rangle> = b"
unfolding cpy_def cpwt_def cpzw_def cpair_def
sorry

lemma cpx_proj: "cpx \<langle>a, b\<rangle> = a"
sorry

lemma cpair_inj:
  assumes eq: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle>"
  shows "a N \<Longrightarrow> b N \<Longrightarrow> a = c \<and> b = d"
proof -
  have H: "a N \<Longrightarrow> b N \<Longrightarrow> cpx \<langle>a, b\<rangle> = cpx \<langle>c, d\<rangle>"
    by (rule eqSubst[OF eq], simp)
  have a_eq_c: "a N \<Longrightarrow> b N \<Longrightarrow> a = c"
    apply (rule eqSubst[where a="cpx \<langle>a, b\<rangle>" and b="a"])
    apply (rule cpx_proj)
    apply (rule eqSubst[where a="cpx \<langle>c, d\<rangle>" and b="c"])
    apply (rule cpx_proj)
    apply (rule H)
    apply (simp)
    done
  have H2: "a N \<Longrightarrow> b N \<Longrightarrow> cpy \<langle>a, b\<rangle> = cpy \<langle>c, d\<rangle>"
    by (rule eqSubst[OF eq], simp)
  have b_eq_d: "a N \<Longrightarrow> b N \<Longrightarrow> b = d"
    apply (rule eqSubst[where a="cpy \<langle>a, b\<rangle>" and b="b"])
    apply (rule cpy_proj)
    apply (rule eqSubst[where a="cpy \<langle>c, d\<rangle>" and b="d"])
    apply (rule cpy_proj)
    apply (rule H2)
    apply (simp)
    done
  show "a N \<Longrightarrow> b N \<Longrightarrow> a = c \<and> b = d"
    apply (rule conjI)
    apply (rule a_eq_c)
    apply (simp)
    apply (rule b_eq_d)
    apply (simp)
    done
qed

lemma cpair_inj_l:
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  assumes eq: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle>"
  shows "a = c"
apply (rule conjE1[where q="b=d"])
apply (rule cpair_inj)
apply (rule eq)
apply (rule a_nat)
apply (rule b_nat)
done

lemma cpair_inj_r:
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  assumes eq: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle>"
  shows "b = d"
apply (rule conjE2[where p="a=c"])
apply (rule cpair_inj)
apply (rule eq)
apply (rule a_nat)
apply (rule b_nat)
done

lemma [auto]:
  "\<not>a \<or> \<not>b \<Longrightarrow> \<not> (a \<and> b)"
unfolding conj_def
by (rule dNegI, assumption)

lemma [auto]:
  "a N \<Longrightarrow> b N \<Longrightarrow> c N \<Longrightarrow> d N \<Longrightarrow> \<not> a = c \<or> \<not> b = d \<Longrightarrow> \<not> \<langle>a, b\<rangle> = \<langle>c, d\<rangle>"
apply (rule grounded_contradiction[where q="\<not>(a=c \<and> b=d)"], simp)
apply (rule cpair_inj_l[where b="b" and d="d"], simp)
apply (rule dNegE, assumption)
apply (rule cpair_inj_r[where a="a" and c="c"], simp)
apply (rule dNegE, assumption)
done

lemma if_leq_not_greater:
  assumes a_le_b: "a \<le> b = 1"
  shows "a > b = 0"
apply (unfold greater_def)
apply (rule eqSubst[where a="1" and b="a \<le> b"])
apply (rule eqSym)
apply (rule a_le_b)
apply (unfold_def def_sub)
apply (rule condI2Eq)
apply (fold neq_def)
apply (auto)
apply (rule eqSubst[where a="0" and b="P S 0"])
apply (rule eqSym)
apply (auto)
apply (rule eqSubst[where a="1" and b="1 - 0"])
apply (rule eqSym)
apply (auto)
done

lemma if_less_not_geq:
  assumes a_less_b: "a < b = 1"
  shows "a \<ge> b = 0"
apply (unfold geq_def)
apply (rule eqSubst[where a="1" and b="a < b"])
apply (rule eqSym)
apply (rule a_less_b)
apply (unfold_def def_sub)
apply (rule condI2Eq)
apply (fold neq_def)
apply (auto)
apply (rule eqSubst[where a="0" and b="P S 0"])
apply (rule eqSym)
apply (auto)
apply (rule eqSubst[where a="1" and b="1 - 0"])
apply (rule eqSym)
apply (auto)
done

lemma leq_monotone [auto, simp]:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "x \<le> y + x = 1"
proof (rule ind[where a="x"])
  show "x N" by (rule x_nat)
  show "0 \<le> y + 0 = 1" by (auto, rule y_nat)
  show "\<forall>x. x \<le> y + x = 1 \<turnstile> S x \<le> y + S x = 1"
    proof (rule forallI entailsI)+
      fix xa
      assume xa_nat: "xa N" and hyp: "xa \<le> y + xa = 1"
      show "S xa \<le> y + S xa = 1"
        apply (unfold_def def_leq)
        apply (rule condI2Eq)
        apply (fold neq_def)
        apply (auto)
        apply (rule xa_nat)
        apply (auto)
        apply (rule condI2Eq)
        apply (fold neq_def)
        apply (rule eqSubst[where a="S(y + xa)" and b="y + S xa"])
        apply (unfold_def def_add)
        apply (rule eqSym)
        apply (rule condI2Eq)
        apply (fold neq_def)
        apply (auto)
        apply (rule xa_nat)
        apply (auto)
        apply (rule y_nat)
        apply (rule xa_nat)
        apply (rule eqSubst[where a="xa" and b="P S xa"])
        apply (rule eqSym)
        apply (rule predSucInv)
        apply (rule xa_nat)
        apply (fold isNat_def)
        apply (auto)
        apply (rule y_nat)
        apply (rule xa_nat)
        apply (auto)
        apply (rule y_nat)
        apply (rule xa_nat)
        apply (auto)
        apply (rule eqSubst[where a="xa" and b="P S xa"])
        apply (rule eqSym)
        apply (rule predSucInv)
        apply (rule xa_nat)
        apply (rule eqSubst[where a="S (y + xa)" and b="y + S xa"])
        apply (unfold_def def_add)
        apply (rule eqSym)
        apply (rule condI2Eq)
        apply (fold neq_def)
        apply (auto)
        apply (rule xa_nat)
        apply (auto)
        apply (rule y_nat)
        apply (rule xa_nat)
        apply (rule eqSubst[where a="xa" and b="P S xa"])
        apply (rule eqSym)
        apply (rule predSucInv)
        apply (rule xa_nat)
        apply (fold isNat_def)
        apply (auto)
        apply (rule y_nat)
        apply (rule xa_nat)
        apply (rule eqSubst[where a="y + xa" and b="P S (y + xa)"])
        apply (rule eqSym)
        apply (auto)
        apply (rule y_nat)
        apply (rule xa_nat)
        apply (rule hyp)
        done
    qed
qed

lemma add_suc_comm:
  shows "x N \<Longrightarrow> y N \<Longrightarrow> y + S(x) = S(y) + x"
apply (rule ind[where a="x"], simp+)
proof (rule forallI entailsI)+
  fix xa
  assume hyp: "y + S xa = S y + xa"
  show "x N \<Longrightarrow> y N \<Longrightarrow> xa N \<Longrightarrow> y + S S xa = S y + S xa"
    apply (rule eqSubst[where a="S(y + S(xa))" and b="y + S S xa"])
    apply (unfold_def def_add)
    apply (simp)
    apply (rule eqSubst[where a="S xa" and b="P S S xa"])
    apply (rule eqSym)
    apply (simp add: hyp)+
    apply (unfold_def def_add)
    apply (simp)
    done
qed

lemma add_comm [auto]:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "x + y = y + x"
apply (rule ind[where a="y"])
apply (rule y_nat)
apply (rule eqSubst[where a="x" and b="x + 0"])
apply (rule eqSym)
apply (auto)
apply (rule x_nat)
apply (rule eqSym)
apply (rule zero_add)
apply (rule x_nat)
proof (rule forallI entailsI)+
  fix xa
  assume xa_nat: "xa N"
  assume hyp: "x + xa = xa + x"
  show "x + S xa = S xa + x"
    apply (rule eqSym)
    apply (unfold_def def_add)
    apply (rule eqSym)
    apply (rule condI2Eq)
    apply (fold neq_def)
    apply (auto)
    apply (rule xa_nat)
    apply (auto)
    apply (rule xa_nat)
    apply (rule x_nat)
    apply (rule eqSubst[where a="xa" and b="P S xa"])
    apply (rule eqSym)
    apply (auto)
    apply (rule xa_nat)
    apply (rule eqSubst[where a="xa + x" and b="x + xa"])
    apply (rule eqSym)
    apply (rule hyp)
    apply (rule eqSubst[where a="xa + S x" and b="S xa + x"])
    apply (rule add_suc_comm)
    apply (rule x_nat)
    apply (rule xa_nat)
    apply (unfold_def def_add)
    apply (rule eqSym)
    apply (rule condI2Eq)
    apply (fold neq_def)
    apply (auto)
    apply (rule x_nat)
    apply (auto)
    apply (rule xa_nat)
    apply (rule x_nat)
    apply (rule eqSubst[where a="x" and b="P S x"])
    apply (rule eqSym)
    apply (auto)
    apply (rule x_nat)
    apply (fold isNat_def)
    apply auto
    apply (rule xa_nat)
    apply (rule x_nat)
    done
qed

lemma add_leq_monotone [cond]:
  assumes x_le_y: "x \<le> y = 1"
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes z_nat: "z N"
  shows "x \<le> y + z = 1"
apply (rule leq_trans[where y="y"])
apply (rule x_nat)
apply (rule y_nat)
apply (auto)
apply (rule y_nat)
apply (rule z_nat)
apply (rule x_le_y)
apply (rule eqSubst[where a="z + y" and b="y + z"])
apply (auto)
apply (rule z_nat)
apply (rule y_nat)
apply (rule leq_monotone)
apply (rule y_nat)
apply (rule z_nat)
done

lemma cpair_mono_r [simp]:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "x N \<Longrightarrow> y N \<Longrightarrow> y \<le> \<langle>x, y\<rangle> = 1"
unfolding cpair_def by auto

lemma neq_monotone_add:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes x_nz: "\<not> x = 0"
  shows "x N \<Longrightarrow> y N \<Longrightarrow> \<not> y = x + y"
proof -
  have H1: "x N \<Longrightarrow> y N \<Longrightarrow> (\<And>xa. xa N \<Longrightarrow> \<not> (y = S(xa) + y))"
    proof -
      fix xa
      show "x N \<Longrightarrow> y N \<Longrightarrow> xa N \<Longrightarrow> \<not> (y = S(xa) + y)"
        apply (rule ind[where a="y"], simp+)
        proof (rule forallI, rule entailsI)
          fix z
          assume hyp: "\<not> z = S xa + z"
          show "xa N \<Longrightarrow> z N \<Longrightarrow> \<not> S z = S xa + S z"
            apply (rule eqSubst[where a="S(S xa + z)" and b="S xa + S z"])
            apply (unfold_def def_add)
            apply (rule eqSym)
            apply (rule condI2Eq)
            apply (fold neq_def)
            apply (simp+)
            apply (rule neq_monotone_suc)
            apply (simp)
            apply (rule hyp)
            done
        qed
    qed
  have "\<exists>p. x = S(p)" by (auto, rule x_nat, rule x_nz)
  then show "x N \<Longrightarrow> y N \<Longrightarrow> \<not> y = x + y"
    apply (rule existsE)
    proof -
      fix a
      assume a_pred: "x = S a"
      show "a N \<Longrightarrow> x N \<Longrightarrow> y N \<Longrightarrow> \<not> y = x + y"
        apply (rule eqSubst[where a="S a" and b="x"])
        apply (rule eqSym)
        apply (rule a_pred)
        apply (rule H1)
        apply (simp)
        done
    qed
qed

lemma swap_add:
  shows "x N \<Longrightarrow> y N \<Longrightarrow> Q(y + x) \<Longrightarrow> Q (x + y)"
  by (rule eqSubst[where a="y+x" and b="x+y"], simp)

lemma nz_monotone_leq:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes H: "S(x) \<le> y = 1"
  shows "\<not> y = 0"
apply (rule grounded_contradiction[where q="S(x) = 0"])
apply (auto)
apply (rule y_nat)
apply (rule leq_0_then_0)
apply (rule natS)
apply (rule x_nat)
apply (rule eqSubst[where a="y" and b="0" and Q="\<lambda>c. S x \<le> c = 1"])
apply (rule dNegE)
apply (assumption)
apply (rule H)
apply (fold neq_def)
apply (auto)
apply (rule x_nat)
done

lemma sub_pred_suc:
  assumes H: "S(z) = x - S(y)"
  shows "x N \<Longrightarrow> y N \<Longrightarrow> z N \<Longrightarrow> x - y = S(S(z))"
proof -
  have unf: "x N \<Longrightarrow> y N \<Longrightarrow> x - S(y) = P(x - y)"
    apply (rule eqSym)
    apply (unfold_def def_sub)
    apply (simp+)
    done
  have x_neq_y: "x N \<Longrightarrow> y N \<Longrightarrow> z N \<Longrightarrow> \<not> x - y = 0"
    apply (rule nz_monotone_leq[where x="z"])
    apply (simp add: H unf)+
    done
  have H1: "x N \<Longrightarrow> y N \<Longrightarrow> P(x - y) = S(z)"
    apply (rule eqSubst[where a="x - S(y)" and b="P(x - y)"])
    apply (simp add: H unf)+
    done
  show "x N \<Longrightarrow> y N \<Longrightarrow> z N \<Longrightarrow> x - y = S(S(z))"
    apply (rule eqSubst[where b="x - y" and a="S P (x - y)"], simp)
    apply (rule x_neq_y)
    apply (simp add: H1)+
    done
qed

lemma sub_suc_pred:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes z_nat: "z N"
  assumes H: "x - y = S(z)"
  shows "x - S(y) = z"
proof -
  have "x - y = S(z) \<turnstile> x - S(y) = z"
    apply (rule ind[where a="y"])
    apply (rule y_nat)
    apply (rule entailsI)
    apply (rule eqSubst[where a="S(z)" and b="x"])
    apply (rule eqSym)
    apply (rule eqSubst[where a="x - 0" and b="x"])
    apply (auto)
    apply (rule x_nat)
    apply (assumption)
    apply (unfold_def def_sub)
    apply (rule condI2Eq)
    apply (fold neq_def)
    apply (auto)
    apply (rule z_nat)
    apply (simp)
    apply (rule eqSubst[where a="S z" and b="S z - 0"])
    apply (rule eqSym)
    apply (auto)
    apply (rule z_nat)
    apply (simp)
    apply (rule z_nat)
    proof (rule forallI entailsI)+
      fix xa
      assume hyp: "x - xa = S z \<turnstile> x - S xa = z"
      assume h: "x - S xa = S z"
      show "xa N \<Longrightarrow> x - S(S xa) = z"
        apply (unfold_def def_sub)
        apply (rule condI2Eq)
        apply (fold neq_def)
        apply (simp)
        apply (rule z_nat)
        apply (simp add: h)
        apply (rule z_nat)
        done
    qed
  then show ?thesis
    apply (rule entailsE)
    apply (rule H)
    done
qed

lemma sub_monotone_lhs:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes z_nat: "z N"
  assumes H: "S(x) - y = S(z)"
  shows "x - y = z"
proof -
  have "\<forall>z. S(x) - y = S(z) \<turnstile> x - y = z"
    apply (rule ind[where a="y"])
    apply (rule y_nat)
    apply (rule forallI)
    apply (rule entailsI)
    apply (rule eqSubst[where a="x" and b="x-0"])
    apply (rule eqSym)
    apply (auto)
    apply (rule x_nat)
    apply (rule sucInj)
    apply (rule eqSubst[where a="S x - 0" and b="S x"])
    apply (auto)
    apply (rule x_nat)
    apply (assumption)
    proof (rule forallI entailsI)+
      fix xa za
      assume hyp: "\<forall>z. S x - xa = S z \<turnstile> x - xa = z"
      assume H1: "S x - S xa = S za"
      show "xa N \<Longrightarrow> za N \<Longrightarrow> x - S xa = za"
        apply (rule sub_suc_pred)
        apply (rule x_nat)
        apply (simp)
        apply (rule entailsE[where a="S x - xa = S(S za)"])
        apply (rule forallE)
        apply (rule hyp)
        apply (auto)
        apply (rule sub_pred_suc)
        apply (rule eqSym)
        apply (rule H1)
        apply (simp)
        apply (rule x_nat)
        apply (simp)
        done
    qed
  then have "S(x) - y = S(z) \<turnstile> x - y = z"
    apply (rule forallE)
    apply (rule z_nat)
    done
  then show ?thesis
    apply (rule entailsE)
    apply (rule H)
    done
qed

lemma sub_eq_0_imp_leq:
  assumes H: "a - b = 0"
  shows "a N \<Longrightarrow> b N \<Longrightarrow> a \<le> b = 1"
proof -
  have "a N \<Longrightarrow> b N \<Longrightarrow> \<forall>a. a - b = 0 \<turnstile> a \<le> b = 1"
  proof (rule ind[where a="b"], simp)
    show "\<forall>a. a - 0 = 0 \<turnstile> a \<le> 0 = 1"
      proof (rule forallI, rule entailsI)
        fix aa
        assume aa_nat: "aa N" and hyp: "aa - 0 = 0"
        have a_zero: "aa = 0"
          apply (rule eqSubst[where a="aa-0" and b="aa"])
          apply (auto)
          apply (rule aa_nat)
          apply (rule hyp)
          done
        show "aa \<le> 0 = 1"
          apply (rule eqSubst[where a="0" and b="aa"])
          apply (rule eqSym)
          apply (rule a_zero)
          apply (auto)
          done
      qed
    show "\<forall>x. (\<forall>a. a - x = 0 \<turnstile> a \<le> x = 1) \<turnstile>
     (\<forall>a. a - S x = 0 \<turnstile> a \<le> S x = 1)"
      proof (rule forallI, rule entailsI, rule forallI, rule entailsI)
        fix xa aa
        assume hyp: "\<forall>a. a - xa = 0 \<turnstile> a \<le> xa = 1"
        assume H1: "aa - S xa = 0"
        show "xa N \<Longrightarrow> aa N \<Longrightarrow> aa \<le> S xa = 1"
          apply (rule cases_nat[where x="aa-xa"])
          apply (rule leq_trans[where y="xa"])
          apply (simp)
          apply (rule entailsE[where a="aa - xa = 0"])
          apply (rule forallE[where a="aa"])
          apply (rule hyp, simp)
          apply (rule cases_nat[where x="aa"])
          apply (simp)
          apply (rule existsE[where Q="\<lambda>c. aa = S(c)"])
          apply (simp)
          proof -
            show "aa N \<Longrightarrow> aa N" by (simp)
            show "aa N \<Longrightarrow> xa N \<Longrightarrow> aa - xa N" by (simp)
            fix a
            assume aa_sub_xa_nz: "\<not> aa - xa = 0" and aa_nz: "\<not> aa = 0" and aa_eq_sa: "aa = S a"
            show "aa N \<Longrightarrow> xa N \<Longrightarrow> a N \<Longrightarrow> aa \<le> S xa = 1"
              apply (rule eqSubst[where a="S a" and b="aa"])
              apply (rule eqSym)
              apply (rule aa_eq_sa)
              apply (rule leq_monotone_suc, simp)
              apply (rule entailsE[where a="a - xa = 0"])
              apply (rule forallE[where a="a"])
              apply (rule hyp, simp)
              apply (rule sub_monotone_lhs, simp)
              apply (rule eqSubst[where a="aa" and b="S a"])
              apply (rule aa_eq_sa)
              apply (rule eqSubst[where a="S P (aa - xa)" and b="aa - xa"], simp)
              apply (rule aa_sub_xa_nz)
              apply (rule sucCong)
              apply (rule eqSubst[where a="aa - S(xa)" and b="P(aa - xa)"])
              apply (rule eqSym)
              apply (unfold_def def_sub)
              apply (simp)
              apply (rule H1)
              done
          qed
      qed
  qed
  then have "a N \<Longrightarrow> b N \<Longrightarrow> a - b = 0 \<turnstile> a \<le> b = 1"
    apply (rule forallE, simp)
    done
  then show "a N \<Longrightarrow> b N \<Longrightarrow> a \<le> b = 1"
    apply (rule entailsE, simp)
    apply (rule H)
    done
qed

lemma less_monotone_pred:
  shows "x N \<Longrightarrow> y N \<Longrightarrow> S x < S y = 1 \<Longrightarrow> x < y = 1"
proof (rule grounded_contradiction[where q="x < y = 1"], simp)
  have H1: "x N \<Longrightarrow> y N \<Longrightarrow> S(x) < S(y) = x < y"
    apply (rule eqSym)
    apply (unfold_def def_less)
    apply (simp)
    done
  show "x N \<Longrightarrow> y N \<Longrightarrow> S x < S y = 1 \<Longrightarrow> x < y = 1"
    apply (rule eqSubst[where a="S(x) < S(y)" and b="1"])
    apply (simp)
    apply (rule eqSym)
    apply (rule H1, simp)
    done
qed

lemma less_trans:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes z_nat: "z N"
  assumes x_le_y: "x < y = 1"
  assumes y_le_z: "y < z = 1"
  shows "x < z = 1"
proof -
  have quantized: "\<forall>x y. (x < y = 1) \<turnstile> (y < z = 1) \<turnstile> (x < z = 1)"
    proof (rule ind[where a="z"])
    show "z N" by (rule z_nat)
    show "\<forall>x y. x < y = 1 \<turnstile>
      y < 0 = 1 \<turnstile> x < 0 = 1"
      proof (rule forallI, rule forallI, rule entailsI, rule entailsI)
        fix xa ya
        assume xa_nat: "xa N"
        assume ya_nat: "ya N"
        assume H: "ya < 0 = 1"
        assume H1: "xa < ya = 1"
        show "xa < 0 = 1"
          apply (rule exF[where P="ya < 0 = 1"])
          apply (rule H)
          apply (simp)
          done
      qed
    show "\<forall>x. (\<forall>xa y. xa < y = 1 \<turnstile> y < x = 1 \<turnstile> xa < x = 1) \<turnstile>
      (\<forall>xa y. xa < y = 1 \<turnstile> y < S x = 1 \<turnstile> xa < S x = 1)"
      proof (rule forallI, rule entailsI)+
        fix x
        show "x N \<Longrightarrow> \<forall>xa y. xa < y = 1 \<turnstile> y < x = 1 \<turnstile> xa < x = 1 \<Longrightarrow>
              \<forall>xa y. xa < y = 1 \<turnstile> y < S x = 1 \<turnstile> xa < S x = 1"
          proof -
            assume hyp: "\<forall>xa y. xa < y = 1 \<turnstile> y < x = 1 \<turnstile> xa < x = 1"
            show "x N \<Longrightarrow> \<forall>xa y. xa < y = 1 \<turnstile> y < S x = 1 \<turnstile> xa < S x = 1"
              proof (rule forallI entailsI)+
                fix xa ya
                assume xa_le_ya: "xa < ya = 1"
                assume ya_le_sx: "ya < S x = 1"
                show "x N \<Longrightarrow> xa N \<Longrightarrow> ya N \<Longrightarrow> xa < S x = 1"
                  apply (rule cases_nat[where x="xa"])
                  apply (simp)
                  apply (unfold_def def_less)
                  apply (simp)
                  proof -
                    assume xa_nz: "\<not> xa = 0"
                    have ya_nz: "ya N \<Longrightarrow> \<not> ya = 0"
                      apply (rule grounded_contradiction[where q="xa < ya = 1"])
                      apply (simp)
                      apply (rule xa_le_ya)
                      apply (rule eqSubst[where a="0" and b="xa < ya"])
                      apply (rule eqSym)
                      apply (rule eqSubst[where a="0" and b="ya"])
                      apply (rule eqSym)
                      apply (rule dNegE)
                      apply (auto)
                      done
                    have H: "x N \<Longrightarrow> ya N \<Longrightarrow> P(ya) < P(S x) = 1"
                      apply (rule less_monotone_pred)
                      apply (rule natP, assumption)
                      apply (subst predSucInv, assumption+)
                      apply (rule eqSubst[where a="ya" and b="S P ya"])
                      apply (rule eqSym)
                      apply (simp)
                      apply (rule ya_nz, simp+)
                      apply (rule ya_le_sx)
                      done
                    have H2: "x N \<Longrightarrow> ya N \<Longrightarrow> P(ya) < x = 1"
                      apply (rule eqSubst[where a="P S x" and b="x"])
                      apply (auto)
                      apply (rule H, simp)
                      done
                    have H3: "xa N \<Longrightarrow> ya N \<Longrightarrow> P(xa) < P(ya) = 1"
                      apply (rule less_monotone_pred)
                      apply (rule natP, assumption)+
                      apply (rule eqSubst[where a="xa" and b="S P xa"])
                      apply (rule eqSym)
                      apply (auto)
                      apply (rule xa_nz)
                      apply (rule eqSubst[where a="ya" and b="S P ya"])
                      apply (rule eqSym, simp)
                      apply (rule ya_nz, simp)
                      apply (rule xa_le_ya)
                      done
                    have H4: "xa N \<Longrightarrow> ya N \<Longrightarrow> P xa < P ya = 1 \<turnstile> P ya < x = 1 \<turnstile> P xa < x = 1"
                      apply (rule forallE[where a="P ya"])
                      apply (rule forallE[where a="P xa"])
                      apply (rule hyp)
                      apply (auto)
                      done
                    then have H5: "xa N \<Longrightarrow> ya N \<Longrightarrow> P ya < x = 1 \<turnstile> P xa < x = 1"
                      apply (rule entailsE, simp)
                      apply (rule H3, simp)
                      done
                    then show "xa N \<Longrightarrow> ya N \<Longrightarrow> x N \<Longrightarrow> P xa < x = 1"
                      apply (rule entailsE, simp)
                      apply (rule H2, simp)
                      done
                  qed
            qed
          qed
      qed
    qed
    then have "\<forall>y. (x < y = 1) \<turnstile> (y < z = 1) \<turnstile> (x < z = 1)"
      apply (rule forallE)
      apply (rule x_nat)
      done
    then have "(x < y = 1) \<turnstile> (y < z = 1) \<turnstile> (x < z = 1)"
      apply (rule forallE)
      apply (rule y_nat)
      done
    then have "(y < z = 1) \<turnstile> (x < z = 1)"
      apply (rule entailsE)
      apply (rule x_le_y)
      done
    then show ?thesis
      apply (rule entailsE)
      apply (rule y_le_z)
      done
qed

lemma sub_less:
  shows "x N \<Longrightarrow> y N \<Longrightarrow> S(x) - S(y) < S(x) = 1"
apply (rule ind[where a="y"])
apply (simp)
apply (rule eqSubst[where a="P(S(x) - 0)" and b="S(x) - 1"])
apply (unfold_def def_sub)
apply (simp+)
proof (rule forallI entailsI)+
  fix xa
  assume hyp: "S x - S xa < S x = 1"
  show "x N \<Longrightarrow> xa N \<Longrightarrow> S x - S S xa < S x = 1"
    apply (rule eqSubst[where b="S x - S S xa" and a="P(S(x) - S(xa))"])
    apply (unfold_def def_sub, simp+)
    apply (rule cases_nat[where x="S(x) - S(xa)"], simp+)
    apply (rule less_monotone_pred)
    apply (rule natP, rule sub_terminates)
    apply (rule natS, assumption)+
    apply (rule eqSubst[where a="S x - S xa" and b="S P (S x - S xa)"], simp)
    apply (rule less_trans[where y="S x"], simp)
    apply (rule hyp, simp)
    done
qed

lemma less_not_refl [simp]:
  shows "x N \<Longrightarrow> x < x = 0"
apply (rule ind[where a="x"], simp, rule forallI, rule entailsI)
apply (unfold_def def_less)
apply (simp)
done

lemma "a N \<Longrightarrow> P(a - b) = P(a) - b"
sorry

lemma [simp]: "a N \<Longrightarrow> a - a = 0"
apply (unfold_def def_sub)
sorry

lemma div_x_x_1 [auto]:
  shows "x N \<Longrightarrow> div (S x) (S x) = 1"
proof (rule ind[where a="x"], auto, rule forallI, rule entailsI)
  fix xa
  assume hyp: "div (S xa) (S xa) = 1"
  show "xa N \<Longrightarrow> div (S S xa) (S S xa) = 1"
    by (unfold_def def_div, simp)
qed

lemma cpair_1_0_1 [simp, auto]: "\<langle>1, 0\<rangle> = 1"
  unfolding cpair_def by (simp)

lemma sub_eq_self_imp_zero:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes H: "S(y) - x = S(y)"
  shows "x = 0"
proof (rule grounded_contradiction[where q="S(y) < S(y) = 1"])
  show "x = 0 B" by (auto, rule x_nat)
  assume x_nz: "\<not> x = 0"
  have H1: "S(y) - x < S(y) = 1"
    apply (rule existsE[where Q="\<lambda>c. x = S(c)"])
    apply (auto)
    apply (rule x_nat)
    apply (rule x_nz)
    proof -
      fix a
      assume a_nat: "a N" and x_p: "x = S a"
      show "S y - x < S y = 1 "
        apply (rule eqSubst[where a="S a" and b="x"])
        apply (rule eqSym)
        apply (rule x_p)
        apply (rule sub_less)
        apply (rule y_nat)
        apply (rule a_nat)
        done
    qed
  show "S(y) < S(y) = 1"
    apply (rule eqSubst[where a="S(y) - x" and b="S(y)" and Q="\<lambda>c. c < S(y) = 1"])
    apply (rule H)
    apply (rule H1)
    done
  show "\<not> S(y) < S(y) = 1"
    apply (rule eqSubst[where a="0" and b= "S y < S y"])
    apply (rule eqSym)
    apply (rule less_not_refl)
    apply (rule natS)
    apply (rule y_nat)
    apply (fold neq_def)
    apply (auto)
    done
qed

lemma div_nz:
  assumes x_geq_y: "x \<ge> S(y) = 1"
  shows "x N \<Longrightarrow> y N \<Longrightarrow> \<not> div x S(y) = 0"
apply (rule eqSubst[where a="S(div (x - S y) S(y))" and b="div x S(y)"])
apply (unfold_def def_div)
apply (rule eqSym)
apply (rule condI2)
apply (rule eqSubst[where a="0" and b="x < S y"])
apply (rule eqSym)
apply (rule sub_eq_self_imp_zero[where y="0"])
apply (simp)
apply (fold geq_def)
apply (rule x_geq_y)
apply (simp)
done

lemma
  assumes a_nz: "\<not> a = 0"
  shows "a * b \<ge> b = 1"
sorry

lemma cpair_strict_mono_l [auto]:
  assumes y_nz: "\<not> x = 0"
  assumes y_neq_1: "\<not> x = 1"
  shows "x N \<Longrightarrow> y N \<Longrightarrow> x < \<langle>x, y\<rangle> = 1"
sorry
lemma cpair_strict_mono_r [auto]:
  assumes y_nz: "\<not> y = 0"
  shows "x N \<Longrightarrow> y N \<Longrightarrow> y < \<langle>x, y\<rangle> = 1"
apply (rule less_is_leq_neq)
apply (simp+)
apply (unfold cpair_def)
apply (rule swap_add)
apply (simp)
apply (rule neq_monotone_add)
apply (simp)
sorry

lemma [auto]:
  assumes p_bool: "p B"
  assumes q_bool: "q B"
  shows "p \<or> q B"
apply (unfold bJudg_def)
apply (rule cases_bool[where p="p"])
apply (rule p_bool)
apply (rule disjI1)
apply (rule disjI1)
apply (assumption)
apply (rule cases_bool[where p="q"])
apply (rule q_bool)
apply (rule disjI1)
apply (rule disjI2)
apply (assumption)
apply (rule disjI2)
apply (auto)
done

lemma [auto]:
  assumes p_bool: "p B"
  assumes q_bool: "q B"
  shows "p \<and> q B"
apply (unfold conj_def)
apply (auto)
apply (rule p_bool)
apply (rule q_bool)
done

lemma notE_impl:
  shows "\<not> a \<Longrightarrow> a \<longrightarrow> b"
apply (unfold impl_def)
apply (rule disjI1)
apply (assumption)
done

lemma [auto]:
  "a N \<Longrightarrow> b N \<Longrightarrow> \<not> (a = b) \<Longrightarrow> \<not> (S a = S b)"
apply (rule grounded_contradiction[where q="a = b"], simp)
apply (rule sucInj)
apply (rule dNegE, simp)
done

lemma [cond]:
  "\<not>a \<Longrightarrow> b \<Longrightarrow> a \<or> b"
by (rule disjI2, simp)

lemma [cond]:
  "\<not>b \<Longrightarrow> a \<Longrightarrow> a \<or> b"
by (rule disjI1, simp)

lemma [auto]: "y N \<Longrightarrow> x = 0 \<Longrightarrow> y - x = y"
by (simp)

lemma [auto]: "a N \<Longrightarrow> b N \<Longrightarrow> a \<le> b = 0 \<Longrightarrow> S a \<le> S b = 0"
by (unfold_def def_leq, simp)

lemma gr_mono_suc [auto]: "a N \<Longrightarrow> b N \<Longrightarrow> a > b = 1 \<Longrightarrow> S a > S b = 1"
unfolding greater_def
apply (simp)
apply (rule sub_eq_self_imp_zero[where y="0"])
apply (simp)
done

lemma [auto]: "a N \<Longrightarrow> S a > 0 = 1"
unfolding greater_def
by (simp)

lemma [cond]: "a < b = 1 \<Longrightarrow> a N \<Longrightarrow> b N \<Longrightarrow> \<not> a = b"
apply (rule grounded_contradiction[where q="a < a = 1"], simp)
apply (rule eqSubst[where a="a < b" and b="a < a"])
apply (rule eqSubst[where a="a" and b="b"])
apply (rule dNegE, assumption)
apply (rule eqSubst[where a="0" and b="a < a"])
apply (rule eqSym, simp)
apply (rule eqSubst[where a="0" and b="a < a"])
apply (rule eqSym, simp)
done

lemma le_less_trans: "a N \<Longrightarrow> b N \<Longrightarrow> c N \<Longrightarrow> a \<le> b = 1 \<Longrightarrow> b < c = 1 \<Longrightarrow> a < c = 1"
apply (rule cases_bool[where p="a = b"], simp)
apply (rule eqSubst[where a="b" and b="a"])
apply (rule eqSym, assumption+)
apply (rule less_trans[where y="b"], simp)
apply (rule less_is_leq_neq, simp)
done

lemma [cond]: " a \<le> b = 1 \<Longrightarrow> a N \<Longrightarrow> b N \<Longrightarrow> c N \<Longrightarrow> \<not> b = 0 \<Longrightarrow> \<not> b = 1 \<Longrightarrow> a < \<langle>b,c\<rangle> = 1"
  by (rule le_less_trans[where b="b"], simp)

lemma [cond]: "a \<le> c = 1 \<Longrightarrow> a N \<Longrightarrow> b N \<Longrightarrow> c N \<Longrightarrow> \<not> c = 0 \<Longrightarrow> a < \<langle>b,c\<rangle> = 1"
  by (rule le_less_trans[where b="c"], simp)

lemma neg_conjI1: "\<not>a \<Longrightarrow> \<not>(a \<and> b)"
  unfolding conj_def by (rule dNegI, rule disjI1, simp)

lemma neg_conjI2: "\<not>b \<Longrightarrow> \<not>(a \<and> b)"
  unfolding conj_def by (rule dNegI, rule disjI2, simp)

ML_file "gd_typeencode.ML"

text "A manual construction of an inductive datatype.
  Later, we want this to be generated automatically from something
  like \<open>declaretype List = Nil | Cons of \<open>nat\<close> \<open>List\<close>\<close>."

(* What the declaretype compiler should compile: *)
type_synonym List = num

definition list_type_tag where
  "list_type_tag \<equiv> 0"

definition Nil :: "List" where
  "Nil \<equiv> \<langle>list_type_tag,1\<rangle>"

definition Cons :: "num \<Rightarrow> List \<Rightarrow> List" where
  "Cons n xs \<equiv> \<langle>list_type_tag,2,n,xs\<rangle>"

consts
  is_list :: "num \<Rightarrow> o"

axiomatization
where
  is_list_def: "is_list x := if x = Nil
                               then True
                             else if ((x = Cons n xs) \<and> (is_list xs) \<and> (n N))
                               then True
                             else False"

lemma nil_nat [auto]: "Nil N"
unfolding Nil_def list_type_tag_def by simp

lemma cons_nat [auto]: "n N \<Longrightarrow> xs N \<Longrightarrow> Cons n xs N"
unfolding Cons_def list_type_tag_def by simp

lemma [auto]: "is_list Nil"
by (unfold_def is_list_def, auto)

lemma [auto]: "n N \<Longrightarrow> xs N \<Longrightarrow> \<not> Nil = Cons n xs"
unfolding Nil_def Cons_def list_type_tag_def
by simp

lemma [auto]: "n N \<Longrightarrow> xs N \<Longrightarrow> \<not> Cons n xs = Nil"
by (fold neq_def, rule neq_sym, simp+)

lemma "is_list x \<Longrightarrow> (x = Nil) \<or> (\<exists>n xs. x = Cons n xs)"
sorry

lemma list_nat [cond]:
  shows "is_list x \<Longrightarrow> x N"
apply (unfold_def is_list_def)
sorry

lemma cons_is_list [auto]:
  shows "n N \<Longrightarrow> is_list xs \<Longrightarrow> is_list (Cons n xs)"
by (unfold_def is_list_def, auto)

ML_file "gd_induct.ML"

lemma is_list_terminates [auto]: "x N \<Longrightarrow> is_list x B"
apply (induct strong x)
apply (unfold_def is_list_def)
apply (unfold Nil_def)
apply (unfold list_type_tag_def)
apply (rule condTB)
apply (simp)
apply (rule condTB)
apply (simp)
sorry

lemma is_list_cases [consumes 1, case_names Nil Cons]:
  assumes "is_list x"
  obtains (Nil) "x = Nil" | (Cons) n xs where "x = Cons n xs"
    sorry

lemma is_list_cases2 [consumes 1, case_names Nil Cons, elim!]:
  assumes main_premise: "is_list x"
  and nil_branch:   "x = Nil \<Longrightarrow> Q"
  and cons_branch:  "\<And>n xs. x = Cons n xs \<Longrightarrow> Q"
  shows "Q"
    sorry

thm is_list_cases

lemma "Cons n xs = Cons m ys \<Longrightarrow> n = m \<and> xs = ys"
sorry

lemma "xs N \<Longrightarrow> n N \<Longrightarrow> xs < Cons n xs = 1"
unfolding Cons_def list_type_tag_def
apply (rule less_trans[where y="\<langle>1, n, xs\<rangle>"])
apply (auto)
sorry

lemma [auto]: "\<not> 0 = Nil"
sorry

lemma list_induction:
  assumes a_list: "is_list a"
  assumes q_nil: "Q Nil"
  assumes step: "\<forall>x xs. x N \<turnstile> is_list xs \<turnstile> Q xs \<turnstile> Q (Cons x xs)"
  shows "Q a"
proof -
  have "is_list a \<longrightarrow> Q a"
    proof (rule strong_induction[where a="a"])
      show "a N" by (rule list_nat, rule a_list)
      show "is_list 0 \<longrightarrow> Q 0"
        apply (rule notE_impl)
        apply (unfold_def is_list_def)
        sorry
      show "\<forall>x. (\<forall>y. y \<le> x = 1 \<turnstile> is_list y \<longrightarrow> Q y) \<turnstile> is_list S x \<longrightarrow> Q S x"
        proof (rule forallI, rule entailsI)+
          fix x
          assume hyp: "\<forall>y. y\<le>x = 1 \<turnstile> is_list y \<longrightarrow> Q y"
          show "x N \<Longrightarrow> is_list S x \<longrightarrow> Q (S x)"
            apply (rule implI)
            apply (rule cases_bool [where p="is_list S x"])
            apply (simp)
            sorry
        qed
    qed
  then show ?thesis
    apply (rule implE)
    apply (rule a_list)
    done
qed

(*
 fun sum :: "List \<Rightarrow> num" where
   sum_nil: "sum Nil = 0" and
   sum_cons: "sum (Cons n xs) = n + sum xs"
 *)

axiomatization
  sum :: "List \<Rightarrow> num"
where
  sum_def: "sum x := if x = Nil then 0
                     else if (x = (Cons n xs) \<and> is_list xs \<and> (n N)) then n + (sum xs)
                     else omega"

lemma [auto]:
  assumes h: "is_list x"
  shows "sum x N"
sorry

(*
lemma [auto]:
  assumes h: "is_list x"
  shows "sum x N"
using h
proof (elim is_list_cases)
  case Nil
sorry
*)

lemma [simp]: "sum Nil = 0"
apply (unfold_def sum_def)
apply (auto)
done

lemma [simp]: "n N \<Longrightarrow> is_list xs \<Longrightarrow> sum (Cons n xs) = n + sum xs"
apply (rule eqSym)
apply (unfold_def sum_def)
apply (rule eqSym)
apply (auto)
done

lemma "sum (Cons 4 (Cons 3 (Nil))) = 7"
apply (simp)
apply (unfold_def def_add)
apply (unfold_def def_add)
apply (simp)
done

lemma "is_list (Cons 4 (Cons 3 (Nil)))"
by simp

(*
declaretype num =
  Zero
  | Suc of "num"

declaretype list =
  nil
  | cons of "num" "list"
*)

end (* End of theory *)
