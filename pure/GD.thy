theory GD
imports Pure
keywords
  "declaretype" :: diag
begin

text \<open>The following theory development formalizes the Grounded Deduction Logic.\<close>

named_theorems gd_simp "GD simplification rules"

 section \<open>Axiomatization of truth in GD\<close>

typedecl o

judgment
  Trueprop :: \<open>o \<Rightarrow> prop\<close>  (\<open>_\<close> 5)

axiomatization
  eq :: \<open>['a, 'a] \<Rightarrow> o\<close>  (infixl \<open>=\<close> 45)
where
  eqRefl: \<open>a = a\<close> and
  eqSubst: \<open>\<lbrakk>a = b; Q a\<rbrakk> \<Longrightarrow> Q b\<close> and
  eqSym: \<open>a = b \<Longrightarrow> b = a\<close>

lemma eq_trans: "a = b \<Longrightarrow> b = c \<Longrightarrow> a = c"
apply (rule eqSubst[where a="b" and b="c"])
apply (assumption)
apply (assumption)
done

axiomatization
  disj :: \<open>[o, o] \<Rightarrow> o\<close>  (infixr \<open>\<or>\<close> 30) and
  not :: \<open>o \<Rightarrow> o\<close> (\<open>\<not> _\<close> [40] 40)
where
  disjI1: \<open>P \<Longrightarrow> P \<or> Q\<close> and
  disjI2: \<open>Q \<Longrightarrow> P \<or> Q\<close> and
  disjI3: \<open>\<lbrakk>\<not>P; \<not>Q\<rbrakk> \<Longrightarrow> \<not>(P \<or> Q)\<close> and
  disjE1: \<open>\<lbrakk>P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R\<close> and
  disjE2: \<open>\<not>(P \<or> Q) \<Longrightarrow> \<not>P\<close> and
  disjE3: \<open>\<not>(P \<or> Q) \<Longrightarrow> \<not>Q\<close> and

  dNegEq: \<open>P = (\<not>\<not>P)\<close> and
  exF: \<open>\<lbrakk>P; \<not>P\<rbrakk> \<Longrightarrow> Q\<close>

definition neq (infixl \<open>\<noteq>\<close> 45)
  where \<open>a \<noteq> b \<equiv> \<not> (a = b)\<close>
definition bJudg (\<open>_ B\<close> 30)
  where \<open>(p B) \<equiv> (p \<or> \<not>p)\<close>
definition conj (infixl \<open>\<and>\<close> 35)
  where \<open>p \<and> q \<equiv> \<not>(\<not>p \<or> \<not>q)\<close>
definition impl (infixl \<open>\<longrightarrow>\<close> 25)
  where \<open>p \<longrightarrow> q \<equiv> \<not>p \<or> q\<close>

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

lemma implI:
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

section \<open>Axiomatization of naturals in GD\<close>

typedecl nat

axiomatization
  zero :: \<open>nat\<close>          (\<open>0\<close>) and
  suc :: \<open>nat \<Rightarrow> nat\<close>     (\<open>S(_)\<close> [800]) and
  pred :: \<open>nat \<Rightarrow> nat\<close>    (\<open>P(_)\<close> [800]) and
  isNat :: \<open>nat \<Rightarrow> o\<close>     (\<open>_ N\<close> [31] 30)
where
  sucEq: \<open>(S a = S b) = (a = b)\<close> and
  nat0: \<open>0 N\<close> and
  natS: \<open>n N \<Longrightarrow> S n N\<close> and
  natP: \<open>n N \<Longrightarrow> P n N\<close> and
  eqBool: \<open>\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow> (a = b) B\<close> and
  sucNonZero: \<open>a N \<Longrightarrow> S a \<noteq> 0\<close> and
  predSucSym: \<open>a N \<Longrightarrow> P(S(a)) = a\<close> and
  pred0: \<open>P(0) = 0\<close>

lemma sucInj:
  assumes H: "S a = S b"
  shows "a = b"
apply (rule eqSubst[where a="S a = S b"])
apply (rule sucEq)
apply (rule H)
done

lemma sucCong:
  assumes H: "a = b"
  shows "S a = S b"
apply (rule eqSubst[where a="a=b"])
apply (rule eqSym)
apply (rule sucEq)
apply (rule H)
done

syntax
  "_gd_num" :: "num_token \<Rightarrow> nat"    ("_")

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
  forall :: "(nat \<Rightarrow> o) \<Rightarrow> o"  (binder "\<forall>" [8] 9) and
  exists :: "(nat \<Rightarrow> o) \<Rightarrow> o"  (binder "\<exists>" [8] 9)
where
  forallI: "\<lbrakk>\<And>x. (x N \<Longrightarrow> Q x)\<rbrakk> \<Longrightarrow> \<forall>x. Q x" and
  forallE: "\<lbrakk>\<forall>x. Q x; a N\<rbrakk> \<Longrightarrow> Q a" and
  existsI: "\<lbrakk>a N; Q a\<rbrakk> \<Longrightarrow> \<exists>x. Q x" and
  existsE: "\<lbrakk>\<exists>x. Q x; \<And>a. a N \<Longrightarrow> Q a \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" and
  forAllNeg: "\<lbrakk>\<not>(\<forall>x. Q x); (Q x) B\<rbrakk> \<Longrightarrow> \<exists>x. \<not>(Q x)" and
  existsNeg: "\<lbrakk>\<not>(\<exists>x. Q x); (Q x) B\<rbrakk> \<Longrightarrow> \<forall>x. \<not>(Q x)" and
  ind: \<open>\<lbrakk>a N; Q 0; \<forall>x.(Q x \<turnstile> Q S(x))\<rbrakk> \<Longrightarrow> Q a\<close>

section \<open>Axiomatization of conditional evaluation in GD\<close>

consts
  cond :: \<open>o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
syntax
  "_cond" :: \<open>o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (\<open>_ ? _ : _\<close> [55, 54, 54] 54)
translations
  "c ? a : b" \<rightleftharpoons> "CONST cond c a b"

axiomatization
where
  condI1: \<open>\<lbrakk>c; a N\<rbrakk> \<Longrightarrow> c ? a : b = a\<close> and
  condI2: \<open>\<lbrakk>\<not>c; b N\<rbrakk> \<Longrightarrow> c ? a : b = b\<close> and
  condT: \<open>\<lbrakk>c B; c \<Longrightarrow> a N; \<not>c \<Longrightarrow> b N\<rbrakk> \<Longrightarrow> (c ? a : b) N\<close>

lemma condI1Eq:
  assumes c_holds: "c"
  assumes d_nat: "d N"
  assumes a_eq_d: "a = d"
  shows "(c ? a : b) = d"
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
  shows "(c ? a : b) = d"
apply (rule eqSubst[where a="d" and b="b"])
apply (rule eqSym)
apply (rule a_eq_d)
apply (rule condI2)
apply (rule not_c)
apply (rule d_nat)
done

lemma condI3:
  assumes c_bool: "c B"
  assumes a_nat: "a N"
  shows "(c ? a : a) = a"
apply (rule disjE1[where P="c" and Q="\<not>c"])
apply (fold GD.bJudg_def)
apply (rule c_bool)
apply (rule condI1)
apply (assumption)
apply (rule a_nat)
apply (rule condI2)
apply (assumption)
apply (rule a_nat)
done

ML_file "gd_auto.ML"

section \<open>Definitional Mechanism in GD\<close>

axiomatization
  def :: \<open>'a \<Rightarrow> 'a \<Rightarrow> o\<close> (infix \<open>:=\<close> 40)
where
  defE: \<open>\<lbrakk>a := b; Q b\<rbrakk> \<Longrightarrow> Q a\<close>

(*
axiomatization
  safe_def :: \<open>(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> o\<close>
where
  safedefE: \<open>\<lbrakk>safedef a b; Q b\<rbrakk> \<Longrightarrow> Q a\<close> and
  (* Sadly unprovable, so definitions must be axiomatized. *)
  safedefI: \<open>\<lbrakk>(safedef a b) \<Longrightarrow> (\<And>c. a := c \<Longrightarrow> b = c)\<rbrakk> \<Longrightarrow> a := b\<close>
 *)

lemmas [gd_simp] = condI3 condI1 condI2 condT nat0 natS natP sucNonZero predSucSym pred0 neq_def eqRefl dNegEq eqBool sucCong
ML_file \<open>unfold_def.ML\<close>

section \<open>Deductions of non-elementary inference rules.\<close>

lemma true [gd_simp]: "True"
apply (unfold GD.True_def)
apply (rule eqRefl)
done

lemma true_bool [gd_simp]: "True B"
apply (unfold GD.bJudg_def)
apply (rule disjI1)
apply (rule true)
done

lemma not_false [gd_simp]: "\<not>False"
proof (unfold False_def)
  show "\<not>(S(0) = 0)"
  proof -
    have "S(0) \<noteq> 0" by (rule sucNonZero) (rule nat0)
    then show ?thesis by (unfold neq_def)
  qed
qed

lemma false_bool [gd_simp]: "False B"
proof (unfold GD.bJudg_def)
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

lemma not_bool [gd_simp]:
  assumes a_bool: "a B"
  shows "(\<not>a) B"
apply (unfold GD.bJudg_def)
apply (rule eqSubst[where a="a" and b="\<not>\<not>a"])
apply (rule dNegEq)
apply (rule disj_comm)
apply (fold GD.bJudg_def)
apply (rule a_bool)
done

lemma dNegI: "a \<Longrightarrow> \<not>\<not>a"
proof -
  assume a: "a"
  show "\<not>\<not>a"
  apply (rule eqSubst[where a="a"])
  apply (rule dNegEq)
  apply (rule a)
  done
qed

lemma dNegE: "\<not>\<not>a \<Longrightarrow> a"
proof -
  assume d_neg_a: "\<not>\<not>a"
  show "a"
  apply (rule eqSubst[where a="\<not>\<not>a"])
  apply (rule eqSym)
  apply (rule dNegEq)
  apply (rule d_neg_a)
  done
qed

lemma neq_com:
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  assumes ab_neq: "a \<noteq> b"
  shows "b \<noteq> a"
proof (unfold neq_def, rule grounded_contradiction[where q="a=b"])
  show "(\<not>(b=a)) B"
    apply (gd_auto)
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

lemma neq_bool [gd_simp]:
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  shows "(a \<noteq> b) B"
apply (unfold neq_def)
apply (gd_auto)
apply (rule a_nat)
apply (rule b_nat)
done

lemma sucNotEqual [gd_simp]:
  assumes a_nat: "a N"
  shows "a \<noteq> S(a)"
proof (rule ind[where a="a"])
  show "a N" by (rule a_nat)
  show "0 \<noteq> S(0)"
    apply (rule neq_com)
    apply (gd_auto)
    done
  show "\<forall>x. (x\<noteq>S(x)) \<turnstile> (S(x) \<noteq> S(S(x)))"
    proof (rule forallI, rule entailsI)
      fix x
      assume x_nat: "x N"
      assume x_neq_s: "x \<noteq> S(x)"
      show "S(x) \<noteq> S(S(x))"
      proof (rule grounded_contradiction[where q="False"])
        show "(S(x) \<noteq> S(S(x))) B"
          apply (rule neq_bool)
          apply (rule natS)
          apply (rule x_nat)
          apply (gd_auto)
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
          apply (gd_auto)
          done
      qed
    qed
qed

theorem GD_consistent: "\<And>Q. \<not>(Q \<and> \<not>Q)"
(* This is the meta-level consistency theorem. The object-level universal
 * quantifier can only quantify over naturals, not propositions.
 * I don't think we can hope to prove this. We should state an object-level
 * one that quantifies over the nats and uses nat encodings of GD propositions.
 *)
sorry

section \<open>Definitions of basic arithmetic functions\<close>

(* Use the recursion mechanism to define the standard arithmetic functions to
 * be available in a global context.
 * Axiomatizing them simply means that the fact that they are defined with the
 * given definitions are axioms.
 * User-defined functions should be in locales,
 * not in axiomatization blocks.
 *)

axiomatization
  add  :: "nat \<Rightarrow> nat \<Rightarrow> nat"  (infixl "+" 60) and
  sub  :: "nat \<Rightarrow> nat \<Rightarrow> nat"  (infixl "-" 60) and
  mult :: "nat \<Rightarrow> nat \<Rightarrow> nat"  (infixl "*" 70) and
  div  :: "nat \<Rightarrow> nat \<Rightarrow> nat"                  and
  less :: "nat \<Rightarrow> nat \<Rightarrow> nat"  (infix "<" 50)  and
  leq  :: "nat \<Rightarrow> nat \<Rightarrow> nat"  (infix "\<le>" 50)
where
  def_add: "add := (\<lambda>x y. (y = 0) ? x : S(x + P(y)))" and
  def_sub: "sub := (\<lambda>x y. (y = 0) ? x : P(x - P(y)))" and
  def_mult: "mult := (\<lambda>x y. (y = 0) ? 0 : (x + x * P(y)))" and
  def_leq: "leq := (\<lambda>x y. (x = 0) ? 1 : ((y = 0) ? 0 : (P(x) \<le> P(y))))" and
  def_less: "less := (\<lambda>x y. (y = 0) ? 0 : ((x = 0) ? 1 : (P(x) < P(y))))" and
  def_div: "div := (\<lambda>x y. (x < y = 1) ? 0 : S(div (x - y) y))"

definition greater :: "nat \<Rightarrow> nat \<Rightarrow> nat" (infix ">" 50) where
  "greater x y \<equiv> 1 - (x \<le> y)"

definition greater_eq :: "nat \<Rightarrow> nat \<Rightarrow> nat" (infix "\<ge>" 50) where
  "greater_eq x y \<equiv> 1 - (x < y)"

(* Returns y if S(y) > sqrt(x), else returns the greatest y s.t. y*y\<le>x. *)
axiomatization
  sqrt_h :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  def_sqrt_h: "sqrt_h := (\<lambda>x y. (S(y) * S(y) > x = 1) ? y : (sqrt_h x S(y)))"

definition floor_sqrt :: "nat \<Rightarrow> nat" where
  "floor_sqrt x \<equiv> sqrt_h x 0"

definition cpair :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "cpair x y \<equiv> div (x+y * S(x+y)) (2+y)"

nonterminal cpair_args

syntax
  "_cpair"      :: "nat \<Rightarrow> cpair_args \<Rightarrow> nat"        ("\<langle>_,_\<rangle>")
  "_cpair_arg"  :: "nat \<Rightarrow> cpair_args"               ("_")
  "_cpair_args" :: "nat \<Rightarrow> cpair_args \<Rightarrow> cpair_args" ("_,_")
translations
  "\<langle>x, y\<rangle>" == "CONST cpair x y"
  "_cpair x (_cpair_args y z)" == "_cpair x (_cpair_arg (_cpair y z))"

(* recover w=x+y from the pair z *)
definition cpzw :: "nat \<Rightarrow> nat" where
  "cpzw z \<equiv> div (floor_sqrt (8 * z + 1) - 1) 2"

(* recover t from w *)
definition cpwt :: "nat \<Rightarrow> nat" where
  "cpwt w \<equiv> div (w * S(w)) 2"

(* recover y from a pair z *)
definition cpy :: "nat \<Rightarrow> nat" where
  "cpy z \<equiv> z - (cpwt (cpzw z))"

(* recover x from a pair z *)
definition cpx :: "nat \<Rightarrow> nat" where
  "cpx z \<equiv> cpzw z - cpy z"

lemma less_0_false [gd_simp]: "(x < 0) = 0"
apply (unfold_def def_less)
apply (gd_auto)
done

lemma add_terminates [gd_simp]:
  assumes x_nat: \<open>x N\<close>
  assumes y_nat: \<open>y N\<close>
  shows       \<open>add x y N\<close>
proof (rule ind[where a=y])
  show habeas_quid_cond: "y N" by (rule y_nat)
  show base_case: "add x 0 N"
    proof (unfold_def def_add)
      show "(0 = 0) ? x : S(add x P(0)) N"
        apply (rule eqSubst[where a="x"])
        apply (rule eqSym)
        apply (rule condI1)
        apply (rule eqRefl)
        apply (rule x_nat)
        apply (rule x_nat)
        done
    qed
  show ind_step: "\<forall>a. ((x + a) N) \<turnstile> ((x + S(a)) N)"
    proof (rule forallI, rule entailsI, unfold_def def_add)
      fix a
      assume HQ: "a N" and BC: "add x a N"
      show "(S(a) = 0) ? x : S(add x P(S(a))) N"
        proof (rule GD.condT)
          show "S(a) = 0 B"
            apply (rule GD.eqBool)
            apply (rule GD.natS)
            apply (rule HQ)
            apply (rule GD.nat0)
            done
          show "x N" by (rule x_nat)
          show "S(add x P(S(a))) N"
            apply (rule GD.natS)
            apply (rule eqSubst[where a="x+a"])
            apply (rule eqSubst[where a="a" and b="P(S(a))"])
            apply (rule eqSym)
            apply (rule predSucSym)
            apply (rule HQ)
            apply (rule eqRefl)
            apply (rule BC)
            done
        qed
    qed
qed

lemma mult_terminates [gd_simp]:
  assumes x_nat: \<open>x N\<close>
  assumes y_nat: \<open>y N\<close>
  shows       \<open>mult x y N\<close>
proof (rule ind[where a=y])
  show habeas_quid_cond: "y N" by (rule y_nat)
  show base_case: "mult x 0 N"
    proof (unfold_def def_mult)
      show "(0 = 0) ? 0 : (add x (mult x P(0))) N"
        apply (rule eqSubst[where a="0"])
        apply (rule eqSym)
        apply (rule condI1)
        apply (rule eqRefl)
        apply (rule nat0)
        apply (rule nat0)
        done
    qed
  show ind_step: "\<forall>a. ((x * a) N) \<turnstile> ((x * S(a)) N)"
    proof (rule forallI, rule entailsI, unfold_def def_mult)
      fix a
      assume HQ: "a N" and BC: "mult x a N"
      show "(S(a) = 0) ? 0 : (add x (mult x P(S(a)))) N"
        proof (rule GD.condT)
          show "S(a) = 0 B"
            apply (rule GD.eqBool)
            apply (rule GD.natS)
            apply (rule HQ)
            apply (rule GD.nat0)
            done
          show "0 N" by (rule nat0)
          show "add x (mult x P(S(a))) N"
            apply (rule add_terminates)
            apply (rule x_nat)
            apply (rule eqSubst[where a="x*a"])
            apply (rule eqSubst[where a="a" and b="P(S(a))"])
            apply (rule eqSym)
            apply (rule predSucSym)
            apply (rule HQ)
            apply (rule eqRefl)
            apply (rule BC)
            done
        qed
    qed
qed

lemma add_0 [gd_simp]:
  assumes a_nat: "a N"
  shows "a + 0 = a"
apply (unfold_def def_add)
apply (rule condI1)
apply (rule eqRefl)
apply (rule a_nat)
done

lemma mult_0 [gd_simp]:
  assumes a_nat: "a N"
  shows "a * 0 = 0"
apply (unfold_def def_mult)
apply (gd_auto)
done

lemma mult_1 [gd_simp]:
  assumes a_nat: "a N"
  shows "a N \<Longrightarrow> a * S(0) = a"
apply (unfold_def def_mult)
apply (rule eqSubst[where a="a" and b="a + (a * P(S(0)))"])
apply (rule eqSubst[where a="0" and b="a * P(S(0))"])
apply (rule eqSubst[where a="0" and b="P(S(0))"])
apply (rule eqSym)
apply (gd_auto)
apply (rule eqSym)
apply (gd_auto)
apply (rule eqSym)
apply (gd_auto)
apply (fold neq_def)
apply (gd_auto)
done

(*
lemma strong_ind:
  assumes y_nat: "y N"
  assumes bc: "Q 0"
  assumes ind_step: "\<And>a. a N \<Longrightarrow> (\<And>xa. xa N \<Longrightarrow> xa \<le> a \<Longrightarrow> Q xa) \<Longrightarrow> Q S(a)"
  shows "Q y"
proof (rule ind)
  show "y N" by (rule y_nat)
  show "Q 0" by (rule bc)
  next
    fix x
    assume x_nat: "x N"
    assume ind_hyp: "Q x"
    show "Q S(x)"
      apply (rule ind_step)
      apply (rule x_nat)
      proof -
        fix xa
        assume xa_nat: "xa N"
        assume xa_le_x: "xa \<le> x"
        show "Q xa"
*)


lemma le_refl [gd_simp]:
  assumes x_nat: "x N"
  shows "(x \<le> x) = 1"
proof (rule ind[where a="x"])
  show "x N" by (rule x_nat)
  show "0 \<le> 0 = 1"
    apply (unfold_def def_leq)
    apply (rule eqSubst[where a="1"])
    apply (rule eqRefl)
    apply (gd_auto)
    done
  show "\<forall>x.(x \<le> x = 1) \<turnstile> (S(x) \<le> S(x) = 1)"
  proof (rule forallI, rule entailsI)
    fix x
    assume x_nat: "x N"
    assume x_refl: "x \<le> x = 1"
    show "((S(x)) \<le> S(x)) = 1"
      apply (unfold_def def_leq)
      apply (rule eqSubst[where a="1" and b="(S(x) = 0) ? 0 : (P(S x) \<le> P(S x))"])
      apply (rule eqSubst[where a="1" and b="P(S x) \<le> P(S x)"])
      apply (rule eqSubst[where a="x" and b="P(S x)"])
      apply (rule eqSym)
      apply (gd_auto)
      apply (rule x_nat)
      apply (rule eqSym)
      apply (rule x_refl)
      apply (rule eqSym)
      apply (gd_auto)
      apply (fold neq_def)
      apply (gd_auto)
      apply (rule x_nat)
      apply (rule condI2)
      apply (fold neq_def)
      apply (gd_auto)
      apply (rule x_nat)
      apply (gd_auto)
      done
  qed
qed

lemma pred_le [gd_simp]:
  assumes z_nat: "z N"
  shows "((P(z)) \<le> z) = 1"
proof (rule ind[where a="z"])
  show "z N" by (rule z_nat)
  show "((P(0)) \<le> 0) = 1"
    apply (unfold_def def_leq)
    apply (gd_auto)
    done
  show "\<forall>x. ((P(x))\<le>x = 1) \<turnstile> (((P(S(x)))\<le>S(x)) = 1)"
    apply (rule forallI)
    apply (rule entailsI)
    proof -
      fix x
      assume x_nat: "x N"
      assume ind_hyp: "((P(x)) \<le> x) = 1"
      show "((P(S(x)))\<le>(S(x))) = 1"
        apply (unfold_def def_leq)
        apply (rule eqSubst[where a="1" and b="((S(x)) = 0) ? 0 : ((P(P(S(x))))\<le>(P(S(x))))"])
        apply (rule eqSubst[where a="x" and b="P(S(x))"])
        apply (rule eqSym)
        apply (gd_auto)
        apply (rule x_nat)
        apply (rule eqSym)
        apply (rule condI2Eq)
        apply (fold neq_def)
        apply (gd_auto)
        apply (rule x_nat)
        apply (gd_auto)
        apply (rule ind_hyp)
        apply (gd_auto)
        apply (rule x_nat)
        done
    qed
qed

lemma le_antisym:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "((x \<le> y) = 1) \<turnstile> ((y \<le> x) = 1) \<turnstile> (x = y)"
sorry

lemma le_0:
  assumes x_nat: "x N"
  assumes H: "x \<le> 0 = 1"
  shows "x = 0"
proof (rule grounded_contradiction[where q="False"])
  show "x = 0 B" by (rule eqBool, rule x_nat, rule nat0)
  show "\<not> x = 0 \<Longrightarrow> False"
    proof -
      assume x_nonzero: "\<not> x = 0"
      show "False"
        apply (rule exF[where P="x \<le> 0 = 1"])
        apply (rule H)
        apply (rule eqSubst[where a="0" and b="x \<le> 0"])
        apply (unfold_def def_leq)
        apply (rule eqSym)
        apply (rule condI2Eq)
        apply (rule x_nonzero)
        apply (gd_auto)
        apply (fold neq_def)
        apply (gd_auto)
        done
    qed
  show "\<not>False" by (gd_auto)
qed

lemma le_trans:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes z_nat: "z N"
  assumes "x \<le> y = 1"
  assumes "y \<le> z = 1"
  shows "(x \<le> y = 1) \<turnstile> (y \<le> z = 1) \<turnstile> (x \<le> z = 1)"
proof (rule ind[where a="z"])
  show "z N" by (rule z_nat)
  show "x\<le>y = 1 \<turnstile> y\<le>0 = 1 \<turnstile> x\<le>0 = 1"
    proof (rule entailsI, rule entailsI)
      assume H: "y \<le> 0 = 1"
      assume H1: "x \<le> y = 1"
      have y_zero: "y = 0" by (rule le_0, rule y_nat, rule H)
      show "x \<le> 0 = 1"
        apply (rule eqSubst[where a="y" and b="0"])
        apply (rule eqSubst[where a="1" and b="S(y)"])
        apply (gd_auto)
        apply (rule eqSym)
        apply (rule y_zero)
        apply (rule y_zero)
        apply (rule eqSubst[where a="1" and b="S(y)"])
        apply (gd_auto)
        apply (rule eqSym)
        apply (rule y_zero)
        apply (rule H1)
        done
    qed
  show "\<forall>xa. (x \<le> y = 1 \<turnstile> y \<le> xa = 1 \<turnstile> x \<le> xa = 1)
    \<turnstile> x \<le> y = 1 \<turnstile> y \<le> S(xa) = 1 \<turnstile> x \<le> S(xa) = 1"
    apply (rule forallI)
    apply (rule entailsI)
    apply (rule entailsI)
    apply (rule entailsI)
    proof -
      fix xa
      assume xa_nat: "xa N"
      assume hyp: "x \<le> y = 1 \<turnstile> y \<le> xa = 1 \<turnstile> x \<le> xa = 1"
      assume x_le_y: "x \<le> y = 1"
      show "x \<le> S(xa) = 1"
        sorry
    qed
qed


lemma less_than_terminates:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "\<forall>z. ((z \<le> x) = 1) \<turnstile> ((z < y) N)"
proof (rule ind[where a="y"])
  show "y N" by (rule y_nat)
  show "\<forall>z. ((z\<le>x) = 1) \<turnstile> ((z < 0) N)"
    apply (rule forallI)
    apply (rule entailsI)
    proof -
      fix z
      show "(z<0) N"
      apply (rule eqSubst[where a="0"])
      apply (rule eqSym)
      apply (gd_auto)
      done
    qed
  show "\<forall>xa. (\<forall>z. ((z\<le>x) = 1) \<turnstile> ((z<xa) N)) \<turnstile> (\<forall>z. ((z\<le>x) = 1) \<turnstile> ((z<S(xa)) N))"
    apply (rule forallI)
    apply (rule entailsI)
    proof -
      fix xa
      assume xa_nat: "xa N"
      assume H: "\<forall>z.(z \<le> x = 1) \<turnstile> ((z < xa) N)"
      show "\<forall>z. ((z\<le>x) = 1) \<turnstile> ((z<S(xa)) N)"
        apply (rule forallI)
        apply (rule entailsI)
        proof -
          fix z
          assume z_nat: "z N"
          assume bc: "(z \<le> x) = 1"
          show "(z < S(xa)) N"
            apply (unfold_def def_less)
            apply (gd_auto)
            apply (rule xa_nat)
            apply (rule z_nat)
            apply (rule eqSubst[where a="xa" and b="P(S(xa))"])
            apply (rule eqSym)
            apply (gd_auto)
            apply (rule xa_nat)
            proof -
              assume "\<not>(S(xa) = 0)"
              assume "\<not>(z = 0)"
              show "((P(z)) < xa) N"
              apply (rule entailsE[where a="((P(z)) \<le> x) = 1"])
              apply (rule forallE[where a="P(z)"])
              apply (rule H)
              apply (gd_auto)
              apply (rule z_nat)
              sorry
            qed
        qed
  qed
qed

lemma zero_less_true [gd_simp]:
  assumes a_nat: "a N"
  shows "0 < S(a) = 1"
apply (unfold_def def_less)
apply (rule condI2Eq)
apply (fold neq_def)
apply (gd_auto)
apply (rule a_nat)
apply (gd_auto)
done

lemma sub_0 [gd_simp]:
  assumes x_nat: "x N"
  shows "x - 0 = x"
apply (unfold_def def_sub)
apply (gd_auto)
apply (rule x_nat)
done

lemma zero_div [gd_simp]:
  assumes x_nat: "x N"
  shows "div 0 S(x) = 0"
apply (unfold_def def_div)
apply (gd_auto)
apply (rule x_nat)
done

lemma div_1 [gd_simp]:
  assumes x_nat: "x N"
  shows "div x 1 = x"
proof (rule ind)
  show "x N" by (rule x_nat)
  show "div 0 1 = 0"
    apply (unfold_def def_div)
    apply (gd_auto)
    done
  show "\<forall>x.(div x 1 = x) \<turnstile> (div S(x) 1 = S(x))"
  proof (rule forallI, rule entailsI)
    fix xa
    assume xa_nat: "xa N"
    assume ind_h: "div xa 1 = xa"
    show "div S(xa) 1 = S(xa)"
      apply (unfold_def def_div)
      apply (rule eqSubst[where a="xa" and b="div ((S(xa))-1) 1"])
      apply (rule eqSubst[where a="xa" and b="(S(xa))-1"])
      apply (unfold_def def_sub)
      apply (rule eqSym)
      apply (rule eqSubst[where a="xa" and b="P((S(xa)) - P(S(0)))"])
      apply (rule eqSubst[where a="0" and b="P(S(0))"])
      apply (rule eqSym)
      apply (gd_auto)
      apply (rule eqSubst[where a="S(xa)" and b="(S(xa)) - 0"])
      apply (rule eqSym)
      apply (gd_auto)
      apply (rule xa_nat)
      apply (rule eqSym)
      apply (gd_auto)
      apply (rule xa_nat)
      apply (gd_auto)
      apply (fold neq_def)
      apply (gd_auto)
      apply (rule xa_nat)
      apply (rule eqSym)
      apply (rule ind_h)
      apply (gd_auto)
      apply (unfold_def def_less)
      apply (rule eqSubst[where a="xa" and b="P(S(xa))"])
      apply (rule eqSym)
      apply (gd_auto)
      apply (rule xa_nat)
      apply (rule contradiction)
      apply (gd_auto)
      apply (rule xa_nat)
      apply (gd_auto)
      apply (rule eqSubst[where a="0" and b="xa < P(S(0))"])
      apply (rule eqSubst[where a="0" and b="P(S(0))"])
      apply (rule eqSym)
      apply (gd_auto)
      apply (rule eqSym)
      apply (gd_auto)
      proof -
        show "xa N" by (rule xa_nat)
        assume H: "\<not> \<not> (S(0) = 0) ? 0 : (S(xa) = 0) ? S(0) : (xa < P(S 0)) = S(0)"
        show "False"
          apply (rule exF[where P="\<not> (S(0) = 0) ? 0 : (S(xa) = 0) ? S(0) : (xa < P(S 0)) = S(0)"])
          apply (rule eqSubst[where a="0" and b="(S(0) = 0) ? 0 : (S(xa) = 0) ? S(0) : (xa < P(S 0))"])
          apply (rule eqSym)
          apply (rule condI2Eq)
          apply (fold neq_def)
          apply (gd_auto)
          apply (rule condI2Eq)
          apply (fold neq_def)
          apply (gd_auto)
          apply (rule xa_nat)
          apply (rule nat0)
          apply (rule eqSubst[where a="0" and b="P(S(0))"])
          apply (rule eqSym)
          apply (gd_auto)
          apply (unfold neq_def)
          apply (rule H)
          done
      qed
  qed
qed

lemma division_terminates:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "div x S(y) N"
proof (rule ind[where a="x"])
  show hq_cond: "x N" by (rule x_nat)
  show base_case: "div 0 S(y) N"
    apply (rule eqSubst[where a="0"])
    apply (rule eqSym)
    apply (unfold_def def_div)
    apply (gd_auto)
    apply (rule y_nat)
    apply (rule nat0)
    done
  show "\<forall>x.((div x S(y)) N) \<turnstile> ((div S(x) S(y)) N)"
  proof (rule forallI, rule entailsI)
    fix a
    assume a_nat: "a N"
    assume bc: "div a S(y) N"
    show "(div S(a) S(y)) N"
      apply (unfold_def def_div)
      apply (gd_auto)
      (* Need both strong induction AND less than terminating proof *)
      sorry
  qed
qed

(*
lemma mult_comm:
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  shows "a * b = b * a"
proof (rule ind[where a="b"])
  show "b N" by (rule b_nat)
  show ""

lemma distr_mult_add:
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  assumes c_nat: "c N"
  shows "a * (b + c) = (a * b) + (a * c)"
apply (unfold_def def_mult)

proof (rule ind[where a="b + c"])
  show "b + c N" by (rule add_terminates, rule b_nat, rule c_nat)
  show "a * 0 = (a * b) + (a * c)"
 *)

(*
locale liar_def =
  fixes L :: "o"
  assumes def_l: "L := \<not>L"
begin

lemma f: "False"
proof -
  assume l_holds: "L"
  have "\<not>L"
    apply (rule defU[where a="L" and b="\<not>L"])
    apply (rule def_liar)
    apply (rule dNegI)
    apply (rule l_holds)
    done
  show "False"
    sorry
qed
end
*)

end (* End of theory *)
