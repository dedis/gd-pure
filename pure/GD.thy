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
  eqNum :: \<open>num \<Rightarrow> num \<Rightarrow> o\<close>  (infixl \<open>\<doteq>\<close> 45)
where
  eqSubst: \<open>\<lbrakk>a \<doteq> b; Q a\<rbrakk> \<Longrightarrow> Q b\<close> and
  eqSym: \<open>a \<doteq> b \<Longrightarrow> b \<doteq> a\<close>

lemma eq_trans: "a \<doteq> b \<Longrightarrow> b \<doteq> c \<Longrightarrow> a \<doteq> c"
apply (rule eqSubst[where a="b" and b="c"])
apply (assumption)
apply (assumption)
done

definition neq :: \<open>num \<Rightarrow> num \<Rightarrow> o\<close> (infixl \<open>\<noteq>\<close> 45)
  where \<open>a \<noteq> b \<equiv> \<not> (a \<doteq> b)\<close>
definition bJudg :: \<open>o \<Rightarrow> o\<close> (\<open>_ B\<close> [21] 20)
  where \<open>(p B) \<equiv> (p \<or> \<not>p)\<close>
definition isNat :: \<open>num \<Rightarrow> o\<close> (\<open>_ N\<close> [21] 20)
where "x N \<equiv> x \<doteq> x"
definition conj :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> (infixl \<open>\<and>\<close> 35)
  where \<open>p \<and> q \<equiv> \<not>(\<not>p \<or> \<not>q)\<close>
definition impl :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> (infixl \<open>\<longrightarrow>\<close> 25)
  where \<open>p \<longrightarrow> q \<equiv> \<not>p \<or> q\<close>

axiomatization
  num_zero :: \<open>num\<close>                        and
  num_suc :: \<open>num \<Rightarrow> num\<close>     (\<open>S(_)\<close> [800]) and
  num_pred :: \<open>num \<Rightarrow> num\<close>    (\<open>P(_)\<close> [800])
where
  nat0: \<open>num_zero N\<close> and
  sucInj: \<open>S a \<doteq> S b \<Longrightarrow> a \<doteq> b\<close> and
  sucCong: \<open>a \<doteq> b \<Longrightarrow> S a \<doteq> S b\<close> and
  predCong: \<open>a \<doteq> b \<Longrightarrow> P a \<doteq> P b\<close> and
  eqBool: \<open>\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow> (a \<doteq> b) B\<close> and
  sucNonZero: \<open>a N \<Longrightarrow> S a \<noteq> num_zero\<close> and
  predSucSym: \<open>a N \<Longrightarrow> P(S(a)) \<doteq> a\<close> and
  pred0: \<open>P(num_zero) \<doteq> num_zero\<close>

lemma zeroRefl [gd_simp]: "num_zero \<doteq> num_zero"
apply (fold isNat_def)
apply (rule nat0)
done

lemma natS [gd_simp]:
  assumes a_nat: "a N"
  shows "S a N"
apply (unfold isNat_def)
apply (rule sucCong)
apply (fold isNat_def)
apply (rule a_nat)
done

lemma natP [gd_simp]:
  assumes a_nat: "a N"
  shows "P a N"
apply (unfold isNat_def)
apply (rule predCong)
apply (fold isNat_def)
apply (rule a_nat)
done

lemma implI [gd_simp]:
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
  where \<open>True \<equiv> 0 \<doteq> 0\<close>
definition False
  where \<open>False \<equiv> S(0) \<doteq> 0\<close>

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
  forAllNeg: "\<lbrakk>\<not>(\<forall>x. Q x); (Q x) B\<rbrakk> \<Longrightarrow> \<exists>x. \<not>(Q x)" and
  existsNeg: "\<lbrakk>\<not>(\<exists>x. Q x); (Q x) B\<rbrakk> \<Longrightarrow> \<forall>x. \<not>(Q x)" and
  ind: \<open>\<lbrakk>a N; Q 0; \<forall>x.(Q x \<turnstile> Q S(x))\<rbrakk> \<Longrightarrow> Q a\<close>

section \<open>Axiomatization of conditional evaluation in GD\<close>

consts
  cond :: \<open>o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
syntax
  "_cond" :: \<open>o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (\<open>if _ then _ else _\<close> [25, 24, 24] 24)
translations
  "if c then a else b" \<rightleftharpoons> "CONST cond c a b"

axiomatization
where
  condI1: \<open>\<lbrakk>c; a N\<rbrakk> \<Longrightarrow> (if c then a else b) \<doteq> a\<close> and
  condI2: \<open>\<lbrakk>\<not>c; b N\<rbrakk> \<Longrightarrow> (if c then a else b) \<doteq> b\<close> and
  condT: \<open>\<lbrakk>c B; c \<Longrightarrow> a N; \<not>c \<Longrightarrow> b N\<rbrakk> \<Longrightarrow> if c then a else b N\<close>

lemma condI1Eq:
  assumes c_holds: "c"
  assumes d_nat: "d N"
  assumes a_eq_d: "a \<doteq> d"
  shows "(if c then a else b) \<doteq> d"
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
  assumes a_eq_d: "b \<doteq> d"
  shows "(if c then a else b) \<doteq> d"
apply (rule eqSubst[where a="d" and b="b"])
apply (rule eqSym)
apply (rule a_eq_d)
apply (rule condI2)
apply (rule not_c)
apply (rule d_nat)
done

lemma condI3:
  assumes a_nat: "a N"
  assumes c_bool: "c B"
  shows "(if c then a else a) \<doteq> a"
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

lemma condI3Eq:
  assumes a_nat: "a N"
  assumes c_bool: "c B"
  assumes d_eq_a: "d \<doteq> a"
  assumes e_eq_a: "e \<doteq> a"
  shows "(if c then d else e) \<doteq> a"
apply (rule disjE1[where P="c" and Q="\<not>c"])
apply (fold GD.bJudg_def)
apply (rule c_bool)
apply (rule eqSubst[where a="a" and b="d"])
apply (rule eqSym)
apply (rule d_eq_a)
apply (rule condI1)
apply (assumption)
apply (rule a_nat)
apply (rule eqSubst[where a="a" and b="e"])
apply (rule eqSym)
apply (rule e_eq_a)
apply (rule condI2)
apply (assumption)
apply (rule a_nat)
done

ML_file "gd_auto.ML"

section \<open>Definitional Mechanism in GD\<close>

axiomatization
  def :: \<open>'a \<Rightarrow> 'a \<Rightarrow> o\<close> (infix \<open>:=\<close> 10)
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

lemmas [gd_simp] = condI3 condT nat0 natS natP sucNonZero predSucSym pred0 neq_def eqBool sucCong
ML_file \<open>unfold_def.ML\<close>

section \<open>Deductions of non-elementary inference rules.\<close>

lemma true [gd_simp]: "True"
apply (unfold GD.True_def)
apply (gd_auto)
done

lemma true_bool [gd_simp]: "True B"
apply (unfold GD.bJudg_def)
apply (rule disjI1)
apply (rule true)
done

lemma not_false [gd_simp]: "\<not>False"
proof (unfold False_def)
  show "\<not>(S(0) \<doteq> 0)"
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

lemma neq_com:
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  assumes ab_neq: "a \<noteq> b"
  shows "b \<noteq> a"
proof (unfold neq_def, rule grounded_contradiction[where q="a\<doteq>b"])
  show "(\<not>(b\<doteq>a)) B"
    apply (gd_auto)
    apply (rule b_nat)
    apply (rule a_nat)
    done
  next
    assume H: "\<not> \<not> b \<doteq> a"
    show "a \<doteq> b"
    apply (rule eqSym)
    apply (rule dNegE)
    apply (rule H)
    done
  next
    assume H: "\<not> \<not> b \<doteq> a"
    show "\<not> a \<doteq> b"
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
          have eq_suc: "x \<doteq> S(x)"
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
  add  :: "num \<Rightarrow> num \<Rightarrow> num"  (infixl "+" 60) and
  sub  :: "num \<Rightarrow> num \<Rightarrow> num"  (infixl "-" 60) and
  mult :: "num \<Rightarrow> num \<Rightarrow> num"  (infixl "*" 70) and
  div  :: "num \<Rightarrow> num \<Rightarrow> num"                  and
  less :: "num \<Rightarrow> num \<Rightarrow> num"  (infix "<" 50)  and
  leq  :: "num \<Rightarrow> num \<Rightarrow> num"  (infix "\<le>" 50) and
  omega :: "'a"
where
  def_add: "add := (\<lambda>x y. if y \<doteq> 0 then x else S(x + P y))" and
  def_sub: "sub := (\<lambda>x y. if y \<doteq> 0 then x else P(x - P y))" and
  def_mult: "mult := (\<lambda>x y. if y \<doteq> 0 then 0 else (x + x * P y))" and
  def_leq: "leq := (\<lambda>x y. if x \<doteq> 0 then 1 else (if y \<doteq> 0 then 0 else (P x \<le> P y)))" and
  def_less: "less := (\<lambda>x y. if y \<doteq> 0 then 0 else (if x \<doteq> 0 then 1 else (P x < P y)))" and
  def_div: "div := (\<lambda>x y. if x < y \<doteq> 1 then 0 else S(div (x - y) y))" and
  def_omega: "omega := omega"

definition greater :: "num \<Rightarrow> num \<Rightarrow> num" (infix ">" 50) where
  "greater x y \<equiv> 1 - (x \<le> y)"

definition greater_eq :: "num \<Rightarrow> num \<Rightarrow> num" (infix "\<ge>" 50) where
  "greater_eq x y \<equiv> 1 - (x < y)"

(* Returns y if S(y) > sqrt(x), else returns the greatest y s.t. y*y\<le>x. *)
axiomatization
  sqrt_h :: "num \<Rightarrow> num \<Rightarrow> num"
where
  def_sqrt_h: "sqrt_h := (\<lambda>x y. if (S(y) * S(y) > x \<doteq> 1) then y else (sqrt_h x S(y)))"

definition floor_sqrt :: "num \<Rightarrow> num" where
  "floor_sqrt x \<equiv> sqrt_h x 0"

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

lemma less_0_false [gd_simp]: "(x < 0) \<doteq> 0"
apply (unfold_def def_less)
apply (rule condI1)
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
      show "if (0 \<doteq> 0) then x else S(add x P(0)) N"
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
      assume HQ: "a N" and BC: "add x a N"
      show "if (S(a) \<doteq> 0) then x else S(add x P(S(a))) N"
        proof (rule GD.condT)
          show "S(a) \<doteq> 0 B"
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
            apply (fold isNat_def)
            apply (rule BC)
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
      show "if (0 \<doteq> 0) then 0 else (add x (mult x P(0))) N"
        apply (rule eqSubst[where a="0"])
        apply (rule eqSym)
        apply (rule condI1)
        apply (rule zeroRefl)
        apply (rule nat0)
        apply (rule nat0)
        done
    qed
  show ind_step: "\<forall>a. ((x * a) N) \<turnstile> ((x * S(a)) N)"
    proof (rule forallI, rule entailsI, unfold_def def_mult)
      fix a
      assume HQ: "a N" and BC: "mult x a N"
      show "if (S(a) \<doteq> 0) then 0 else (add x (mult x P(S(a)))) N"
        proof (rule GD.condT)
          show "S(a) \<doteq> 0 B"
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
            apply (fold isNat_def)
            apply (rule BC)
            apply (rule BC)
            done
        qed
    qed
qed

lemma add_0 [gd_simp]:
  assumes a_nat: "a N"
  shows "a + 0 \<doteq> a"
apply (unfold_def def_add)
apply (rule condI1)
apply (rule zeroRefl)
apply (rule a_nat)
done

lemma mult_0 [gd_simp]:
  shows "a * 0 \<doteq> 0"
apply (unfold_def def_mult)
apply (rule condI1)
apply (gd_auto)
done

lemma mult_1 [gd_simp]:
  assumes a_nat: "a N"
  shows "a N \<Longrightarrow> a * S(0) \<doteq> a"
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
apply (rule condI2)
apply (fold neq_def)
apply (gd_auto)
done

lemma zero_leq_true [gd_simp]:
  assumes x_nat: "x N"
  shows "0 \<le> x \<doteq> 1"
apply (unfold_def def_leq)
apply (rule condI1Eq)
apply (gd_auto)
done

lemma leq_refl [gd_simp]:
  assumes x_nat: "x N"
  shows "(x \<le> x) \<doteq> 1"
proof (rule ind[where a="x"])
  show "x N" by (rule x_nat)
  show "0 \<le> 0 \<doteq> 1"
    apply (unfold_def def_leq)
    apply (rule eqSubst[where a="1"])
    apply (gd_auto)
    apply (rule condI1)
    apply (gd_auto)
    done
  show "\<forall>x.(x \<le> x \<doteq> 1) \<turnstile> (S(x) \<le> S(x) \<doteq> 1)"
  proof (rule forallI, rule entailsI)
    fix x
    assume x_nat: "x N"
    assume x_refl: "x \<le> x \<doteq> 1"
    show "((S(x)) \<le> S(x)) \<doteq> 1"
      apply (unfold_def def_leq)
      apply (rule eqSubst[where a="1" and b="if (S(x) \<doteq> 0) then 0 else (P(S x) \<le> P(S x))"])
      apply (rule eqSubst[where a="1" and b="P(S x) \<le> P(S x)"])
      apply (rule eqSubst[where a="x" and b="P(S x)"])
      apply (rule eqSym)
      apply (gd_auto)
      apply (rule x_nat)
      apply (rule eqSym)
      apply (rule x_refl)
      apply (rule eqSym)
      apply (rule condI2)
      apply (gd_auto)
      apply (fold neq_def)
      apply (gd_auto)
      apply (rule x_nat)
      apply (gd_auto)
      apply (rule x_nat)
      done
  qed
qed

lemma pred_le [gd_simp]:
  assumes z_nat: "z N"
  shows "P(z) \<le> z \<doteq> 1"
proof (rule ind[where a="z"])
  show "z N" by (rule z_nat)
  show "((P(0)) \<le> 0) \<doteq> 1"
    apply (unfold_def def_leq)
    apply (rule condI1)
    apply (gd_auto)
    done
  show "\<forall>x. ((P(x))\<le>x \<doteq> 1) \<turnstile> (((P(S(x)))\<le>S(x)) \<doteq> 1)"
    apply (rule forallI)
    apply (rule entailsI)
    proof -
      fix x
      assume x_nat: "x N"
      assume ind_hyp: "((P(x)) \<le> x) \<doteq> 1"
      show "((P(S(x)))\<le>(S(x))) \<doteq> 1"
        apply (unfold_def def_leq)
        apply (rule eqSubst[where a="1" and b="if ((S(x)) \<doteq> 0) then 0 else ((P(P(S(x))))\<le>(P(S(x))))"])
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
  shows "((x \<le> y) \<doteq> 1) \<turnstile> ((y \<le> x) \<doteq> 1) \<turnstile> (x \<doteq> y)"
sorry

lemma le_0:
  assumes x_nat: "x N"
  assumes H: "x \<le> 0 \<doteq> 1"
  shows "x \<doteq> 0"
proof (rule grounded_contradiction[where q="False"])
  show "x \<doteq> 0 B" by (rule eqBool, rule x_nat, rule nat0)
  show "\<not> x \<doteq> 0 \<Longrightarrow> False"
    proof -
      assume x_nonzero: "\<not> x \<doteq> 0"
      show "False"
        apply (rule exF[where P="x \<le> 0 \<doteq> 1"])
        apply (rule H)
        apply (rule eqSubst[where a="0" and b="x \<le> 0"])
        apply (unfold_def def_leq)
        apply (rule eqSym)
        apply (rule condI2Eq)
        apply (rule x_nonzero)
        apply (gd_auto)
        apply (fold neq_def)
        apply (rule condI1)
        apply (gd_auto)
        done
    qed
  show "\<not>False" by (gd_auto)
qed

lemma leq_monotone_suc [gd_simp]:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes x_leq_y: "x \<le> y \<doteq> 1"
  shows "S x \<le> S y \<doteq> 1"
apply (unfold_def def_leq)
apply (rule condI2Eq)
apply (fold neq_def)
apply (gd_auto)
apply (rule x_nat)
apply (gd_auto)
apply (rule condI2Eq)
apply (fold neq_def)
apply (gd_auto)
apply (rule y_nat)
apply (gd_auto)
apply (rule eqSubst[where a="x" and b="P(S(x))"])
apply (rule eqSym)
apply (gd_auto)
apply (rule x_nat)
apply (rule eqSubst[where a="y" and b="P(S(y))"])
apply (rule eqSym)
apply (gd_auto)
apply (rule y_nat)
apply (rule x_leq_y)
done

lemma num_cases:
  assumes x_nat: "x N"
  shows "x \<doteq> 0 \<or> (\<exists>y. x \<doteq> S y)"
proof (rule ind[where a="x"])
  show "x N" by (rule x_nat)
  show "0 \<doteq> 0 \<or> (\<exists>y. 0 \<doteq> S y)" by (rule disjI1, gd_auto)
  show "\<forall>x. x\<doteq>0 \<or> (\<exists>y. x \<doteq> S y) \<turnstile> S x \<doteq> 0 \<or> (\<exists>y. S x \<doteq> S y)"
    apply (rule forallI)
    apply (rule entailsI)
    proof -
      fix x
      assume x_nat: "x N"
      show "S x \<doteq> 0 \<or> (\<exists>y. S x \<doteq> S y)"
        apply (rule disjI2)
        apply (rule existsI[where a="x"])
        apply (rule x_nat)
        apply (gd_auto)
        apply (fold isNat_def)
        apply (rule x_nat)
        done
    qed
qed

lemma num_non_zero [gd_simp]:
  assumes x_nat: "x N"
  assumes x_nz: "\<not> x \<doteq> 0"
  shows "\<exists>y. x \<doteq> S(y)"
proof -
  have "x \<doteq> 0 \<or> (\<exists>y. x \<doteq> S y)"
    apply (rule num_cases)
    apply (rule x_nat)
    done
  then show ?thesis
    apply (rule disjE1)
    apply (rule exF[where P="x\<doteq>0"])
    apply (assumption)
    apply (rule x_nz)
    apply (assumption)
    done
qed

lemma leq_nz_monotone:
  assumes xa_nz: "\<not> xa \<doteq> 0"
  assumes xa_le_ya: "xa \<le> ya \<doteq> 1"
  assumes ya_nat: "ya N"
  shows "ya \<noteq> 0"
proof (rule grounded_contradiction[where q="xa \<le> 0 \<doteq> 1"])
  show "ya \<noteq> 0 B" by (rule neq_bool, rule ya_nat, rule nat0)
  show "\<not> ya \<noteq> 0 \<Longrightarrow> xa \<le> 0 \<doteq> 1"
    proof -
      assume H: "\<not> ya \<noteq> 0"
      have ya_nz: "ya \<doteq> 0" by (rule dNegE, fold neq_def, rule H)
      show "xa \<le> 0 \<doteq> 1"
        apply (rule eqSubst[where a="ya" and b="0"])
        apply (rule ya_nz)
        apply (rule eqSubst[where a="1" and b="S ya"])
        apply (gd_auto)
        apply (rule eqSym)
        apply (rule ya_nz)
        apply (rule xa_le_ya)
        done
    qed
  show "\<not> xa \<le> 0 \<doteq> 1"
    apply (rule eqSubst[where a="0" and b="xa \<le> 0"])
    apply (rule eqSym)
    apply (unfold_def def_leq)
    apply (rule condI2Eq)
    apply (rule xa_nz)
    apply (rule nat0)
    apply (rule condI1)
    apply (gd_auto)
    apply (fold neq_def)
    apply (gd_auto)
    done
qed

lemma leq_0_if_nz [gd_simp]:
  assumes H: "\<not> x \<doteq> 0"
  shows "x \<le> 0 \<doteq> 0"
apply (unfold_def def_leq)
apply (rule condI2Eq)
apply (rule H)
apply (gd_auto)
apply (rule condI1)
apply (gd_auto)
done


lemma leq_terminates:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "x \<le> y N"
proof -
  have H: "\<forall>x. x\<le>y N"
  proof (rule ind[where a="y"])
    show "y N" by (rule y_nat)
    show "\<forall>x'. x' \<le> 0 N"
      apply (rule forallI)
      proof -
        fix x'
        assume x'_nat: "x' N"
        show "x' \<le> 0 N"
          apply (unfold_def def_leq)
          apply (rule condT)
          apply (rule eqBool)
          apply (rule x'_nat)
          apply (gd_auto)
          proof -
            assume H: "\<not> 0 \<doteq> 0"
            show "P x' \<le> P 0 N"
              apply (rule exF[where P="0\<doteq>0"])
              apply (rule zeroRefl)
              apply (rule H)
              done
          qed
      qed
    show "\<forall>x. (\<forall>xa. xa \<le> x N) \<turnstile> (\<forall>xa. xa \<le> S(x) N)"
      apply (rule forallI)
      apply (rule entailsI)
      proof -
        fix x
        assume x_nat: "x N"
        assume H: "\<forall>xa. xa \<le> x N"
        show "\<forall>xa. xa \<le> S(x) N"
          apply (rule forallI)
          proof -
            fix xa
            assume xa_nat: "xa N"
            show "xa \<le> S(x) N"
              apply (unfold_def def_leq)
              apply (gd_auto)
              apply (rule xa_nat)
              apply (rule x_nat)
              apply (rule eqSubst[where a="x" and b="P(S(x))"])
              apply (rule eqSym)
              apply (gd_auto)
              apply (rule x_nat)
              apply (rule forallE[where a="P xa"])
              apply (rule H)
              apply (gd_auto)
              apply (rule xa_nat)
              done
          qed
      qed
  qed
  then show ?thesis
    apply (rule forallE)
    apply (rule x_nat)
    done
qed

lemma leq_suc_eq:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "x \<le> y \<doteq> S x \<le> S y"
proof (rule ind[where a="y"])
  show "y N" by (rule y_nat)
  show "x \<le> 0 \<doteq> S x \<le> S 0"
    apply (rule disjE1[where P="x \<doteq> 0" and Q="\<not> x \<doteq> 0"])
    apply (fold bJudg_def)
    apply (rule eqBool)
    apply (rule x_nat)
    apply (gd_auto)
    apply (rule eqSubst[where a="1"])
    apply (rule eqSym)
    apply (rule eqSubst[where a="0" and b="x"])
    apply (rule eqSym)
    apply (assumption)
    apply (rule leq_refl)
    apply (gd_auto)
    apply (rule eqSubst[where a="0" and b="x"])
    apply (rule eqSym)
    apply (assumption)
    apply (rule leq_refl)
    apply (gd_auto)
    apply (rule eqSubst[where a="0"])
    apply (rule eqSym)
    apply (unfold_def def_leq)
    apply (rule condI2Eq)
    apply (fold neq_def)
    apply (gd_auto)
    apply (rule x_nat)
    apply (gd_auto)
    apply (rule condI2Eq)
    apply (fold neq_def)
    apply (gd_auto)
    apply (rule eqSubst[where a="x" and b="P S x"])
    apply (rule eqSym)
    apply (gd_auto)
    apply (rule x_nat)
    apply (rule eqSubst[where a="0" and b="P S 0"])
    apply (rule eqSym)
    apply (gd_auto)
    apply (rule leq_0_if_nz)
    apply (fold neq_def)
    apply (assumption)
    apply (rule leq_0_if_nz)
    apply (fold neq_def)
    apply (assumption)
    done
  show "\<forall>xa. x \<le> xa \<doteq> S(x) \<le> S(xa) \<turnstile> x \<le> S(xa) \<doteq> S(x) \<le> S(S(xa))"
    apply (rule forallI)
    apply (rule entailsI)
    proof -
      fix xa
      assume xa_nat: "xa N"
      assume H: "x \<le> xa \<doteq> S x \<le> S xa"
      show "x \<le> S xa \<doteq> S x \<le> S S xa"
        apply (rule defE[where Q="\<lambda>c. (x \<le> S xa) \<doteq> (c (S x) (S S xa))" and a="leq" and b="(\<lambda>x y. if x \<doteq> 0 then 1 else (if y \<doteq> 0 then 0 else (P x \<le> P y)))"])
        apply (rule def_leq)
        apply (rule eqSubst[where a="if S S xa \<doteq> num_zero then num_zero else P S x \<le> P S S xa"])
        apply (rule eqSym)
        apply (rule condI2Eq)
        apply (fold neq_def)
        apply (gd_auto)
        apply (rule x_nat)
        apply (rule condT)
        apply (rule eqBool)
        apply (gd_auto)
        apply (rule xa_nat)
        apply (gd_auto)
        apply (rule leq_terminates)
        apply (rule eqSubst[where a="x" and b="P S x"])
        apply (rule eqSym)
        apply (rule predSucSym)
        apply (rule x_nat)
        apply (rule x_nat)
        apply (gd_auto)
        apply (rule xa_nat)
        apply (gd_auto)
        apply (fold isNat_def)
        apply (rule condT)
        apply (rule eqBool)
        apply (gd_auto)
        apply (rule xa_nat)
        apply (gd_auto)
        apply (rule leq_terminates)
        apply (gd_auto)
        apply (rule x_nat)
        apply (gd_auto)
        apply (rule xa_nat)
        apply (rule eqSubst[where a="P S x \<le> P S S xa" and b="(if S S xa \<doteq> num_zero then num_zero else P S x \<le> P S S xa)"])
        apply (rule eqSym)
        apply (rule condI2Eq)
        apply (fold neq_def)
        apply (gd_auto)
        apply (rule xa_nat)
        apply (rule leq_terminates)
        apply (gd_auto)
        apply (rule x_nat)
        apply (gd_auto)
        apply (rule xa_nat)
        apply (fold isNat_def)
        apply (rule leq_terminates)
        apply (gd_auto)
        apply (rule x_nat)
        apply (gd_auto)
        apply (rule xa_nat)
        apply (rule eqSubst[where a="x" and b="P S x"])
        apply (rule eqSym)
        apply (rule predSucSym)
        apply (rule x_nat)
        apply (rule eqSubst[where a="S xa" and b="P S S xa"])
        apply (rule eqSym)
        apply (gd_auto)
        apply (rule xa_nat)
        apply (fold isNat_def)
        apply (rule leq_terminates)
        apply (rule x_nat)
        apply (gd_auto)
        apply (rule xa_nat)
        done
    qed
qed

lemma suc_pred_inv [gd_simp]:
  assumes x_nat: "x N"
  assumes x_nz: "\<not> x \<doteq> 0"
  shows "S P x \<doteq> x"
proof -
  have "\<exists>u. x \<doteq> S(u)" by (gd_auto, rule x_nat, rule x_nz)
  then show ?thesis
    apply (rule existsE)
    proof -
      fix a
      assume a_nat: "a N"
      assume H: "x \<doteq> S a"
      show "S P x \<doteq> x"
        apply (rule eqSubst[where a="S a"])
        apply (rule eqSym)
        apply (rule H)
        apply (rule eqSubst[where a="a" and b="P S a"])
        apply (rule eqSym)
        apply (rule predSucSym)
        apply (rule a_nat)
        apply (fold isNat_def)
        apply (rule natS)
        apply (rule a_nat)
        done
    qed
qed

lemma cases_nat:
  assumes x_nat: "x N"
  assumes x_z: "x \<doteq> 0 \<Longrightarrow> Q 0"
  assumes x_nz: "\<not> x \<doteq> 0 \<Longrightarrow> Q x"
  shows "Q x"
apply (rule disjE1[where P="x \<doteq> 0" and Q="\<not> x \<doteq> 0"])
apply (fold GD.bJudg_def)
apply (gd_auto)
apply (rule x_nat)
apply (rule eqSubst[where a="0" and b="x"])
apply (rule eqSym)
apply (assumption)
apply (rule x_z)
apply (assumption)
apply (rule x_nz)
apply (assumption)
done

lemma leq_monotone_pred:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes H: "x \<le> y \<doteq> 1"
  shows "P x \<le> P y \<doteq> 1"
proof (rule cases_nat[where x="x"])
  show "x N" by (rule x_nat)
  show "x \<doteq> 0 \<Longrightarrow> P 0 \<le> P y \<doteq> 1"
    apply (rule eqSubst[where a="0" and b="P 0"])
    apply (rule eqSym)
    apply (gd_auto)
    apply (rule y_nat)
    done
  show "\<not> x \<doteq> 0 \<Longrightarrow> P x \<le> P y \<doteq> 1"
  proof (rule cases_nat[where x="y"])
    show "y N" by (rule y_nat)
    show "\<not> x \<doteq> 0 \<Longrightarrow> y \<doteq> 0 \<Longrightarrow> P x \<le> P 0 \<doteq> 1"
      apply (rule exF[where P="x \<le> y \<doteq> 1"])
      apply (rule H)
      apply (rule eqSubst[where a="0" and b="x \<le> y"])
      apply (rule eqSym)
      apply (rule eqSubst[where a="0" and b="y"])
      apply (rule eqSym)
      apply (assumption)
      apply (gd_auto)
      apply (fold neq_def)
      apply (gd_auto)
      done
    show "\<not> x \<doteq> 0 \<Longrightarrow> \<not> y \<doteq> 0 \<Longrightarrow> P x \<le> P y \<doteq> 1"
    proof -
      assume x_nz: "\<not> x \<doteq> 0"
      assume y_nz: "\<not> y \<doteq> 0"
      have H1: "P x \<le> P y \<doteq> S P x \<le> S P y"
        apply (rule leq_suc_eq)
        apply (gd_auto)
        apply (rule x_nat)
        apply (gd_auto)
        apply (rule y_nat)
        done
      have H2: "P x \<le> P y \<doteq> x \<le> y"
        apply (rule eqSubst[where a="S P x" and b="x"])
        apply (gd_auto)
        apply (rule x_nat)
        apply (rule x_nz)
        apply (rule eqSubst[where a="S P y" and b="y"])
        apply (gd_auto)
        apply (rule y_nat)
        apply (rule y_nz)
        apply (rule eqSubst[where a="P x" and b="P S P x"])
        apply (rule eqSym)
        apply (rule predSucSym)
        apply (gd_auto)
        apply (rule x_nat)
        apply (rule eqSubst[where a="P y" and b="P S P y"])
        apply (rule eqSym)
        apply (rule predSucSym)
        apply (gd_auto)
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

lemma leq_trans:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes z_nat: "z N"
  assumes x_leq_y: "x \<le> y \<doteq> 1"
  assumes y_leq_z: "y \<le> z \<doteq> 1"
  shows "x \<le> z \<doteq> 1"
proof -
  have quantized: "\<forall>x y. (x \<le> y \<doteq> 1) \<turnstile> (y \<le> z \<doteq> 1) \<turnstile> (x \<le> z \<doteq> 1)"
  proof (rule ind[where a="z"])
  show "z N" by (rule z_nat)
  show "\<forall>x y. x \<le> y \<doteq> 1 \<turnstile>
    y \<le> 0 \<doteq> 1 \<turnstile> x \<le> 0 \<doteq> 1"
    proof (rule forallI, rule forallI, rule entailsI, rule entailsI)
      fix xa ya
      assume xa_nat: "xa N"
      assume ya_nat: "ya N"
      assume H: "ya \<le> 0 \<doteq> 1"
      assume H1: "xa \<le> ya \<doteq> 1"
      have ya_zero: "ya \<doteq> 0" by (rule le_0, rule ya_nat, rule H)
      show "xa \<le> 0 \<doteq> 1"
        apply (rule eqSubst[where a="ya" and b="0"])
        apply (rule eqSubst[where a="1" and b="S(ya)"])
        apply (gd_auto)
        apply (rule eqSym)
        apply (rule ya_zero)
        apply (rule ya_zero)
        apply (rule eqSubst[where a="1" and b="S(ya)"])
        apply (gd_auto)
        apply (rule eqSym)
        apply (rule ya_zero)
        apply (rule H1)
        done
    qed
  show "\<forall>x. (\<forall>xa y. xa \<le> y \<doteq> 1 \<turnstile> y \<le> x \<doteq> 1 \<turnstile> xa \<le> x \<doteq> 1) \<turnstile>
     (\<forall>xa y. xa \<le> y \<doteq> 1 \<turnstile> y \<le> S x \<doteq> 1 \<turnstile> xa \<le> S x \<doteq> 1)"
    apply (rule forallI)
    apply (rule entailsI)
    proof -
      fix x
      assume x_nat: "x N"
      show "\<forall>xa y. xa \<le> y \<doteq> 1 \<turnstile> y \<le> x \<doteq> 1 \<turnstile> xa \<le> x \<doteq> 1 \<Longrightarrow>
            \<forall>xa y. xa \<le> y \<doteq> 1 \<turnstile> y \<le> S x \<doteq> 1 \<turnstile> xa \<le> S x \<doteq> 1"
        proof -
          assume hyp: "\<forall>xa y. xa \<le> y \<doteq> 1 \<turnstile> y \<le> x \<doteq> 1 \<turnstile> xa \<le> x \<doteq> 1"
          show "\<forall>xa y. xa \<le> y \<doteq> 1 \<turnstile> y \<le> S x \<doteq> 1 \<turnstile> xa \<le> S x \<doteq> 1"
            apply (rule forallI)
            apply (rule forallI)
            apply (rule entailsI)
            apply (rule entailsI)
            proof -
              fix xa ya
              assume xa_nat: "xa N"
              assume ya_nat: "ya N"
              assume xa_leq_ya: "xa \<le> ya \<doteq> 1"
              assume ya_leq_sx: "ya \<le> S x \<doteq> 1"
              show "xa \<le> S x \<doteq> 1"
                apply (unfold_def def_leq)
                apply (rule condI3Eq)
                apply (gd_auto)
                apply (rule xa_nat)
                apply (gd_auto)
                apply (rule condI2Eq)
                apply (fold neq_def)
                apply (gd_auto)
                apply (rule x_nat)
                apply (gd_auto)
                apply (rule eqSubst[where a="x" and b="P(S(x))"])
                apply (rule eqSym)
                apply (gd_auto)
                apply (rule x_nat)
                apply (rule disjE1[where P="xa\<doteq>0" and Q="\<not>(xa\<doteq>0)"])
                apply (fold GD.bJudg_def)
                apply (rule eqBool)
                apply (rule xa_nat)
                apply (rule nat0)
                apply (rule eqSubst[where a="0" and b="P(xa)"])
                apply (rule eqSubst[where a="0" and b="xa"])
                apply (rule eqSym)
                apply (assumption)
                apply (rule eqSym)
                apply (gd_auto)
                apply (rule x_nat)
                proof -
                  assume xa_nz: "\<not> xa \<doteq> 0"
                  have ya_nz: "\<not> ya \<doteq> 0"
                    apply (fold neq_def)
                    apply (rule leq_nz_monotone[where xa="xa"])
                    apply (rule xa_nz)
                    apply (rule xa_leq_ya)
                    apply (rule ya_nat)
                    done
                  have H: "P(ya) \<le> P(S x) \<doteq> 1"
                    apply (rule GD.leq_monotone_pred)
                    apply (rule ya_nat)
                    apply (gd_auto)
                    apply (rule x_nat)
                    apply (rule ya_leq_sx)
                    done
                  have H2: "P(ya) \<le> x \<doteq> 1"
                    apply (rule eqSubst[where a="P S x" and b="x"])
                    apply (gd_auto)
                    apply (rule x_nat)
                    apply (rule H)
                    done
                  have H3: "P(xa) \<le> P(ya) \<doteq> 1"
                    apply (rule leq_monotone_pred)
                    apply (rule xa_nat)
                    apply (rule ya_nat)
                    apply (rule xa_leq_ya)
                    done
                  have H4: "P xa \<le> P ya \<doteq> 1 \<turnstile> P ya \<le> x \<doteq> 1 \<turnstile> P xa \<le> x \<doteq> 1"
                    apply (rule forallE[where a="P ya"])
                    apply (rule forallE[where a="P xa"])
                    apply (rule hyp)
                    apply (gd_auto)
                    apply (rule xa_nat)
                    apply (gd_auto)
                    apply (rule ya_nat)
                    done
                  then have H5: "P ya \<le> x \<doteq> 1 \<turnstile> P xa \<le> x \<doteq> 1"
                    apply (rule entailsE)
                    apply (rule H3)
                    done
                  then show "P xa \<le> x \<doteq> 1"
                    apply (rule entailsE)
                    apply (rule H2)
                    done
                qed
           qed
        qed
     qed
  qed
  then have "\<forall>y. (x \<le> y \<doteq> 1) \<turnstile> (y \<le> z \<doteq> 1) \<turnstile> (x \<le> z \<doteq> 1)"
    apply (rule forallE)
    apply (rule x_nat)
    done
  then have "(x \<le> y \<doteq> 1) \<turnstile> (y \<le> z \<doteq> 1) \<turnstile> (x \<le> z \<doteq> 1)"
    apply (rule forallE)
    apply (rule y_nat)
    done
  then have "(y \<le> z \<doteq> 1) \<turnstile> (x \<le> z \<doteq> 1)"
    apply (rule entailsE)
    apply (rule x_leq_y)
    done
  then show ?thesis
    apply (rule entailsE)
    apply (rule y_leq_z)
    done
qed

lemma less_terminates [gd_simp]:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "x < y N"
proof -
  have q: "\<forall>x. x < y N"
  proof (rule ind[where a="y"])
    show "y N" by (rule y_nat)
    show "\<forall>x. x < 0 N"
      apply (rule forallI)
      proof -
        fix x
        assume x_nat: "x N"
        show "x < 0 N"
          apply (rule eqSubst[where a="0" and b="x < 0"])
          apply (rule eqSym)
          apply (gd_auto)
          done
      qed
    show "\<forall>x. (\<forall>xa. xa < x N) \<turnstile> (\<forall>xa. xa < S x N)"
      apply (rule forallI)
      apply (rule entailsI)
      apply (rule forallI)
      proof -
        fix x y
        assume x_nat: "x N"
        assume hyp: "\<forall>xa. xa < x N"
        assume y_nat: "y N"
        show "y < S x N"
          apply (unfold_def def_less)
          apply (rule condT)
          apply (rule eqBool)
          apply (rule natS)
          apply (rule x_nat)
          apply (rule nat0)
          apply (rule nat0)
          apply (rule condT)
          apply (rule eqBool)
          apply (rule y_nat)
          apply (gd_auto)
          apply (rule eqSubst[where a="x" and b="P S x"])
          apply (rule eqSym)
          apply (gd_auto)
          apply (rule x_nat)
          apply (rule forallE[where a="P y"])
          apply (rule hyp)
          apply (gd_auto)
          apply (rule y_nat)
          done
      qed
  qed
  show ?thesis
    apply (rule forallE[where a="x"])
    apply (rule q)
    apply (rule x_nat)
    done
qed

lemma zero_less_true [gd_simp]:
  assumes a_nat: "a N"
  shows "0 < S(a) \<doteq> 1"
apply (unfold_def def_less)
apply (rule condI2Eq)
apply (fold neq_def)
apply (gd_auto)
apply (rule a_nat)
apply (gd_auto)
apply (rule condI1)
apply (gd_auto)
done

lemma sub_0 [gd_simp]:
  assumes x_nat: "x N"
  shows "x - 0 \<doteq> x"
apply (unfold_def def_sub)
apply (gd_auto)
apply (rule condI1)
apply (gd_auto)
apply (rule x_nat)
done

lemma zero_div [gd_simp]:
  assumes x_nat: "x N"
  shows "div 0 S(x) \<doteq> 0"
apply (unfold_def def_div)
apply (gd_auto)
apply (rule condI1)
apply (gd_auto)
apply (rule x_nat)
apply (gd_auto)
done

lemma div_1 [gd_simp]:
  assumes x_nat: "x N"
  shows "div x 1 \<doteq> x"
proof (rule ind)
  show "x N" by (rule x_nat)
  show "div 0 1 \<doteq> 0"
    apply (unfold_def def_div)
    apply (gd_auto)
    apply (rule condI1)
    apply (gd_auto)
    done
  show "\<forall>x.(div x 1 \<doteq> x) \<turnstile> (div S(x) 1 \<doteq> S(x))"
  proof (rule forallI, rule entailsI)
    fix xa
    assume xa_nat: "xa N"
    assume ind_h: "div xa 1 \<doteq> xa"
    show "div S(xa) 1 \<doteq> S(xa)"
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
      apply (rule condI2)
      apply (fold neq_def)
      apply (gd_auto)
      apply (rule xa_nat)
      apply (rule eqSym)
      apply (rule ind_h)
      apply (rule condI2)
      apply (rule eqSubst[where a="0" and b="S xa < 1"])
      apply (rule eqSym)
      apply (unfold_def def_less)
      apply (rule eqSubst[where a="xa" and b="P(S(xa))"])
      apply (rule eqSym)
      apply (gd_auto)
      apply (rule xa_nat)
      apply (rule condI2Eq)
      apply (fold neq_def)
      apply (gd_auto)
      apply (rule condI2Eq)
      apply (fold neq_def)
      apply (gd_auto)
      apply (rule xa_nat)
      apply (gd_auto)
      apply (rule eqSubst[where a="0" and b="P(S(0))"])
      apply (rule eqSym)
      apply (gd_auto)
      apply (rule xa_nat)
      done
  qed
qed

lemma x_leq_0_then_x_0:
  assumes x_nat: "x N"
  assumes x_leq_0: "x \<le> 0 \<doteq> 1"
  shows "x \<doteq> 0"
apply (rule grounded_contradiction[where q="x \<le> 0 \<doteq> 1"])
apply (rule eqBool)
apply (rule x_nat)
apply (rule nat0)
apply (rule x_leq_0)
apply (rule eqSubst[where a="0" and b="x \<le> 0"])
apply (rule eqSym)
apply (unfold_def def_leq)
apply (rule condI2Eq)
apply (assumption)
apply (rule nat0)
apply (rule condI1)
apply (rule zeroRefl)
apply (rule nat0)
apply (fold neq_def)
apply (gd_auto)
done

lemma neq_monotone_pred:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes x_nz: "\<not> x \<doteq> 0"
  assumes y_nz: "\<not> y \<doteq> 0"
  assumes x_neq_y: "\<not> x \<doteq> y"
  shows "\<not> P x \<doteq> P y"
proof (rule GD.grounded_contradiction[where q="x \<doteq> y"])
  show "\<not> P x \<doteq> P y B" by (gd_auto, rule x_nat, rule y_nat)
  show "\<not>\<not> P x \<doteq> P y \<Longrightarrow> x \<doteq> y"
    proof -
      assume H: "\<not> \<not> P x \<doteq> P y"
      then have H2: "P x \<doteq> P y"
        by (rule dNegE)
      then have H3: "S P x \<doteq> S P y"
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
  show "\<not>\<not> P x \<doteq> P y \<Longrightarrow> \<not> x \<doteq> y" by (rule x_neq_y)
qed

lemma less_is_leq_neq:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes x_leq_y: "x \<le> y \<doteq> 1"
  assumes x_neq_y: "\<not> x \<doteq> y"
  shows "x < y \<doteq> 1"
proof -
  have "\<forall>x. x \<le> y \<doteq> 1 \<turnstile> \<not> x \<doteq> y \<turnstile> x < y \<doteq> 1"
  proof (rule ind[where a="y"])
    show "y N" by (rule y_nat)
    show "\<forall>x. x \<le> 0 \<doteq> 1 \<turnstile> \<not> x \<doteq> 0 \<turnstile> x < 0 \<doteq> 1"
      apply (rule forallI)
      apply (rule entailsI)
      apply (rule entailsI)
      proof -
        fix x
        assume x_nat: "x N"
        assume x_leq_0: "x \<le> 0 \<doteq> 1"
        assume x_nz: "\<not> x \<doteq> 0"
        show "x < 0 \<doteq> 1"
          apply (rule exF[where P="x \<doteq> 0"])
          apply (rule x_leq_0_then_x_0)
          apply (rule x_nat)
          apply (rule x_leq_0)
          apply (rule x_nz)
          done
      qed
    show "\<forall>x. (\<forall>xa. xa \<le> x \<doteq> 1 \<turnstile> \<not> xa \<doteq> x \<turnstile> xa < x \<doteq> 1) \<turnstile>
     (\<forall>xa. xa \<le> S x \<doteq> 1 \<turnstile> \<not> xa \<doteq> S x \<turnstile> xa < S x \<doteq> 1)"
      apply (rule forallI)
      apply (rule entailsI)
      apply (rule forallI)
      apply (rule entailsI)
      apply (rule entailsI)
      proof -
        fix x xa
        assume x_nat: "x N"
        assume xa_nat: "xa N"
        assume hyp: "\<forall>xa. xa \<le> x \<doteq> 1 \<turnstile> \<not> xa \<doteq> x \<turnstile> xa < x \<doteq> 1"
        assume xa_leq_sx: "xa \<le> S x \<doteq> 1"
        assume xa_neq_sx: "\<not> xa \<doteq> S x"
        have H: "P xa \<le> P S x \<doteq> 1"
          by (rule leq_monotone_pred, rule xa_nat, rule natS, rule x_nat, rule xa_leq_sx)
        have p_xa_leq_x: "P xa \<le> x \<doteq> 1"
          by (rule eqSubst[where a="P S x" and b="x"], gd_auto, rule x_nat, rule H)
        show "xa < S x \<doteq> 1 "
          apply (unfold_def def_less)
          apply (rule condI2Eq)
          apply (fold neq_def)
          apply (gd_auto)
          apply (rule x_nat)
          apply (gd_auto)
          apply (rule cases_nat[where x="xa"])
          apply (rule xa_nat)
          apply (rule condI1)
          apply (rule zeroRefl)
          apply (gd_auto)
          apply (rule condI2Eq)
          apply (assumption)
          apply (gd_auto)
          apply (rule eqSubst[where a="x" and b="P S x"])
          apply (rule eqSym)
          apply (gd_auto)
          apply (rule x_nat)
          proof -
            assume xa_nz: "\<not> xa \<doteq> 0"
            have H2: "\<not> P xa \<doteq> P S x"
              apply (rule neq_monotone_pred)
              apply (rule xa_nat)
              apply (rule natS)
              apply (rule x_nat)
              apply (rule xa_nz)
              apply (fold neq_def)
              apply (gd_auto)
              apply (rule x_nat)
              apply (unfold neq_def)
              apply (rule xa_neq_sx)
              done
            have pxa_neq_x: "\<not> P xa \<doteq> x"
              apply (rule eqSubst[where a="P S x" and b="x"])
              apply (rule predSucSym)
              apply (rule x_nat)
              apply (rule H2)
              done
            have "P xa \<le> x \<doteq> 1 \<turnstile> \<not> P xa \<doteq> x \<turnstile> P xa < x \<doteq> 1"
              apply (rule forallE[where a="P xa"])
              apply (rule hyp)
              apply (rule natP)
              apply (rule xa_nat)
              done
            then have "\<not> P xa \<doteq> x \<turnstile> P xa < x \<doteq> 1"
              apply (rule entailsE)
              apply (rule p_xa_leq_x)
              done
            then show "P xa < x \<doteq> 1"
              apply (rule entailsE)
              apply (rule pxa_neq_x)
              done
        qed
      qed
  qed
  then have "x \<le> y \<doteq> 1 \<turnstile> \<not> x \<doteq> y \<turnstile> x < y \<doteq> 1"
    apply (rule forallE)
    apply (rule x_nat)
    done
  then have "\<not> x \<doteq> y \<turnstile> x < y \<doteq> 1"
    apply (rule entailsE)
    apply (rule x_leq_y)
    done
  then show "x < y \<doteq> 1"
    apply (rule entailsE)
    apply (rule x_neq_y)
    done
qed

lemma x_less_1_is_0:
  assumes x_nat: "x N"
  assumes H: "x < 1 \<doteq> 1"
  shows "x \<doteq> 0"
proof (rule grounded_contradiction[where q="x < 1 \<doteq> 0"])
  show "x \<doteq> 0 B"
    by (rule eqBool, rule x_nat, gd_auto)
  show "\<not> x \<doteq> 0 \<Longrightarrow> x < 1 \<doteq> 0"
    apply (unfold_def def_less)
    apply (rule condI2Eq)
    apply (fold neq_def)
    apply (gd_auto)
    apply (rule condI2Eq)
    apply (unfold neq_def)
    apply (gd_auto)
    apply (rule eqSubst[where a="0" and b="P S 0"])
    apply (rule eqSym)
    apply (gd_auto)
    done
  show "\<not> x \<doteq> 0 \<Longrightarrow> \<not> x < 1 \<doteq> 0"
      apply (rule eqSubst[where a="1" and b="x < 1"])
      apply (rule eqSym)
      apply (rule H)
      apply (fold neq_def)
      apply (gd_auto)
      done
qed

lemma le_monotone_suc:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes x_le_y: "x < y \<doteq> 1"
  shows "S x < S y \<doteq> 1"
apply (unfold_def def_less)
apply (rule condI2Eq)
apply (fold neq_def)
apply (gd_auto)
apply (rule y_nat)
apply (gd_auto)
apply (rule condI2Eq)
apply (fold neq_def)
apply (gd_auto)
apply (rule x_nat)
apply (gd_auto)
apply (rule eqSubst[where a="x" and b="P(S(x))"])
apply (rule eqSym)
apply (gd_auto)
apply (rule x_nat)
apply (rule eqSubst[where a="y" and b="P(S(y))"])
apply (rule eqSym)
apply (gd_auto)
apply (rule y_nat)
apply (rule x_le_y)
done

lemma le_monotone_pred:
  assumes x_nat: "x N"
  assumes x_nz: "\<not> x \<doteq> 0"
  assumes y_nat: "y N"
  assumes x_le_y: "x < y \<doteq> 1"
  shows "P x < P y \<doteq> 1"
apply (rule grounded_contradiction[where q="x < y \<doteq> 1"])
apply (gd_auto)
apply (rule x_nat)
apply (rule y_nat)
apply (rule x_le_y)
apply (unfold_def def_less)
apply (rule cases_nat[where x="y"])
apply (rule y_nat)
apply (rule eqSubst[where a="0" and b="(if 0 \<doteq> 0 then 0 else
  if x \<doteq> 0 then 1 else (P x < P 0))"])
apply (rule eqSym)
apply (rule condI1)
apply (gd_auto)
apply (fold neq_def)
apply (gd_auto)
apply (rule eqSubst[where a="P x < P y" and b="(if y \<doteq> 0 then 0 else if
  x \<doteq> 0 then 1 else P x < P y)"])
apply (rule eqSym)
apply (rule condI2Eq)
apply (unfold neq_def)
apply (assumption)
apply (rule less_terminates)
apply (gd_auto)
apply (rule x_nat)
apply (gd_auto)
apply (rule y_nat)
apply (rule condI2Eq)
apply (rule x_nz)
apply (rule less_terminates)
apply (gd_auto)
apply (rule x_nat)
apply (gd_auto)
apply (rule y_nat)
apply (fold isNat_def)
apply (rule less_terminates)
apply (gd_auto)
apply (rule x_nat)
apply (gd_auto)
apply (rule y_nat)
apply (assumption)
done

lemma le_suc_implies_leq:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes x_le_sy: "x < S y \<doteq> 1"
  shows "x \<le> y \<doteq> 1"
proof -
  have "\<forall>x. x < S y \<doteq> 1 \<turnstile> x \<le> y \<doteq> 1"
  proof (rule ind[where a="y"])
    show "y N" by (rule y_nat)
    show "\<forall>x. x < 1 \<doteq> 1 \<turnstile> x \<le> 0 \<doteq> 1"
      apply (rule forallI)
      apply (rule entailsI)
      proof -
        fix x
        assume x_nat: "x N"
        assume x_le_sy: "x < 1 \<doteq> 1"
        show "x \<le> 0 \<doteq> 1"
          apply (unfold_def def_leq)
          apply (rule condI1)
          apply (rule GD.x_less_1_is_0)
          apply (rule x_nat)
          apply (rule x_le_sy)
          apply (gd_auto)
          done
      qed
    show "\<forall>x. (\<forall>xa. xa < S x \<doteq> 1 \<turnstile> xa \<le> x \<doteq> 1) \<turnstile>
     (\<forall>xa. xa < S S x \<doteq> 1 \<turnstile> xa \<le> S x \<doteq> 1)"
      apply (rule forallI)
      apply (rule entailsI)
      apply (rule forallI)
      apply (rule entailsI)
      proof -
        fix x xa
        assume x_nat: "x N"
        assume xa_nat: "xa N"
        assume hyp: "\<forall>xa. xa < S x \<doteq> 1 \<turnstile> xa \<le> x \<doteq> 1"
        have hyp_inst: "P xa < S x \<doteq> 1 \<turnstile> P xa \<le> x \<doteq> 1"
          apply (rule forallE[where a="P xa"])
          apply (rule hyp)
          apply (gd_auto)
          apply (rule xa_nat)
          done
        assume xa_le_ssx: "xa < S S x \<doteq> 1"
        show "xa \<le> S x \<doteq> 1"
          apply (unfold_def def_leq)
          apply (rule cases_nat[where x="xa"])
          apply (rule xa_nat)
          apply (rule condI1)
          apply (gd_auto)
          apply (rule condI2Eq)
          apply (assumption)
          apply (gd_auto)
          apply (rule condI2Eq)
          apply (fold neq_def)
          apply (gd_auto)
          apply (rule x_nat)
          apply (gd_auto)
          apply (rule eqSubst[where a="x" and b="P S x"])
          apply (rule eqSym)
          apply (gd_auto)
          apply (rule x_nat)
          apply (rule entailsE[where a="P xa < S x \<doteq> 1"])
          apply (rule hyp_inst)
          apply (rule eqSubst[where a="P S S x" and b = "S x"])
          apply (gd_auto)
          apply (rule x_nat)
          apply (rule le_monotone_pred)
          apply (rule xa_nat)
          apply (fold neq_def)
          apply (gd_auto)
          apply (rule x_nat)
          apply (rule xa_le_ssx)
          done
      qed
  qed
  then have "x < S y \<doteq> 1 \<turnstile> x \<le> y \<doteq> 1"
    apply (rule forallE)
    apply (rule x_nat)
    done
  then show ?thesis
    apply (rule entailsE)
    apply (rule x_le_sy)
    done
qed

lemma leq_suc_not_leq_implies_eq:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes x_ge_y: "\<not> x \<le> y \<doteq> 1"
  assumes x_le_sy: "x \<le> S y \<doteq> 1"
  shows "x \<doteq> S y"
proof (rule contradiction)
  show "x \<doteq> S(y) B" by (rule eqBool, rule x_nat, rule natS, rule y_nat)
  show "\<not> x \<doteq> S(y) \<Longrightarrow> False"
    proof -
      assume x_neq_sy: "\<not> x \<doteq> S y"
      have H: "x < S y \<doteq> 1"
        apply (rule less_is_leq_neq)
        apply (rule x_nat)
        apply (rule natS)
        apply (rule y_nat)
        apply (rule x_le_sy)
        apply (rule x_neq_sy)
        done
      have H4: "x \<le> y \<doteq> 1" by (rule le_suc_implies_leq, rule x_nat, rule y_nat, rule H)
      show "False"
        apply (rule exF[where P="x \<le> y \<doteq> 1"])
        apply (rule H4)
        apply (rule x_ge_y)
        done
    qed
qed

lemma strong_induction:
  assumes a_nat: "a N"
  assumes bc: "Q 0"
  assumes step: "\<forall>x.((\<forall>y. y\<le>x \<doteq> 1 \<turnstile> Q y) \<turnstile> (Q S(x)))"
  shows "Q a"
proof -
  have q: "\<forall>x. (x \<le> a \<doteq> 1) \<turnstile> Q x"
    proof (rule ind[where a="a"])
      show "a N" by (rule a_nat)
      show "\<forall>x. x \<le> 0 \<doteq> 1 \<turnstile> Q x"
        apply (rule forallI)
        apply (rule entailsI)
        proof -
          fix x
          assume x_nat: "x N"
          assume x_le_0: "x \<le> 0 \<doteq> 1"
          have x_zero: "x \<doteq> 0"
            apply (rule GD.x_leq_0_then_x_0)
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
      show "\<forall>x. (\<forall>xa. xa \<le> x \<doteq> 1 \<turnstile> Q xa) \<turnstile> (\<forall>xa. xa \<le> S x \<doteq> 1 \<turnstile> Q xa)"
        apply (rule forallI)
        apply (rule entailsI)
        apply (rule forallI)
        apply (rule entailsI)
        proof -
          fix x xa
          assume x_nat: "x N"
          assume xa_nat: "xa N"
          assume hyp: "\<forall>x'. x' \<le> x \<doteq> 1 \<turnstile> Q x'"
          assume xa_leq_sx: "xa \<le> S x \<doteq> 1"
          have H: "xa \<le> x \<doteq> 1 \<turnstile> Q xa"
            apply (rule forallE[where a="xa"])
            apply (rule hyp)
            apply (rule xa_nat)
            done
          show "Q xa"
            apply (rule disjE1[where P="xa \<le> x \<doteq> 1" and Q="\<not> xa \<le> x \<doteq> 1"])
            apply (fold GD.bJudg_def)
            apply (rule eqBool)
            apply (rule leq_terminates)
            apply (rule xa_nat)
            apply (rule x_nat)
            apply (gd_auto)
            apply (rule entailsE[where a="xa \<le> x \<doteq> 1"])
            apply (rule H)
            apply (assumption)
            proof -
              assume xa_not_leq_x: "\<not> xa \<le> x \<doteq> 1"
              have xa_eq_sx: "xa \<doteq> S x"
                apply (rule leq_suc_not_leq_implies_eq)
                apply (rule xa_nat)
                apply (rule x_nat)
                apply (rule xa_not_leq_x)
                apply (rule xa_leq_sx)
                done
              have "(\<forall>y. y\<le>x \<doteq> 1 \<turnstile> Q y) \<turnstile> (Q S(x))"
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
    then have "a \<le> a \<doteq> 1 \<turnstile> Q a"
      apply (rule forallE)
      apply (rule a_nat)
      done
    then show ?thesis
      apply (rule entailsE)
      apply (rule leq_refl)
      apply (rule a_nat)
      done
qed

lemma sub_terminates [gd_simp]:
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
      show "if (S(a) \<doteq> 0) then x else P(x - P(S(a))) N"
        proof (rule GD.condT)
          show "S(a) \<doteq> 0 B"
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
            apply (rule predSucSym)
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
  shows "(S x) - (S y) \<le> x \<doteq> 1"
proof -
  have "\<forall>x. (S x) - (S y) \<le> x \<doteq> 1"
  proof (rule ind[where a="y"])
    show "y N" by (rule y_nat)
    show "\<forall>x. S x - 1 \<le> x \<doteq> 1"
      apply (rule forallI)
      proof -
        fix x
        assume x_nat: "x N"
        show "S x - 1 \<le> x \<doteq> 1"
          apply (rule eqSubst[where a="x" and b="S x - 1"])
          apply (rule eqSym)
          apply (unfold_def def_sub)
          apply (rule condI2Eq)
          apply (fold neq_def)
          apply (gd_auto)
          apply (rule x_nat)
          apply (rule eqSubst[where a="0" and b="P S 0"])
          apply (rule eqSym)
          apply (gd_auto)
          apply (rule eqSubst[where a="S x" and b="S x - 0"])
          apply (rule eqSym)
          apply (gd_auto)
          apply (rule x_nat)
          apply (gd_auto)
          apply (rule x_nat)
          apply (gd_auto)
          apply (rule x_nat)
          done
      qed
    show "\<forall>x. (\<forall>xa. S xa - S x \<le> xa \<doteq> 1) \<turnstile> (\<forall>xa. S xa - S S x \<le> xa \<doteq> 1)"
      apply (rule forallI)
      apply (rule entailsI)
      apply (rule forallI)
      proof -
        fix x xa
        assume x_nat: "x N" and xa_nat: "xa N"
        assume hyp: "\<forall>xa. S xa - S x \<le> xa \<doteq> 1"
        then have H: "S xa - S x \<le> xa \<doteq> 1"
          apply (rule forallE)
          apply (rule xa_nat)
          done
        have H2: "P(S xa - S x) \<le> xa \<doteq> 1"
          apply (rule leq_trans[where y="S xa - S x"])
          apply (gd_auto)
          apply (rule xa_nat)
          apply (rule x_nat)
          apply (gd_auto)
          apply (rule xa_nat)
          apply (rule x_nat)
          apply (rule xa_nat)
          apply (gd_auto)
          apply (rule xa_nat)
          apply (rule x_nat)
          apply (rule H)
          done
        show "S xa - S S x \<le> xa \<doteq> 1"
          apply (unfold_def def_sub)
          apply (rule eqSubst[where a="P(S xa - S x)" and b="(if S S x \<doteq> num_zero then S xa else P(S xa - P S S x))"])
          apply (rule eqSym)
          apply (rule condI2Eq)
          apply (fold neq_def)
          apply (gd_auto)
          apply (rule x_nat)
          apply (gd_auto)
          apply (rule xa_nat)
          apply (rule x_nat)
          apply (rule eqSubst[where a="S x" and b="P S S x"])
          apply (rule eqSym)
          apply (gd_auto)
          apply (rule x_nat)
          apply (fold isNat_def)
          apply (gd_auto)
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

lemma div_terminates [gd_simp]:
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
    apply (gd_auto)
    apply (rule y_nat)
    apply (gd_auto)
    done
  show "\<forall>x. (\<forall>ya. ya \<le> x \<doteq> 1 \<turnstile> div ya (S y) N) \<turnstile> div (S x) (S y) N "
    apply (rule forallI)
    apply (rule entailsI)
    proof -
      fix x
      assume x_nat: "x N"
      assume hyp: "\<forall>ya. ya \<le> x \<doteq> 1 \<turnstile> div ya (S y) N"
      then have "S x - S y \<le> x \<doteq> 1 \<turnstile> div (S x - S y) (S y) N"
        apply (rule forallE)
        apply (rule sub_terminates)
        apply (gd_auto)
        apply (rule x_nat)
        apply (gd_auto)
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
        apply (gd_auto)
        apply (rule x_nat)
        apply (rule y_nat)
        apply (gd_auto)
        apply (rule H2)
        done
    qed
qed

lemma cpair_terminates [gd_simp]:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "\<langle>x, y\<rangle> N"
apply (unfold cpair_def)
apply (gd_auto)
apply (rule y_nat)
apply (rule x_nat)
apply (rule y_nat)
apply (rule x_nat)
apply (rule y_nat)
done

ML_file "gd_typeencode.ML"

subsection "User-level Equality"

text "We define a user-level equality, which doesn't know about
  the underlying \<open>num\<close> representation.
  For the following manually constructed inductive datatype, it cannot
  be proven for example that \<open>Nil = 0\<close> or \<open>Nil \<doteq> 0\<close>, even though Cons is
  actually represented by 0. The type_synonym types are opaque."

axiomatization
  eq :: "'a \<Rightarrow> 'a \<Rightarrow> o" (infix "=" 20)
where
  refl: "a = a" and
  eq_comm: "a = b \<Longrightarrow> b = a" and
  eq_subst: "\<lbrakk>a = b; Q b\<rbrakk> \<Longrightarrow> Q a"

text "A manual construction of an inductive datatype.
  Later, we want this to be generated automatically from something
  like \<open>declaretype List = Nil | Cons of \<open>nat\<close> \<open>List\<close>\<close>."

(* First approach:
 * A new inductive type is an actual syntactic type unequal to our nums.
 * You can do type-checking! A function that expects a list gets a syn-
 * tactic list!
 * We then need a new 'userland' equality that is different from the
 * num equality we have (since that is not defined for types other
 * than num).
 * The representation into num stems from an encoding function num \<Rightarrow> type
 * and decoding function type \<Rightarrow> num. It is however unclear what exactly
 * we do with this.
 * The problem is that we require tons of axiomatization about the new
 * type. We axiomatize that the constructors are different and injective.
 * We cannot reuse the (if _ then _ else _), since that is grounded
 * and requires proving that something is N (i.e. equal to itself with
 * respect to num-level equality), which is not possible if what you
 * return is of a different type.
 *)

(*
typedecl List

consts
  Nil :: "List"
  Cons :: "num \<Rightarrow> List \<Rightarrow> List"
  list_encode :: "List \<Rightarrow> num"
  list_decode :: "num \<Rightarrow> List"
  is_list :: "num \<Rightarrow> num"

axiomatization
where
  const_distinct: "\<not> ((Cons a x) = Nil)" and
  list_injective: "(Cons a x) = (Cons b y) \<Longrightarrow> a \<doteq> b \<and> (x = y)" and
  list_encode:  "list_encode := (\<lambda>x.
                             if (x = Nil) then \<langle>0,0\<rangle>
                             else if (x = (Cons n xs)) then \<langle>0,1,n,list_encode xs\<rangle>
                             else omega)" and
  list_decode: "list_decode := (\<lambda>x.
                             if (x \<doteq> \<langle>0,0\<rangle>) then Nil
                             else if (x \<doteq> \<langle>0,1,n,z'\<rangle>) then Cons n (list_decode z')
                             else omega)"

lemma zero_is_cons: "list_encode Nil \<doteq> 0"
apply (unfold_def list_encode)
apply (rule condI1Eq)
apply (rule refl)
apply (rule nat0)
apply (unfold cpair_def)
apply (unfold_def def_div)
sorry

lemma list_encode_nil: "list_encode Nil \<doteq> \<langle>0, 0\<rangle>"
apply (unfold_def list_encode)
apply (rule condI1)
apply (rule refl)
done

lemma list_encode_cons:  "list_encode (Cons n xs) \<doteq> \<langle>0, 1, n, list_encode xs\<rangle>"
apply (unfold_def list_encode)
apply (rule condI2Eq)
apply (rule const_distinct)
sorry
lemma list_decode_nil: "(list_decode \<langle>0, 0\<rangle>) = Nil"
sorry
lemma list_decode_cons: "list_decode \<langle>0, 1, n, z'\<rangle> = Cons n (list_decode z')"
sorry

lemma list_induction: "\<lbrakk>Q Nil; \<forall>n xs. n N \<turnstile> Q (list_decode xs) \<turnstile> Q (Cons n (list_decode xs))\<rbrakk> \<Longrightarrow> Q l"
sorry
lemma encode_decode_correct: "list_encode x N \<Longrightarrow> list_decode (list_encode x) = x"
sorry
lemma decode_encode_correct: "list_decode (list_encode x) = x"
sorry

*)

(* What the declaretype compiler should compile: *)
type_synonym List = num

definition list_type_tag where
  "list_type_tag \<equiv> 0"

definition Nil :: "List" where
  "Nil \<equiv> \<langle>list_type_tag,0\<rangle>"

definition Cons :: "num \<Rightarrow> List \<Rightarrow> List" where
  "Cons n xs \<equiv> \<langle>list_type_tag,1,n,xs\<rangle>"

consts
  is_list :: "num \<Rightarrow> o"

axiomatization
where
  is_list_def: "is_list := (\<lambda>x.
                              if x \<doteq> Nil then True
                              else if ((x \<doteq> Cons n xs) \<and> (is_list xs)) then True
                              else False
                              )"

lemma "is_list Nil"
sorry
lemma "is_list xs \<Longrightarrow> is_list (Cons n xs)"
sorry
lemma "is_list xs \<Longrightarrow> xs N"
sorry
lemma "is_list x \<Longrightarrow> (x \<doteq> Nil) \<or> (\<exists>n. \<exists> xs. x \<doteq> Cons n xs)"
sorry
lemma "Cons n xs \<doteq> Cons m ys \<Longrightarrow> n \<doteq> m \<and> xs \<doteq> ys"
sorry
lemma "Cons n xs \<noteq> Nil"
sorry
lemma list_induction:
  assumes "is_list a"
  assumes "Q Nil"
  assumes "\<forall>x xs. x N \<turnstile> is_list xs \<turnstile> Q xs \<turnstile> Q (Cons x xs)"
  shows "Q a"
sorry

lemma "is_list (Cons 4 (Cons 2 (Nil)))"
sorry

(*
declaretype num =
  Zero
  | Suc of "num"

declaretype list =
  nil
  | cons of "num" "list"
*)

end (* End of theory *)
