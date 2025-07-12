(* Title: pure/GD.thy
*)

section \<open>Grounded deduction logic\<close>

theory GD
  imports Pure
begin

text \<open>The following theory development formalizes the Grounded Deduction Logic.\<close>

(*
syntax
  "_turnstile" :: "prop \<Rightarrow> prop \<Rightarrow> prop"  (infixr "\<turnstile>" 1)
translations
  "_turnstile a b" \<rightleftharpoons> "a \<Longrightarrow> b"
*)

section \<open>Axiomatization of truth in GD\<close>

typedecl o

judgment
  Trueprop :: \<open>o \<Rightarrow> prop\<close>  (\<open>_\<close> 5)

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

  dNegI: \<open>P \<Longrightarrow> \<not>\<not>P\<close> and
  dNegE: \<open>\<not>\<not>P \<Longrightarrow> P\<close> and
  exF: \<open>\<lbrakk>P; \<not>P\<rbrakk> \<Longrightarrow> Q\<close>

section \<open>Axiomatization of equality in GD\<close>

typedecl nat

axiomatization
  eq :: \<open>['a, 'a] \<Rightarrow> o\<close>  (infixl \<open>=\<close> 50)
where
  eqRefl: \<open>a = a\<close> and
  eqSubst: \<open>\<lbrakk>a = b; Q a\<rbrakk> \<Longrightarrow> Q b\<close> and
  eqSym: \<open>a = b \<Longrightarrow> b = a\<close>

definition neq (infixl \<open>\<noteq>\<close> 50)
  where \<open>a \<noteq> b \<equiv> \<not> (a = b)\<close>

section \<open>Axiomatization of naturals in GD\<close>

axiomatization
  zero :: \<open>nat\<close>           (\<open>0\<close>) and
  suc :: \<open>nat \<Rightarrow> nat\<close>     (\<open>S(_)\<close> [800]) and
  pred :: \<open>nat \<Rightarrow> nat\<close>     (\<open>P(_)\<close> [800])
where
  sucInj: \<open>S a = S b \<Longrightarrow> a = b\<close>

definition True
  where \<open>True \<equiv> 0 = 0\<close>
definition False
  where \<open>False \<equiv> S(0) = 0\<close>
definition bJudg (\<open>_ B\<close>)
  where \<open>p B \<equiv> p \<or> \<not>p\<close>
definition conj (infixl \<open>\<and>\<close> 35)
  where \<open>p \<and> q \<equiv> \<not>(\<not>p \<or> \<not>q)\<close>
definition impl (infixl \<open>\<longrightarrow>\<close> 25)
  where \<open>p \<longrightarrow> q \<equiv> \<not>p \<or> q\<close>

axiomatization
  isNat :: \<open>nat \<Rightarrow> o\<close> (\<open>_ N\<close> [50] 50)
where
  nat0: \<open>0 N\<close> and
  natS: \<open>n N \<Longrightarrow> S n N\<close> and
  natP: \<open>n N \<Longrightarrow> P n N\<close> and
  eqT: \<open>\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow> (a = b) B\<close> and
  sucNonZero: \<open>a N \<Longrightarrow> S a \<noteq> 0\<close> and
  predSucSym: \<open>a N \<Longrightarrow> P(S(a)) = a\<close> and
  ind: \<open>\<lbrakk>a N; Q 0; \<And>x. x N \<Longrightarrow> Q x \<Longrightarrow> Q (S(x))\<rbrakk> \<Longrightarrow> Q a\<close>

section \<open>Axiomatization of conditional evaluation in GD\<close>

consts
  cond :: \<open>o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
syntax
  "_cond" :: \<open>o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (\<open>_ ? _ : _\<close> [1000, 1000, 1000] 1000)
translations
  "c ? a : b" \<rightleftharpoons> "CONST cond c a b"

axiomatization
where
  condI1: \<open>\<lbrakk>c; a N\<rbrakk> \<Longrightarrow> c ? a : b = a\<close> and
  condI2: \<open>\<lbrakk>\<not>c; b N\<rbrakk> \<Longrightarrow> c ? a : b = b\<close> and
  condT: \<open>\<lbrakk>c B; a N; b N\<rbrakk> \<Longrightarrow> (c ? a : b) N\<close> and
  condI1B: \<open>\<lbrakk>c; d B\<rbrakk> \<Longrightarrow> c ? d : e = d\<close> and
  condI2B: \<open>\<lbrakk>\<not>c; e B\<rbrakk> \<Longrightarrow> c ? d : e = e\<close> and
  condTB: \<open>\<lbrakk>c B; d B; e B\<rbrakk> \<Longrightarrow> (c ? d : e) B\<close>

section \<open>Definitional Mechanism in GD\<close>

axiomatization
  def :: \<open>'a \<Rightarrow> 'a \<Rightarrow> o\<close> (\<open>_:=_\<close>)
where
  defU: \<open>\<lbrakk>a := b; Q b\<rbrakk> \<Longrightarrow> Q a\<close>

ML_file \<open>unfold_def.ML\<close>

print_methods

section \<open>Deductions of non-elementary inference rules.\<close>

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

lemma not_false: "\<not>False"
proof (unfold False_def)
  show "\<not>(S(0) = 0)"
  proof -
    have "S(0) \<noteq> 0" by (rule sucNonZero) (rule nat0)
    then show ?thesis by (unfold neq_def)
  qed
qed

lemma false_bool: "False B"
proof (unfold GD.bJudg_def)
  show "False \<or> \<not>False"
  proof -
    have "\<not>False" by (rule not_false)
    then show ?thesis by (rule disjI2[where Q="\<not>False" and P="False"])
  qed
qed

lemma disj_sym:
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

theorem GD_consistent: "\<And>Q. \<not>(Q \<and> \<not>Q)"
(* Can't use grounded contradiction, because that requires proving that
 * Q (i.e. any proposition) is boolean, that is, either true or false.
 * Which is certainly not provable.
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
  add :: "nat \<Rightarrow> nat \<Rightarrow> nat"     (\<open>_+_\<close>) and
  sub :: "nat \<Rightarrow> nat \<Rightarrow> nat"     (\<open>_-_\<close>) and
  mult :: "nat \<Rightarrow> nat \<Rightarrow> nat"    (\<open>_*_\<close>) and
  less :: "nat \<Rightarrow> nat \<Rightarrow> o"      (\<open>_<_\<close>) and
  div :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  def_add: "add := (\<lambda>x y. (y = 0) ? x : S(add x P(y)))" and
  def_sub: "sub := (\<lambda>x y. (y = 0) ? x : P(sub x P(y)))" and
  def_mult: "mult := (\<lambda>x y. (y = 0) ? 0 : (x + (mult x P(y))))" and
  def_less: "less := (\<lambda>x y. (y = 0) ? False : ((x = 0) ? True : (less P(x) P(y))))" and
  def_div: "div := (\<lambda>x y. (x < y) ? 0 : (div (x - y) y))"

lemma less_0_false: "(x < 0) = False"
proof (unfold_def def_less)
  show "((0 = 0) ? False : ((x = 0) ? True : (P(x) < P(0)))) = False"
    proof (rule condI1B)
      show "0 = 0" by (rule eqRefl)
      show "False B" by (rule false_bool)
    qed
qed

(*
 * Non-proof of termination for division. It gets stuck for the base case,
 * since it doesn't terminate for y = 0.
 *)
lemma division_terminates:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  shows "div x y N"
proof (rule GD.ind[where a="y"])
  show hq_cond: "y N" by (rule y_nat)
  show base_case: "div x 0 N"
  proof (unfold_def def_div)
    show "(x < 0) ? 0 : (div (x - 0) 0) N"
      apply (rule GD.eqSubst[where a="0"])
      apply (rule eqSym)
      apply (rule eqSubst[where a="0" and b="div (x-0) 0"])
      apply (rule eqSym)
      (* Recurses to the proof obligation that div x 0 is some natural number.
       * Habeas quid for the win!
       *)
      sorry
  qed
  show ind_step: "\<And>a. a N \<Longrightarrow> div x a N \<Longrightarrow> (div x S(a)) N"
    sorry
qed

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

section \<open>Termination Proofs of Addition and Multiplication\<close>

lemma add_terminates:
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
  show ind_step: "\<And>a. a N \<Longrightarrow> add x a N \<Longrightarrow> add x S(a) N"
    proof (unfold_def def_add)
      fix a
      assume HQ: "a N" and BC: "add x a N"
      show "(S(a) = 0) ? x : S(add x P(S(a))) N"
        proof (rule GD.condT)
          show "S(a) = 0 B"
            apply (rule GD.eqT)
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

lemma mult_terminates:
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
  show ind_step: "\<And>a. a N \<Longrightarrow> mult x a N \<Longrightarrow> mult x S(a) N"
    proof (unfold_def def_mult)
      fix a
      assume HQ: "a N" and BC: "mult x a N"
      show "(S(a) = 0) ? 0 : (add x (mult x P(S(a)))) N"
        proof (rule GD.condT)
          show "S(a) = 0 B"
            apply (rule GD.eqT)
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

end (* End of theory *)
