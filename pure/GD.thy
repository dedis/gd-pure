(* Title: pure/GD.thy
*)

section \<open>Grounded deduction logic\<close>

theory GD
  imports Pure
begin

text \<open>The following theory development formalizes the Grounded Deduction Logic.\<close>

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
  negE: \<open>\<lbrakk>P; \<not>P\<rbrakk> \<Longrightarrow> Q\<close>

section \<open>Axiomatization of equality in GD\<close>

typedecl nat

axiomatization
  eq :: \<open>[nat, nat] \<Rightarrow> o\<close>  (infixl \<open>=\<close> 50)
where
  eqRefl: \<open>a = a\<close> and
  eqSubst: \<open>a = b \<Longrightarrow> Q a \<Longrightarrow> Q b\<close> and
  eqSym: \<open>a = b \<Longrightarrow> b = a\<close>

definition neq (infixl \<open>\<noteq>\<close> 50)
  where \<open>a \<noteq> b \<equiv> \<not> (a = b)\<close>

section \<open>Axiomatization of naturals in GD\<close>

axiomatization
  zero :: \<open>nat\<close>           (\<open>0\<close>) and
  suc :: \<open>nat \<Rightarrow> nat\<close>     (\<open>S(_)\<close> [800]) and
  pred :: \<open>nat \<Rightarrow> nat\<close>     (\<open>P(_)\<close> [800])
where
  sucInj: \<open>S a = S b \<Longrightarrow> a = b\<close> and
  sucInj2: \<open>a = b \<Longrightarrow> S a = S b\<close>

definition \<open>True \<equiv> 0 = 0\<close>
definition \<open>False \<equiv> 0 = S(0)\<close>
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
  eqT: \<open>\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow> a = b B\<close> and
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
  condT: \<open>\<lbrakk>c B; a N; b N\<rbrakk> \<Longrightarrow> (c ? a : b) N\<close>

section \<open>Dynamic Typing Rules in GD\<close>


section \<open>Definitional Mechanism in GD\<close>

axiomatization
  def :: \<open>['a \<Rightarrow> 'a \<Rightarrow> 'a] \<Rightarrow> ['a \<Rightarrow> 'a \<Rightarrow> 'a] \<Rightarrow> o\<close>
where
  defU: \<open>\<lbrakk>def a b; Q b\<rbrakk> \<Longrightarrow> Q a\<close>

lemma add_terminates:
  assumes A1: \<open>def add (\<lambda>x y.((y = 0) ? x : S(add x P(y))))\<close>
  assumes A2: \<open>x N\<close>
  assumes A3: \<open>y N\<close>
  shows       \<open>(add x y) N\<close>
apply (rule ind[where Q="\<lambda>n. add x n N" and a=y])
apply (rule A3)
apply (rule eqSubst[where a="x" and b="add x 0"])
apply (rule defU[where a="add" and b="(\<lambda>x y.((y = 0) ? x : S(add x P(y))))"])
apply (rule A1)
apply (rule eqSym)
apply (rule condI1)
apply (rule eqRefl)
apply (rule A2)
apply (rule A2)
apply (rule defU[where a="add" and b="\<lambda>x y.((y = 0) ? x : S(add x P(y)))"])
apply (rule A1)
apply (rule GD.condT)
apply (rule GD.eqT)
apply (rule GD.natS)
proof -
  fix xa
  assume H: "xa N" and BC: "add x xa N"
  show "xa N"
    by (rule H)
  show "0 N"
    by (rule GD.nat0)
  show "x N"
    by (rule A2)
  show "S (add x P(S(xa))) N"
  proof -
    show "S (add x P(S(xa))) N"
    apply (rule GD.natS)
    apply (rule eqSubst[where a="add x xa" and b="add x P(S(xa))"])
    apply (rule eqSubst[where a="xa" and b="P(S(xa))"])
    apply (rule eqSym)
    apply (rule predSucSym)
    apply (rule H)
    apply (rule eqRefl)
    apply (rule BC)
    done
  qed
qed
end
