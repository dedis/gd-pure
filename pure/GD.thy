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
  eq :: \<open>['a, 'a] \<Rightarrow> o\<close>  (infixl \<open>=\<close> 50)
where
  refl: \<open>a = a\<close> and
  subst: \<open>a = b \<Longrightarrow> P(a) \<Longrightarrow> P(b)\<close>

axiomatization
  False :: \<open>o\<close> and
  conj :: \<open>[o, o] => o\<close>  (infixr \<open>\<and>\<close> 35) and
  disj :: \<open>[o, o] => o\<close>  (infixr \<open>\<or>\<close> 30) and
  imp :: \<open>[o, o] => o\<close>  (infixr \<open>\<longrightarrow>\<close> 25)
where
  conjI: \<open>\<lbrakk>P;  Q\<rbrakk> \<Longrightarrow> P \<and> Q\<close> and
  conjunct1: \<open>P \<and> Q \<Longrightarrow> P\<close> and
  conjunct2: \<open>P \<and> Q \<Longrightarrow> Q\<close> and

  disjI1: \<open>P \<Longrightarrow> P \<or> Q\<close> and
  disjI2: \<open>Q \<Longrightarrow> P \<or> Q\<close> and
  disjE: \<open>\<lbrakk>P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R\<close> and

  impI: \<open>(P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q\<close> and
  mp: \<open>\<lbrakk>P \<longrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q\<close> and

  FalseE: \<open>False \<Longrightarrow> P\<close>

definition \<open>True \<equiv> False \<longrightarrow> False\<close>

definition nequal (infixl \<open>\<noteq>\<close> 50)
  where \<open>P \<noteq> Q \<equiv> (P = Q) \<longrightarrow> False\<close>

section \<open>Axiomatization of naturals in GD\<close>

typedecl nat

axiomatization
  zero :: \<open>nat\<close> and
  succ :: \<open>nat \<Rightarrow> nat\<close>
where
  succInj: \<open>succ m = succ n \<Longrightarrow> m = n\<close> and
  succNonZero: \<open>succ n \<noteq> zero\<close> and
  ind: \<open>\<lbrakk>P zero; \<And>n. P n \<Longrightarrow> P (succ n)\<rbrakk> \<Longrightarrow> P n\<close>

end
