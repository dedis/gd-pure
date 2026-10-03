theory GD_Auto_Test
  imports GD_Arith
begin

text \<open>
  Smoke tests for the automation, kept out of GD_Base and GD_Arith so that a
  failure here does not block the library.  Each lemma states what should
  make it go through.
\<close>

text \<open>auto: resolution with the [auto] termination rules.\<close>

lemma \<open>x N \<Longrightarrow> y N \<Longrightarrow> x + y N\<close> by auto
lemma \<open>x N \<Longrightarrow> y N \<Longrightarrow> (x * y) + S x N\<close> by auto
lemma \<open>x N \<Longrightarrow> y N \<Longrightarrow> (x + y = y) B\<close> by auto

text \<open>simp: computation rules as rewrites; N side conditions by the solver.\<close>

lemma \<open>x + 0 = x \<Longrightarrow> x N\<close> by simp
lemma \<open>x N \<Longrightarrow> x + 0 = x\<close> by simp
lemma \<open>x N \<Longrightarrow> y N \<Longrightarrow> x + S y = S (x + y)\<close> by simp
lemma \<open>2 + 2 = 4\<close> by simp
lemma \<open>2 * 3 = 6\<close> by simp
lemma \<open>3 \<le> 5 = 1\<close> by simp

text \<open>A fact rewrites to its truth value: here the premise c turns the
  conditional into its first branch.\<close>

lemma \<open>c \<Longrightarrow> a N \<Longrightarrow> (if c then a else b) = a\<close> by simp

text \<open>unfold_def: one unfolding of a recursive definition, then simp.\<close>

lemma
  assumes \<open>x N\<close>
  shows \<open>x + 0 = x\<close>
  by (unfold_def add_def, simp add: assms)

end
