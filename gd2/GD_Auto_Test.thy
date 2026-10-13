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

text \<open>induct and cases methods.\<close>

lemma
  assumes x: \<open>x N\<close>
  shows \<open>x \<le> x = 1\<close>
  using x
proof (induct x)
  case Base
  show ?case unfolding leq_0 by (rule natD[OF one_N])
next
  case (Step z)
  show ?case unfolding leq_SS[OF Step(1) Step(1)] by (rule Step(2))
qed

lemma
  assumes x: \<open>x N\<close>
  shows \<open>0 + x = x\<close>
  using x
proof (induct strong x)
  case Base
  show ?case unfolding add_0 by (rule zero_eq)
next
  case (Step z)
  have ih: \<open>0 + z = z\<close> by (rule Step(2)[inst_all, OF Step(1) leq_refl[OF Step(1)]])
  show ?case unfolding add_S[OF Step(1)] eq_reflection[OF ih]
    by (rule natD[OF natS[OF Step(1)]])
qed

lemma
  assumes x: \<open>x N\<close>
  shows \<open>x = 0 \<or> \<not> (x = 0)\<close>
  using x
proof (cases x)
  case Zero
  then show ?thesis by (rule disjI1)
next
  case (Suc b)
  have \<open>\<not> (S b = 0)\<close> by (rule sucNonZero[OF Suc(1)])
  then show ?thesis unfolding eq_reflection[OF Suc(2)] by (rule disjI2)
qed

text \<open>Evaluation by simp: with the weak congruence rule for if-then-else, a
  recursive definition can be given to simp directly; the branch not taken is
  never unfolded.\<close>

lemma \<open>div 7 2 = 3\<close> by (simp add: div_def)
lemma \<open>div 100 2 = 50\<close> by (simp add: div_def)
lemma \<open>7 mod 2 = 1\<close> by (simp add: mod_def)
lemma \<open>(if 2 = 3 then div 1 0 else 5) = 5\<close> by simp

text \<open>Simp decides comparisons and propositional structure on numerals.\<close>

lemma \<open>(3 \<le> 2) \<or> (2 < 3)\<close> by simp
lemma \<open>\<not> (3 = 4)\<close> by simp

text \<open>Induction plus simp for a nested recursive function: the inner call
  is rewritten by the induction hypothesis before the outer one is unfolded.\<close>

gd_def zt :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>zt n \<equiv> if n = 0 then 0 else zt (zt (P n))\<close>

lemma zt_0: \<open>zt 0 \<equiv> 0\<close> using zt_def[of 0] by simp
lemma zt_S: \<open>m N \<Longrightarrow> zt (S m) \<equiv> zt (zt m)\<close> using zt_def[of \<open>S m\<close>] by simp

lemma \<open>n N \<Longrightarrow> zt n = 0\<close>
  by (induct n) (simp_all add: zt_0 zt_S)

text \<open>Induction with a generalised variable, and subst.\<close>

lemma
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>x + y = y + x\<close>
  using x y
proof (induct x arbitrary: y)
  case (Base y)
  show ?case using Base by simp
next
  case (Step a y)
  show ?case using Step(1) Step(3) by (simp add: Step(2)[inst_all, OF Step(3)])
qed

lemma
  assumes h: \<open>a = 3\<close>
  shows \<open>a + 1 = 4\<close>
  by (subst h, simp)

end
