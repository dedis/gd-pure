theory GD_Arith
  imports GD_Base
begin

text \<open>
  Port of the arithmetic section of pure/GD.thy, first slice: the
  definitions, their computation rules, termination (habeas quid) lemmas, and
  the basic algebra of + and \<le>, and strong induction.

  Two things the new kernel changes, visible below:
  \<^item> computation rules are meta-equalities and mostly need no N premise on
    the arguments that are not inspected (x + 0 \<equiv> x holds for every x, even
    a divergent one), because the conditional rules are lazy;
  \<^item> each function is its own gd_def block, so gd_approx can later be
    applied per function.
\<close>


section \<open>Definitions\<close>

gd_def add :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infixl \<open>+\<close> 60)
  where \<open>x + y \<equiv> if y = 0 then x else S (x + P y)\<close>

gd_def sub :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infixl \<open>-\<close> 60)
  where \<open>x - y \<equiv> if y = 0 then x else P (x - P y)\<close>

gd_def mult :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infixl \<open>*\<close> 70)
  where \<open>x * y \<equiv> if y = 0 then 0 else x + x * P y\<close>

gd_def leq :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infix \<open>\<le>\<close> 50)
  where \<open>x \<le> y \<equiv> if x = 0 then 1 else if y = 0 then 0 else P x \<le> P y\<close>

gd_def less :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infix \<open><\<close> 50)
  where \<open>x < y \<equiv> if y = 0 then 0 else if x = 0 then 1 else P x < P y\<close>

gd_def div :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>
  where \<open>div x y \<equiv> if x < y = 1 then 0 else S (div (x - y) y)\<close>


section \<open>Computation rules\<close>

text \<open>Each is one unfolding of the definition followed by taking the branch.\<close>

lemma add_0 [simp]: \<open>x + 0 \<equiv> x\<close>
  using add_def[of x 0] unfolding condT[OF zero_eq] .

lemma add_S [simp]:
  assumes y: \<open>y N\<close>
  shows \<open>x + S y \<equiv> S (x + y)\<close>
  using add_def[of x \<open>S y\<close>]
  unfolding condF[OF sucNonZero[OF y]] eq_reflection[OF predSuc[OF y]] .

lemma sub_0 [simp]: \<open>x - 0 \<equiv> x\<close>
  using sub_def[of x 0] unfolding condT[OF zero_eq] .

lemma sub_S [simp]:
  assumes y: \<open>y N\<close>
  shows \<open>x - S y \<equiv> P (x - y)\<close>
  using sub_def[of x \<open>S y\<close>]
  unfolding condF[OF sucNonZero[OF y]] eq_reflection[OF predSuc[OF y]] .

lemma mult_0 [simp]: \<open>x * 0 \<equiv> 0\<close>
  using mult_def[of x 0] unfolding condT[OF zero_eq] .

lemma mult_S [simp]:
  assumes y: \<open>y N\<close>
  shows \<open>x * S y \<equiv> x + x * y\<close>
  using mult_def[of x \<open>S y\<close>]
  unfolding condF[OF sucNonZero[OF y]] eq_reflection[OF predSuc[OF y]] .

lemma leq_0 [simp]: \<open>0 \<le> y \<equiv> 1\<close>
  using leq_def[of 0 y] unfolding condT[OF zero_eq] .

lemma leq_S0 [simp]:
  assumes x: \<open>x N\<close>
  shows \<open>S x \<le> 0 \<equiv> 0\<close>
  using leq_def[of \<open>S x\<close> 0]
  unfolding condF[OF sucNonZero[OF x]] condT[OF zero_eq] .

lemma leq_SS [simp]:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>S x \<le> S y \<equiv> x \<le> y\<close>
  using leq_def[of \<open>S x\<close> \<open>S y\<close>]
  unfolding condF[OF sucNonZero[OF x]] condF[OF sucNonZero[OF y]]
    eq_reflection[OF predSuc[OF x]] eq_reflection[OF predSuc[OF y]] .

lemma less_0 [simp]: \<open>x < 0 \<equiv> 0\<close>
  using less_def[of x 0] unfolding condT[OF zero_eq] .

lemma less_0S [simp]:
  assumes y: \<open>y N\<close>
  shows \<open>0 < S y \<equiv> 1\<close>
  using less_def[of 0 \<open>S y\<close>]
  unfolding condF[OF sucNonZero[OF y]] condT[OF zero_eq] .

lemma less_SS [simp]:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>S x < S y \<equiv> x < y\<close>
  using less_def[of \<open>S x\<close> \<open>S y\<close>]
  unfolding condF[OF sucNonZero[OF y]] condF[OF sucNonZero[OF x]]
    eq_reflection[OF predSuc[OF x]] eq_reflection[OF predSuc[OF y]] .


section \<open>Termination\<close>

lemma add_N [auto]:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>x + y N\<close>
proof (rule ind[OF y])
  show \<open>x + 0 N\<close> unfolding add_0 by (rule x)
next
  fix z
  assume z: \<open>z N\<close> and ih: \<open>x + z N\<close>
  show \<open>x + S z N\<close> unfolding add_S[OF z] by (rule natS[OF ih])
qed

lemma sub_N [auto]:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>x - y N\<close>
proof (rule ind[OF y])
  show \<open>x - 0 N\<close> unfolding sub_0 by (rule x)
next
  fix z
  assume z: \<open>z N\<close> and ih: \<open>x - z N\<close>
  show \<open>x - S z N\<close> unfolding sub_S[OF z] by (rule natP[OF ih])
qed

lemma mult_N [auto]:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>x * y N\<close>
proof (rule ind[OF y])
  show \<open>x * 0 N\<close> unfolding mult_0 by (rule nat0)
next
  fix z
  assume z: \<open>z N\<close> and ih: \<open>x * z N\<close>
  show \<open>x * S z N\<close> unfolding mult_S[OF z] by (rule add_N[OF x ih])
qed

text \<open>\<le> and < recurse on both arguments, so the induction is on y with x
  generalised; the motive is a Pure statement, not an object formula.\<close>

text \<open>The induction is on y with x generalised.  The generalisation is done
  with the object quantifier: a motive of the form  \<And>a. a N \<Longrightarrow> ...  is not
  in the normal form rule expects (Isabelle cannot match it against a goal
  with parameters), whereas  \<forall>a. a \<le> w N  is an ordinary formula.\<close>

lemma leq_N [auto]:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>x \<le> y N\<close>
proof -
  have H: \<open>\<forall>a. a \<le> y N\<close>
  proof (rule ind[OF y])
    show \<open>\<forall>a. a \<le> 0 N\<close>
    proof (rule forallI)
      fix a
      assume a: \<open>a N\<close>
      show \<open>a \<le> 0 N\<close>
      proof (rule nat_cases[OF a])
        assume e: \<open>a = 0\<close>
        show \<open>a \<le> 0 N\<close> unfolding eq_reflection[OF e] leq_0 by (rule one_N)
      next
        fix b
        assume b: \<open>b N\<close> and e: \<open>a = S b\<close>
        show \<open>a \<le> 0 N\<close> unfolding eq_reflection[OF e] leq_S0[OF b] by (rule nat0)
      qed
    qed
  next
    fix z
    assume z: \<open>z N\<close> and ih: \<open>\<forall>a. a \<le> z N\<close>
    show \<open>\<forall>a. a \<le> S z N\<close>
    proof (rule forallI)
      fix a
      assume a: \<open>a N\<close>
      show \<open>a \<le> S z N\<close>
      proof (rule nat_cases[OF a])
        assume e: \<open>a = 0\<close>
        show \<open>a \<le> S z N\<close> unfolding eq_reflection[OF e] leq_0 by (rule one_N)
      next
        fix b
        assume b: \<open>b N\<close> and e: \<open>a = S b\<close>
        show \<open>a \<le> S z N\<close>
          unfolding eq_reflection[OF e] leq_SS[OF b z] by (rule forallE[OF ih b])
      qed
    qed
  qed
  show \<open>x \<le> y N\<close> by (rule forallE[OF H x])
qed

lemma less_N [auto]:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>x < y N\<close>
proof -
  have H: \<open>\<forall>a. a < y N\<close>
  proof (rule ind[OF y])
    show \<open>\<forall>a. a < 0 N\<close>
    proof (rule forallI)
      fix a
      show \<open>a < 0 N\<close> unfolding less_0 by (rule nat0)
    qed
  next
    fix z
    assume z: \<open>z N\<close> and ih: \<open>\<forall>a. a < z N\<close>
    show \<open>\<forall>a. a < S z N\<close>
    proof (rule forallI)
      fix a
      assume a: \<open>a N\<close>
      show \<open>a < S z N\<close>
      proof (rule nat_cases[OF a])
        assume e: \<open>a = 0\<close>
        show \<open>a < S z N\<close> unfolding eq_reflection[OF e] less_0S[OF z] by (rule one_N)
      next
        fix b
        assume b: \<open>b N\<close> and e: \<open>a = S b\<close>
        show \<open>a < S z N\<close>
          unfolding eq_reflection[OF e] less_SS[OF b z] by (rule forallE[OF ih b])
      qed
    qed
  qed
  show \<open>x < y N\<close> by (rule forallE[OF H x])
qed


section \<open>Addition\<close>

lemma zero_add [simp]:
  assumes a: \<open>a N\<close>
  shows \<open>0 + a = a\<close>
proof (rule ind[OF a])
  show \<open>0 + 0 = 0\<close> unfolding add_0 by (rule zero_eq)
next
  fix z
  assume z: \<open>z N\<close> and ih: \<open>0 + z = z\<close>
  show \<open>0 + S z = S z\<close>
    unfolding add_S[OF z] eq_reflection[OF ih] by (rule natD[OF natS[OF z]])
qed

lemma add_S_left:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>S x + y = S (x + y)\<close>
proof (rule ind[OF y])
  show \<open>S x + 0 = S (x + 0)\<close> unfolding add_0 by (rule natD[OF natS[OF x]])
next
  fix z
  assume z: \<open>z N\<close> and ih: \<open>S x + z = S (x + z)\<close>
  show \<open>S x + S z = S (x + S z)\<close>
    unfolding add_S[OF z] eq_reflection[OF ih]
    by (rule natD[OF natS[OF natS[OF add_N[OF x z]]]])
qed

lemma add_comm:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>x + y = y + x\<close>
proof (rule ind[OF y])
  show \<open>x + 0 = 0 + x\<close>
    unfolding add_0 eq_reflection[OF zero_add[OF x]] by (rule natD[OF x])
next
  fix z
  assume z: \<open>z N\<close> and ih: \<open>x + z = z + x\<close>
  show \<open>x + S z = S z + x\<close>
    unfolding add_S[OF z] eq_reflection[OF add_S_left[OF z x]] eq_reflection[OF ih]
    by (rule natD[OF natS[OF add_N[OF z x]]])
qed

lemma add_assoc:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and z: \<open>z N\<close>
  shows \<open>x + y + z = x + (y + z)\<close>
proof (rule ind[OF z])
  show \<open>x + y + 0 = x + (y + 0)\<close>
    unfolding add_0 by (rule natD[OF add_N[OF x y]])
next
  fix w
  assume w: \<open>w N\<close> and ih: \<open>x + y + w = x + (y + w)\<close>
  show \<open>x + y + S w = x + (y + S w)\<close>
    unfolding add_S[OF w] add_S[OF add_N[OF y w]] eq_reflection[OF ih]
    by (rule natD[OF natS[OF add_N[OF x add_N[OF y w]]]])
qed

lemma add_one: \<open>x + 1 \<equiv> S x\<close>
  unfolding add_S[OF nat0] add_0 by (rule Pure.reflexive)


section \<open>Multiplication\<close>

lemma zero_mult [simp]:
  assumes a: \<open>a N\<close>
  shows \<open>0 * a = 0\<close>
proof (rule ind[OF a])
  show \<open>0 * 0 = 0\<close> unfolding mult_0 by (rule zero_eq)
next
  fix z
  assume z: \<open>z N\<close> and ih: \<open>0 * z = 0\<close>
  show \<open>0 * S z = 0\<close>
    unfolding mult_S[OF z] eq_reflection[OF ih] add_0 by (rule zero_eq)
qed

lemma mult_1:
  assumes x: \<open>x N\<close>
  shows \<open>x * 1 = x\<close>
  unfolding mult_S[OF nat0] mult_0 add_0 by (rule natD[OF x])


section \<open>Order\<close>

lemma leq_refl:
  assumes x: \<open>x N\<close>
  shows \<open>x \<le> x = 1\<close>
proof (rule ind[OF x])
  show \<open>0 \<le> 0 = 1\<close> unfolding leq_0 by (rule natD[OF one_N])
next
  fix z
  assume z: \<open>z N\<close> and ih: \<open>z \<le> z = 1\<close>
  show \<open>S z \<le> S z = 1\<close> unfolding leq_SS[OF z z] by (rule ih)
qed

lemma less_irrefl:
  assumes x: \<open>x N\<close>
  shows \<open>x < x = 0\<close>
proof (rule ind[OF x])
  show \<open>0 < 0 = 0\<close> unfolding less_0 by (rule zero_eq)
next
  fix z
  assume z: \<open>z N\<close> and ih: \<open>z < z = 0\<close>
  show \<open>S z < S z = 0\<close> unfolding less_SS[OF z z] by (rule ih)
qed

lemma leq_S_self:
  assumes x: \<open>x N\<close>
  shows \<open>x \<le> S x = 1\<close>
proof (rule ind[OF x])
  show \<open>0 \<le> S 0 = 1\<close> unfolding leq_0 by (rule natD[OF one_N])
next
  fix z
  assume z: \<open>z N\<close> and ih: \<open>z \<le> S z = 1\<close>
  show \<open>S z \<le> S (S z) = 1\<close> unfolding leq_SS[OF z natS[OF z]] by (rule ih)
qed


section \<open>Order facts needed for strong induction\<close>

lemma less_S_self:
  assumes a: \<open>a N\<close>
  shows \<open>a < S a = 1\<close>
proof (rule ind[OF a])
  show \<open>0 < S 0 = 1\<close> unfolding less_0S[OF nat0] by (rule natD[OF one_N])
next
  fix z
  assume z: \<open>z N\<close> and ih: \<open>z < S z = 1\<close>
  show \<open>S z < S (S z) = 1\<close> unfolding less_SS[OF z natS[OF z]] by (rule ih)
qed

lemma less_zero_E:
  assumes h: \<open>y < 0 = 1\<close>
  shows \<open>PROP R\<close>
proof -
  have z: \<open>0 = 1\<close> using h unfolding less_0 .
  show \<open>PROP R\<close> by (rule exF[OF z zero_neq_suc[OF nat0]])
qed

definition less_S_cases :: \<open>tm \<Rightarrow> prop\<close> where
  \<open>less_S_cases n \<equiv> (\<And>y (R :: prop). y N \<Longrightarrow> y < S n = 1 \<Longrightarrow>
      (y < n = 1 \<Longrightarrow> PROP R) \<Longrightarrow> (y = n \<Longrightarrow> PROP R) \<Longrightarrow> PROP R)\<close>

lemma less_S_cases_all:
  assumes n: \<open>n N\<close>
  shows \<open>PROP less_S_cases n\<close>
proof (rule ind[where Q=less_S_cases, OF n])
  show \<open>PROP less_S_cases 0\<close> unfolding less_S_cases_def
  proof -
    fix y and R :: "prop"
    assume y: \<open>y N\<close> and h: \<open>y < S 0 = 1\<close>
      and lt: \<open>y < 0 = 1 \<Longrightarrow> PROP R\<close> and eq: \<open>y = 0 \<Longrightarrow> PROP R\<close>
    show \<open>PROP R\<close>
    proof (rule nat_cases[OF y])
      assume e: \<open>y = 0\<close>
      show \<open>PROP R\<close> by (rule eq[OF e])
    next
      fix b
      assume b: \<open>b N\<close> and e: \<open>y = S b\<close>
      have \<open>b < 0 = 1\<close> using h unfolding eq_reflection[OF e] less_SS[OF b nat0] .
      then show \<open>PROP R\<close> by (rule less_zero_E)
    qed
  qed
next
  fix x
  assume x: \<open>x N\<close> and ih: \<open>PROP less_S_cases x\<close>
  show \<open>PROP less_S_cases (S x)\<close> unfolding less_S_cases_def
  proof -
    fix y and R :: "prop"
    assume y: \<open>y N\<close> and h: \<open>y < S (S x) = 1\<close>
      and lt: \<open>y < S x = 1 \<Longrightarrow> PROP R\<close> and eq: \<open>y = S x \<Longrightarrow> PROP R\<close>
    show \<open>PROP R\<close>
    proof (rule nat_cases[OF y])
      assume e: \<open>y = 0\<close>
      show \<open>PROP R\<close>
      proof (rule lt)
        show \<open>y < S x = 1\<close>
          unfolding eq_reflection[OF e] less_0S[OF x] by (rule natD[OF one_N])
      qed
    next
      fix b
      assume b: \<open>b N\<close> and e: \<open>y = S b\<close>
      have hb: \<open>b < S x = 1\<close> using h unfolding eq_reflection[OF e] less_SS[OF b natS[OF x]] .
      show \<open>PROP R\<close>
      proof (rule ih[unfolded less_S_cases_def, inst_all, OF b hb])
        assume bx: \<open>b < x = 1\<close>
        show \<open>PROP R\<close>
        proof (rule lt)
          show \<open>y < S x = 1\<close> unfolding eq_reflection[OF e] less_SS[OF b x] by (rule bx)
        qed
      next
        assume bx: \<open>b = x\<close>
        show \<open>PROP R\<close>
        proof (rule eq)
          show \<open>y = S x\<close>
            unfolding eq_reflection[OF e] eq_reflection[OF bx] by (rule natD[OF natS[OF x]])
        qed
      qed
    qed
  qed
qed

lemma less_S_E:
  assumes y: \<open>y N\<close> and n: \<open>n N\<close> and h: \<open>y < S n = 1\<close>
  shows \<open>(y < n = 1 \<Longrightarrow> PROP R) \<Longrightarrow> (y = n \<Longrightarrow> PROP R) \<Longrightarrow> PROP R\<close>
  by (rule less_S_cases_all[OF n, unfolded less_S_cases_def, inst_all, OF y h])

definition leq_less_S :: \<open>tm \<Rightarrow> prop\<close> where
  \<open>leq_less_S n \<equiv> (\<And>y. y N \<Longrightarrow> y \<le> n = 1 \<Longrightarrow> y < S n = 1)\<close>

lemma leq_less_S_all:
  assumes n: \<open>n N\<close>
  shows \<open>PROP leq_less_S n\<close>
proof (rule ind[where Q=leq_less_S, OF n])
  show \<open>PROP leq_less_S 0\<close> unfolding leq_less_S_def
  proof -
    fix y
    assume y: \<open>y N\<close> and h: \<open>y \<le> 0 = 1\<close>
    show \<open>y < S 0 = 1\<close>
    proof (rule nat_cases[OF y])
      assume e: \<open>y = 0\<close>
      show \<open>y < S 0 = 1\<close> unfolding eq_reflection[OF e] less_0S[OF nat0] by (rule natD[OF one_N])
    next
      fix b
      assume b: \<open>b N\<close> and e: \<open>y = S b\<close>
      have z: \<open>0 = 1\<close> using h unfolding eq_reflection[OF e] leq_S0[OF b] .
      show \<open>y < S 0 = 1\<close> by (rule exF[OF z zero_neq_suc[OF nat0]])
    qed
  qed
next
  fix x
  assume x: \<open>x N\<close> and ih: \<open>PROP leq_less_S x\<close>
  show \<open>PROP leq_less_S (S x)\<close> unfolding leq_less_S_def
  proof -
    fix y
    assume y: \<open>y N\<close> and h: \<open>y \<le> S x = 1\<close>
    show \<open>y < S (S x) = 1\<close>
    proof (rule nat_cases[OF y])
      assume e: \<open>y = 0\<close>
      show \<open>y < S (S x) = 1\<close>
        unfolding eq_reflection[OF e] less_0S[OF natS[OF x]] by (rule natD[OF one_N])
    next
      fix b
      assume b: \<open>b N\<close> and e: \<open>y = S b\<close>
      have hb: \<open>b \<le> x = 1\<close> using h unfolding eq_reflection[OF e] leq_SS[OF b x] .
      show \<open>y < S (S x) = 1\<close>
        unfolding eq_reflection[OF e] less_SS[OF b natS[OF x]]
        by (rule ih[unfolded leq_less_S_def, inst_all, OF b hb])
    qed
  qed
qed

lemma leq_imp_less_S:
  assumes y: \<open>y N\<close> and n: \<open>n N\<close> and h: \<open>y \<le> n = 1\<close>
  shows \<open>y < S n = 1\<close>
  by (rule leq_less_S_all[OF n, unfolded leq_less_S_def, inst_all, OF y h])


section \<open>Strong induction\<close>

definition below :: \<open>(tm \<Rightarrow> prop) \<Rightarrow> tm \<Rightarrow> prop\<close> where
  \<open>below Q n \<equiv> (\<And>y. y N \<Longrightarrow> y < n = 1 \<Longrightarrow> PROP Q y)\<close>

text \<open>Course-of-values induction: to prove Q x, assume Q for everything below x.\<close>

lemma less_induct [case_names HQ Step]:
  assumes a: \<open>a N\<close>
    and step: \<open>\<And>x. x N \<Longrightarrow> (\<And>y. y N \<Longrightarrow> y < x = 1 \<Longrightarrow> PROP Q y) \<Longrightarrow> PROP Q x\<close>
  shows \<open>PROP Q a\<close>
proof -
  have all: \<open>PROP below Q n\<close> if n: \<open>n N\<close> for n
  proof (rule ind[where Q=\<open>below Q\<close>, OF n])
    show \<open>PROP below Q 0\<close> unfolding below_def
    proof -
      fix y
      assume \<open>y N\<close> and h: \<open>y < 0 = 1\<close>
      show \<open>PROP Q y\<close> by (rule less_zero_E[OF h])
    qed
  next
    fix x
    assume x: \<open>x N\<close> and ih: \<open>PROP below Q x\<close>
    show \<open>PROP below Q (S x)\<close> unfolding below_def
    proof -
      fix y
      assume y: \<open>y N\<close> and h: \<open>y < S x = 1\<close>
      show \<open>PROP Q y\<close>
      proof (rule less_S_E[OF y x h])
        assume yx: \<open>y < x = 1\<close>
        show \<open>PROP Q y\<close> by (rule ih[unfolded below_def, inst_all, OF y yx])
      next
        assume e: \<open>y = x\<close>
        show \<open>PROP Q y\<close> unfolding eq_reflection[OF e]
        proof (rule step[inst_all, OF x])
          fix z
          assume z: \<open>z N\<close> and zx: \<open>z < x = 1\<close>
          show \<open>PROP Q z\<close> by (rule ih[unfolded below_def, inst_all, OF z zx])
        qed
      qed
    qed
  qed
  show \<open>PROP Q a\<close> by (rule all[OF natS[OF a], unfolded below_def, inst_all, OF a less_S_self[OF a]])
qed

text \<open>The form of pure/GD.thy: base case 0, and S x from everything up to x.\<close>

lemma strong_induction [case_names HQ Base Step]:
  assumes a: \<open>a N\<close>
    and base: \<open>PROP Q 0\<close>
    and step: \<open>\<And>x. x N \<Longrightarrow> (\<And>y. y N \<Longrightarrow> y \<le> x = 1 \<Longrightarrow> PROP Q y) \<Longrightarrow> PROP Q (S x)\<close>
  shows \<open>PROP Q a\<close>
proof (rule less_induct[where Q=Q, OF a])
  fix x
  assume x: \<open>x N\<close> and ih: \<open>\<And>y. y N \<Longrightarrow> y < x = 1 \<Longrightarrow> PROP Q y\<close>
  show \<open>PROP Q x\<close>
  proof (rule nat_cases[OF x])
    assume e: \<open>x = 0\<close>
    show \<open>PROP Q x\<close> unfolding eq_reflection[OF e] by (rule base)
  next
    fix b
    assume b: \<open>b N\<close> and e: \<open>x = S b\<close>
    show \<open>PROP Q x\<close> unfolding eq_reflection[OF e]
    proof (rule step[inst_all, OF b])
      fix y
      assume y: \<open>y N\<close> and yb: \<open>y \<le> b = 1\<close>
      have \<open>y < x = 1\<close> unfolding eq_reflection[OF e] by (rule leq_imp_less_S[OF y b yb])
      then show \<open>PROP Q y\<close> by (rule ih[inst_all, OF y])
    qed
  qed
qed


section \<open>More arithmetic\<close>

abbreviation greater :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infix \<open>>\<close> 50)
  where \<open>x > y \<equiv> y < x\<close>

abbreviation geq :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infix \<open>\<ge>\<close> 50)
  where \<open>x \<ge> y \<equiv> y \<le> x\<close>

declare add_S_left [simp]
declare sub_S [simp del]

text \<open>sub_S is not a simp rule here: on  S x - S y  it would fire before sub_SS.
  Numerals still compute, through sub_SS and sub_0.\<close>

lemma one_mult [simp]: \<open>y N \<Longrightarrow> 1 * y = y\<close>
  by (induct y) simp_all

lemma mult_S_left [simp]:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>S x * y = x * y + y\<close>
  using y x by (induct y) (simp_all add: add_assoc)

lemma add_left_comm:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and z: \<open>z N\<close>
  shows \<open>x + (y + z) = y + (x + z)\<close>
  unfolding eq_reflection[OF eqSym[OF add_assoc[OF x y z]]] eq_reflection[OF add_comm[OF x y]]
    eq_reflection[OF add_assoc[OF y x z]]
  by (rule natD[OF add_N[OF y add_N[OF x z]]])

subsection \<open>Truth values of comparisons\<close>

lemma leq_B [auto]:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>(x \<le> y) B\<close>
  using y x
proof (induct y arbitrary: x)
  case (Base x)
  show ?case using Base by (cases x) simp_all
next
  case (Step z x)
  show ?case using Step(3)
  proof (cases x)
    case Zero
    then show ?thesis by simp
  next
    case (Suc b)
    then show ?thesis using Step(1) Step(2)[inst_all, OF Suc(1)] by simp
  qed
qed

lemma less_B [auto]:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>(x < y) B\<close>
  using y x
proof (induct y arbitrary: x)
  case Base
  show ?case by simp
next
  case (Step z x)
  show ?case using Step(3)
  proof (cases x)
    case Zero
    then show ?thesis using Step(1) by simp
  next
    case (Suc b)
    then show ?thesis using Step(1) Step(2)[inst_all, OF Suc(1)] by simp
  qed
qed

lemma less_Sleq:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>(x < y) \<equiv> (S x \<le> y)\<close>
proof (rule eq_reflection)
  show \<open>(x < y) = (S x \<le> y)\<close>
    using y x
  proof (induct y arbitrary: x)
    case Base
    show ?case using Base by simp
  next
    case (Step z x)
    show ?case using Step(3)
    proof (cases x)
      case Zero
      then show ?thesis using Step(1) by simp
    next
      case (Suc b)
      then show ?thesis using Step(1) Step(2)[inst_all, OF Suc(1)] by simp
    qed
  qed
qed

subsection \<open>Order\<close>

lemma leq_0_eq:
  assumes x: \<open>x N\<close> and h: \<open>x \<le> 0 = 1\<close>
  shows \<open>x = 0\<close>
  using x h by (cases x) simp_all

lemma pred_leq:
  assumes a: \<open>a N\<close>
  shows \<open>P a \<le> a = 1\<close>
  using a by (cases a) (simp_all add: leq_S_self)

lemma leq_trans:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and z: \<open>z N\<close>
    and xy: \<open>x \<le> y = 1\<close> and yz: \<open>y \<le> z = 1\<close>
  shows \<open>x \<le> z = 1\<close>
  using x y z xy yz
proof (induct x arbitrary: y z)
  case Base
  show ?case by simp
next
  case (Step a y z)
  note IH = Step(2) and h1 = Step(5) and h2 = Step(6)
  show ?case using Step(3)
  proof (cases y)
    case Zero
    then show ?thesis using h1 Step(1) by simp
  next
    case (Suc b)
    note b = Suc(1) and ey = Suc(2)
    show ?thesis using Step(4)
    proof (cases z)
      case Zero
      then show ?thesis using h2 ey b by simp
    next
      case (Suc c)
      have ab: \<open>a \<le> b = 1\<close> using h1 ey b Step(1) by simp
      have bc: \<open>b \<le> c = 1\<close> using h2 ey Suc b by simp
      have ac: \<open>a \<le> c = 1\<close> by (rule IH[inst_all, OF b Suc(1) ab bc])
      show ?thesis using ac Suc Step(1) by simp
    qed
  qed
qed

lemma leq_antisym:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and xy: \<open>x \<le> y = 1\<close> and yx: \<open>y \<le> x = 1\<close>
  shows \<open>x = y\<close>
  using x y xy yx
proof (induct x arbitrary: y)
  case (Base y)
  have \<open>y = 0\<close> by (rule leq_0_eq[OF Base(1) Base(3)])
  then show ?case by simp
next
  case (Step a y)
  show ?case using Step(3)
  proof (cases y)
    case Zero
    then show ?thesis using Step by simp
  next
    case (Suc b)
    have ab: \<open>a \<le> b = 1\<close> using Step(4) Suc Step(1) by simp
    have ba: \<open>b \<le> a = 1\<close> using Step(5) Suc Step(1) by simp
    have \<open>a = b\<close> by (rule Step(2)[inst_all, OF Suc(1) ab ba])
    then show ?thesis using Suc Step(1) by simp
  qed
qed

lemma leq_total:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>x \<le> y = 1 \<or> y \<le> x = 1\<close>
  using x y
proof (induct x arbitrary: y)
  case Base
  show ?case by (rule disjI1, simp)
next
  case (Step a y)
  show ?case using Step(3)
  proof (cases y)
    case Zero
    then show ?thesis using Step(1) by simp
  next
    case (Suc b)
    then show ?thesis using Step(1) Step(2)[inst_all, OF Suc(1)] by simp
  qed
qed

lemma not_less_leq:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and h: \<open>\<not> (x < y = 1)\<close>
  shows \<open>y \<le> x = 1\<close>
  using x y h
proof (induct x arbitrary: y)
  case (Base y)
  show ?case using Base(1) Base(2) by (cases y) simp_all
next
  case (Step a y)
  show ?case using Step(3)
  proof (cases y)
    case Zero
    then show ?thesis by simp
  next
    case (Suc b)
    have \<open>\<not> (a < b = 1)\<close> using Step(4) Suc Step(1) by simp
    then have \<open>b \<le> a = 1\<close> by (rule Step(2)[inst_all, OF Suc(1)])
    then show ?thesis using Suc Step(1) by simp
  qed
qed

lemma less_imp_leq:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and h: \<open>x < y = 1\<close>
  shows \<open>x \<le> y = 1\<close>
proof -
  have Sxy: \<open>S x \<le> y = 1\<close> using h unfolding less_Sleq[OF x y] .
  show ?thesis by (rule leq_trans[OF x natS[OF x] y leq_S_self[OF x] Sxy])
qed

lemma less_trans:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and z: \<open>z N\<close>
    and xy: \<open>x < y = 1\<close> and yz: \<open>y < z = 1\<close>
  shows \<open>x < z = 1\<close>
proof -
  have xy': \<open>x \<le> y = 1\<close> by (rule less_imp_leq[OF x y xy])
  have yz': \<open>S y \<le> z = 1\<close> using yz unfolding less_Sleq[OF y z] .
  have \<open>S x \<le> S y = 1\<close> using xy' x y by simp
  then have \<open>S x \<le> z = 1\<close> by (rule leq_trans[OF natS[OF x] natS[OF y] z _ yz'])
  then show ?thesis unfolding less_Sleq[OF x z] .
qed

lemma leq_add:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>x \<le> x + y = 1\<close>
  using y x
proof (induct y)
  case Base
  show ?case using Base by (simp add: leq_refl)
next
  case (Step z)
  have xz: \<open>x + z N\<close> by (rule add_N[OF Step(3) Step(1)])
  have h: \<open>x + z \<le> S (x + z) = 1\<close> by (rule leq_S_self[OF xz])
  show ?case unfolding add_S[OF Step(1)]
    by (rule leq_trans[OF Step(3) xz natS[OF xz] Step(2) h])
qed

subsection \<open>Subtraction\<close>

lemma zero_sub [simp]: \<open>x N \<Longrightarrow> 0 - x = 0\<close>
  by (induct x) (simp_all add: sub_S)

lemma sub_SS [simp]:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>S x - S y = x - y\<close>
  using y x by (induct y) (simp_all add: sub_S)

lemma sub_self [simp]: \<open>x N \<Longrightarrow> x - x = 0\<close>
  by (induct x) simp_all

lemma add_sub_cancel [simp]:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>x + y - y = x\<close>
  using y x by (induct y) simp_all

lemma sub_leq:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>x - y \<le> x = 1\<close>
  using y x
proof (induct y)
  case Base
  show ?case using Base by (simp add: leq_refl)
next
  case (Step z)
  have xz: \<open>x - z N\<close> by (rule sub_N[OF Step(3) Step(1)])
  show ?case unfolding sub_S[OF Step(1)]
    by (rule leq_trans[OF natP[OF xz] xz Step(3) pred_leq[OF xz] Step(2)])
qed

lemma sub_add:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and h: \<open>y \<le> x = 1\<close>
  shows \<open>x - y + y = x\<close>
  using y x h
proof (induct y arbitrary: x)
  case Base
  show ?case using Base by simp
next
  case (Step z x)
  show ?case using Step(3)
  proof (cases x)
    case Zero
    then show ?thesis using Step by simp
  next
    case (Suc a)
    have za: \<open>z \<le> a = 1\<close> using Step(4) Suc Step(1) by simp
    have \<open>a - z + z = a\<close> by (rule Step(2)[inst_all, OF Suc(1) za])
    then show ?thesis using Suc Step(1) by simp
  qed
qed

lemma sub_less:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and y0: \<open>0 < y = 1\<close> and h: \<open>y \<le> x = 1\<close>
  shows \<open>x - y < x = 1\<close>
  using y y0 h
proof (cases y)
  case Zero
  then show ?thesis using y0 by simp
next
  case (Suc b)
  note b = \<open>b N\<close> and ey = \<open>y = S b\<close>
  show ?thesis using x h
  proof (cases x)
    case Zero
    have \<open>S b \<le> 0 = 1\<close> using h unfolding eq_reflection[OF ey] eq_reflection[OF \<open>x = 0\<close>] .
    then show ?thesis using b by simp
  next
    case (Suc a)
    have lt: \<open>a - b < S a = 1\<close>
      by (rule leq_imp_less_S[OF sub_N[OF \<open>a N\<close> b] \<open>a N\<close> sub_leq[OF \<open>a N\<close> b]])
    show ?thesis using lt ey Suc b by simp
  qed
qed

subsection \<open>Multiplication\<close>

lemma mult_comm:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close>
  shows \<open>x * y = y * x\<close>
  using y x
proof (induct y)
  case Base
  show ?case using Base by simp
next
  case (Step z)
  have IH: \<open>x * z = z * x\<close> by (rule Step(2))
  show ?case
    unfolding mult_S[OF Step(1)] eq_reflection[OF mult_S_left[OF Step(1) Step(3)]] eq_reflection[OF IH]
    by (rule add_comm[OF Step(3) mult_N[OF Step(1) Step(3)]])
qed

lemma add_mult_distrib:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and z: \<open>z N\<close>
  shows \<open>x * (y + z) = x * y + x * z\<close>
  using z x y
proof (induct z)
  case Base
  show ?case using Base by simp
next
  case (Step w)
  have xN: \<open>x N\<close> by (rule Step(3)) have yN: \<open>y N\<close> by (rule Step(4))
  show ?case
    unfolding add_S[OF Step(1)] mult_S[OF add_N[OF yN Step(1)]] eq_reflection[OF Step(2)]
      mult_S[OF Step(1)]
    by (rule add_left_comm[OF xN mult_N[OF xN yN] mult_N[OF xN Step(1)]])
qed

lemma mult_assoc:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and z: \<open>z N\<close>
  shows \<open>x * y * z = x * (y * z)\<close>
  using z x y
proof (induct z)
  case Base
  show ?case using Base by simp
next
  case (Step w)
  have xN: \<open>x N\<close> by (rule Step(3)) have yN: \<open>y N\<close> by (rule Step(4))
  show ?case
    unfolding mult_S[OF Step(1)] eq_reflection[OF add_mult_distrib[OF xN yN mult_N[OF yN Step(1)]]]
      eq_reflection[OF Step(2)]
    by (rule natD, rule add_N[OF mult_N[OF xN yN] mult_N[OF xN mult_N[OF yN Step(1)]]])
qed


subsection \<open>Division\<close>

gd_def mod :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infixl \<open>mod\<close> 70)
  where \<open>x mod y \<equiv> if x < y = 1 then x else (x - y) mod y\<close>

lemma div_N [auto]:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and y0: \<open>0 < y = 1\<close>
  shows \<open>div x y N\<close>
  using x y y0
proof (induct less x)
  case (Step x)
  have e: \<open>div x y \<equiv> if x < y = 1 then 0 else S (div (x - y) y)\<close> by (rule div_def)
  show ?case unfolding e
  proof (rule cases_bool[OF eqBool[OF less_N[OF Step(1) Step(3)] one_N]])
    assume c: \<open>x < y = 1\<close>
    show \<open>(if x < y = 1 then 0 else S (div (x - y) y)) N\<close> unfolding condT[OF c] by (rule nat0)
  next
    assume c: \<open>\<not> (x < y = 1)\<close>
    have yx: \<open>y \<le> x = 1\<close> by (rule not_less_leq[OF Step(1) Step(3) c])
    have lt: \<open>x - y < x = 1\<close> by (rule sub_less[OF Step(1) Step(3) Step(4) yx])
    show \<open>(if x < y = 1 then 0 else S (div (x - y) y)) N\<close>
      unfolding condF[OF c] by (rule natS[OF Step(2)[inst_all, OF sub_N[OF Step(1) Step(3)] lt]])
  qed
qed

lemma mod_N [auto]:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and y0: \<open>0 < y = 1\<close>
  shows \<open>x mod y N\<close>
  using x y y0
proof (induct less x)
  case (Step x)
  have e: \<open>x mod y \<equiv> if x < y = 1 then x else (x - y) mod y\<close> by (rule mod_def)
  show ?case unfolding e
  proof (rule cases_bool[OF eqBool[OF less_N[OF Step(1) Step(3)] one_N]])
    assume c: \<open>x < y = 1\<close>
    show \<open>(if x < y = 1 then x else (x - y) mod y) N\<close> unfolding condT[OF c] by (rule Step(1))
  next
    assume c: \<open>\<not> (x < y = 1)\<close>
    have yx: \<open>y \<le> x = 1\<close> by (rule not_less_leq[OF Step(1) Step(3) c])
    have lt: \<open>x - y < x = 1\<close> by (rule sub_less[OF Step(1) Step(3) Step(4) yx])
    show \<open>(if x < y = 1 then x else (x - y) mod y) N\<close>
      unfolding condF[OF c] by (rule Step(2)[inst_all, OF sub_N[OF Step(1) Step(3)] lt])
  qed
qed

lemma mod_less:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and y0: \<open>0 < y = 1\<close>
  shows \<open>x mod y < y = 1\<close>
  using x y y0
proof (induct less x)
  case (Step x)
  have e: \<open>x mod y \<equiv> if x < y = 1 then x else (x - y) mod y\<close> by (rule mod_def)
  show ?case unfolding e
  proof (rule cases_bool[OF eqBool[OF less_N[OF Step(1) Step(3)] one_N]])
    assume c: \<open>x < y = 1\<close>
    show \<open>(if x < y = 1 then x else (x - y) mod y) < y = 1\<close> unfolding condT[OF c] by (rule c)
  next
    assume c: \<open>\<not> (x < y = 1)\<close>
    have yx: \<open>y \<le> x = 1\<close> by (rule not_less_leq[OF Step(1) Step(3) c])
    have lt: \<open>x - y < x = 1\<close> by (rule sub_less[OF Step(1) Step(3) Step(4) yx])
    show \<open>(if x < y = 1 then x else (x - y) mod y) < y = 1\<close>
      unfolding condF[OF c] by (rule Step(2)[inst_all, OF sub_N[OF Step(1) Step(3)] lt])
  qed
qed

lemma div_mod:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and y0: \<open>0 < y = 1\<close>
  shows \<open>y * div x y + x mod y = x\<close>
  using x y y0
proof (induct less x)
  case (Step x)
  note xN = Step(1) and yN = Step(3) and y0 = Step(4)
  have ed: \<open>div x y \<equiv> if x < y = 1 then 0 else S (div (x - y) y)\<close> by (rule div_def)
  have em: \<open>x mod y \<equiv> if x < y = 1 then x else (x - y) mod y\<close> by (rule mod_def)
  show ?case unfolding ed em
  proof (rule cases_bool[OF eqBool[OF less_N[OF xN yN] one_N]])
    assume c: \<open>x < y = 1\<close>
    show \<open>y * (if x < y = 1 then 0 else S (div (x - y) y)) + (if x < y = 1 then x else (x - y) mod y) = x\<close>
      unfolding condT[OF c] using xN by simp
  next
    assume c: \<open>\<not> (x < y = 1)\<close>
    have yx: \<open>y \<le> x = 1\<close> by (rule not_less_leq[OF xN yN c])
    have lt: \<open>x - y < x = 1\<close> by (rule sub_less[OF xN yN y0 yx])
    have d: \<open>x - y N\<close> by (rule sub_N[OF xN yN])
    have D: \<open>div (x - y) y N\<close> by (rule div_N[OF d yN y0])
    have M: \<open>(x - y) mod y N\<close> by (rule mod_N[OF d yN y0])
    have IH: \<open>y * div (x - y) y + (x - y) mod y = x - y\<close> by (rule Step(2)[inst_all, OF d lt])
    show \<open>y * (if x < y = 1 then 0 else S (div (x - y) y)) + (if x < y = 1 then x else (x - y) mod y) = x\<close>
      unfolding condF[OF c] mult_S[OF D] eq_reflection[OF add_assoc[OF yN mult_N[OF yN D] M]]
        eq_reflection[OF IH] eq_reflection[OF add_comm[OF yN d]] eq_reflection[OF sub_add[OF xN yN yx]]
      by (rule natD[OF xN])
  qed
qed

end
