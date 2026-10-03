theory GD_Arith
  imports GD_Base
begin

text \<open>
  Port of the arithmetic section of pure/GD.thy, first slice: the
  definitions, their computation rules, termination (habeas quid) lemmas, and
  the basic algebra of + and \<le>.  div is defined but its termination proof
  needs strong induction, which is not ported yet.

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

end
