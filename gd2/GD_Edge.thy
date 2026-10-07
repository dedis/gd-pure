theory GD_Edge
  imports GD_Arith
begin

text \<open>
  Three kinds of recursive program, chosen to separate GD from HOL and Lean.

  1. Recursion by self-application (k \<cdot> k).  Not typable in HOL or Lean, so
     not expressible there at all.
  2. Open recursion: a recursion combinator rec over an arbitrary functional
     F, with an unconditional unfolding equation and a generic termination
     theorem stated with habeas quid.  HOL has the combinator only for a
     well-founded relation fixed in advance (wfrec), with the unfolding
     equation conditional on an admissibility proof; its definitional
     packages reject or trivialise it.
  3. Nested recursion, where termination depends on the function's own
     result.  HOL handles these with function (domintros) plus a separate
     termination proof that reasons under the domain predicate; here
     termination is a corollary of the correctness proof.

  None of the definitions below needed a termination argument to be stated,
  and nothing in this file uses an approx axiom.
\<close>


section \<open>Factorial, the reference function\<close>

gd_def fact :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>fact n \<equiv> if n = 0 then 1 else n * fact (P n)\<close>

lemma fact_0: \<open>fact 0 \<equiv> 1\<close>
  using fact_def[of 0] unfolding condT[OF zero_eq] .

lemma fact_S:
  assumes m: \<open>m N\<close>
  shows \<open>fact (S m) \<equiv> S m * fact m\<close>
  using fact_def[of \<open>S m\<close>] unfolding condF[OF sucNonZero[OF m]] eq_reflection[OF predSuc[OF m]] .

lemma fact_N [auto]:
  assumes n: \<open>n N\<close>
  shows \<open>fact n N\<close>
  using n
proof (induct n)
  case Base
  show ?case unfolding fact_0 by (rule one_N)
next
  case (Step m)
  show ?case unfolding fact_S[OF Step(1)] by (rule mult_N[OF natS[OF Step(1)] Step(2)])
qed


section \<open>1. Recursion by self-application\<close>

text \<open>
  The function receives itself as its first argument and recurses by
  applying that argument to itself.  No name refers to SELF in its own
  definition, so this is an ordinary Pure definition; the recursion lives
  entirely in the term k \<cdot> k.  In HOL the body does not type-check
  (k would need a type T with T = T \<Rightarrow> ...), and a datatype with that
  constructor is rejected (negative occurrence).  Lean rejects it for the
  same reason.
\<close>

definition SELF :: \<open>tm\<close> where
  \<open>SELF \<equiv> \<Lambda> k. \<Lambda> n. if n = 0 then 1 else n * (k \<cdot> k \<cdot> (P n))\<close>

lemma SELF_app: \<open>SELF \<cdot> k \<cdot> n \<equiv> if n = 0 then 1 else n * (k \<cdot> k \<cdot> (P n))\<close>
  unfolding SELF_def beta by (rule Pure.reflexive)

theorem SELF_fact:
  assumes n: \<open>n N\<close>
  shows \<open>SELF \<cdot> SELF \<cdot> n = fact n\<close>
  using n
proof (induct n)
  case Base
  show ?case
    unfolding SELF_app[of SELF 0] condT[OF zero_eq] fact_0 by (rule natD[OF one_N])
next
  case (Step m)
  show ?case
    unfolding SELF_app[of SELF \<open>S m\<close>] condF[OF sucNonZero[OF Step(1)]]
      eq_reflection[OF predSuc[OF Step(1)]] eq_reflection[OF Step(2)] fact_S[OF Step(1)]
    by (rule natD[OF mult_N[OF natS[OF Step(1)] fact_N[OF Step(1)]]])
qed

corollary SELF_N: \<open>n N \<Longrightarrow> SELF \<cdot> SELF \<cdot> n N\<close>
  by (rule eq_natL, rule SELF_fact)


section \<open>2. Open recursion\<close>

text \<open>
  rec F x calls the functional F with the recursion itself as an object
  function.  The definition is accepted for every F, including ones that
  never terminate; rec_def holds unconditionally.
\<close>

gd_def rec :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>
  where \<open>rec F x \<equiv> F \<cdot> (\<Lambda> y. rec F y) \<cdot> x\<close>

text \<open>
  A generic termination theorem.  The hypothesis says: if the recursion
  argument k returns a number on every y below x, then F k x returns a
  number.  It does not ask F to be monotone or continuous, or to leave k
  alone outside the region below x: a call to k elsewhere would simply have
  no value, and the hypothesis would then not be provable for that F.
  Habeas quid (k \<cdot> y N) does the work that a domain predicate, an option
  type or a well-founded relation fixed in advance does in HOL.
\<close>

theorem rec_N:
  assumes total: \<open>\<And>k x. x N \<Longrightarrow> (\<And>y. y N \<Longrightarrow> y < x = 1 \<Longrightarrow> k \<cdot> y N) \<Longrightarrow> F \<cdot> k \<cdot> x N\<close>
    and x: \<open>x N\<close>
  shows \<open>rec F x N\<close>
  using x
proof (induct less x)
  case (Step x)
  have e: \<open>rec F x \<equiv> F \<cdot> (\<Lambda> y. rec F y) \<cdot> x\<close> by (rule rec_def)
  show ?case unfolding e
  proof (rule total[inst_all, OF Step(1)])
    fix y
    assume y: \<open>y N\<close> and yx: \<open>y < x = 1\<close>
    show \<open>(\<Lambda> y. rec F y) \<cdot> y N\<close> unfolding beta by (rule Step(2)[inst_all, OF y yx])
  qed
qed

text \<open>An instance: factorial as a functional.\<close>

definition FACTF :: \<open>tm\<close> where
  \<open>FACTF \<equiv> \<Lambda> k. \<Lambda> n. if n = 0 then 1 else n * (k \<cdot> (P n))\<close>

lemma FACTF_app: \<open>FACTF \<cdot> k \<cdot> n \<equiv> if n = 0 then 1 else n * (k \<cdot> (P n))\<close>
  unfolding FACTF_def beta by (rule Pure.reflexive)

text \<open>Termination from the generic theorem: only the local step is checked.\<close>

theorem rec_FACTF_N:
  assumes n: \<open>n N\<close>
  shows \<open>rec FACTF n N\<close>
proof (rule rec_N)
  fix k x
  assume x: \<open>x N\<close> and hk: \<open>\<And>y. y N \<Longrightarrow> y < x = 1 \<Longrightarrow> k \<cdot> y N\<close>
  show \<open>FACTF \<cdot> k \<cdot> x N\<close> unfolding FACTF_app
  proof (rule nat_cases[OF x])
    assume e: \<open>x = 0\<close>
    show \<open>(if x = 0 then 1 else x * (k \<cdot> (P x))) N\<close>
      unfolding eq_reflection[OF e] condT[OF zero_eq] by (rule one_N)
  next
    fix b
    assume b: \<open>b N\<close> and e: \<open>x = S b\<close>
    have kb: \<open>k \<cdot> b N\<close> by (rule hk[inst_all, OF b], unfold eq_reflection[OF e], rule less_S_self[OF b])
    show \<open>(if x = 0 then 1 else x * (k \<cdot> (P x))) N\<close>
      unfolding eq_reflection[OF e] condF[OF sucNonZero[OF b]] eq_reflection[OF predSuc[OF b]]
      by (rule mult_N[OF natS[OF b] kb])
  qed
next
  show \<open>n N\<close> by (rule n)
qed

text \<open>And the value, by ordinary induction.\<close>

theorem rec_FACTF:
  assumes n: \<open>n N\<close>
  shows \<open>rec FACTF n = fact n\<close>
  using n
proof (induct n)
  case Base
  show ?case
    unfolding rec_def[of FACTF 0] FACTF_app condT[OF zero_eq] fact_0 by (rule natD[OF one_N])
next
  case (Step m)
  show ?case
    unfolding rec_def[of FACTF \<open>S m\<close>] FACTF_app condF[OF sucNonZero[OF Step(1)]]
      eq_reflection[OF predSuc[OF Step(1)]] beta eq_reflection[OF Step(2)] fact_S[OF Step(1)]
    by (rule natD[OF mult_N[OF natS[OF Step(1)] fact_N[OF Step(1)]]])
qed


section \<open>3. Nested recursion\<close>

text \<open>
  The argument of the outer call is the result of an inner call, so a
  termination measure has to know what the function returns.  In HOL this
  is the standard example for function: first prove the result
  under the domain predicate by partial induction, then use it in a
  separate termination proof.  In Lean, well-founded recursion cannot see
  the inner result at all without changing the return type to a subtype.
  Here the value is proved by plain induction, and termination is the
  corollary eq_natL.
\<close>

gd_def z :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>z n \<equiv> if n = 0 then 0 else z (z (P n))\<close>

lemma z_0: \<open>z 0 \<equiv> 0\<close>
  using z_def[of 0] unfolding condT[OF zero_eq] .

lemma z_S:
  assumes m: \<open>m N\<close>
  shows \<open>z (S m) \<equiv> z (z m)\<close>
  using z_def[of \<open>S m\<close>] unfolding condF[OF sucNonZero[OF m]] eq_reflection[OF predSuc[OF m]] .

theorem z_zero:
  assumes n: \<open>n N\<close>
  shows \<open>z n = 0\<close>
  using n
proof (induct n)
  case Base
  show ?case unfolding z_0 by (rule zero_eq)
next
  case (Step m)
  show ?case unfolding z_S[OF Step(1)] eq_reflection[OF Step(2)] z_0 by (rule zero_eq)
qed

corollary z_N: \<open>n N \<Longrightarrow> z n N\<close>
  by (rule eq_natL, rule z_zero)

text \<open>Nested identity: nid (S m) = S (nid (nid m)).  Same shape, nonconstant result.\<close>

gd_def nid :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>nid n \<equiv> if n = 0 then 0 else S (nid (nid (P n)))\<close>

lemma nid_0: \<open>nid 0 \<equiv> 0\<close>
  using nid_def[of 0] unfolding condT[OF zero_eq] .

lemma nid_S:
  assumes m: \<open>m N\<close>
  shows \<open>nid (S m) \<equiv> S (nid (nid m))\<close>
  using nid_def[of \<open>S m\<close>] unfolding condF[OF sucNonZero[OF m]] eq_reflection[OF predSuc[OF m]] .

theorem nid_id:
  assumes n: \<open>n N\<close>
  shows \<open>nid n = n\<close>
  using n
proof (induct n)
  case Base
  show ?case unfolding nid_0 by (rule zero_eq)
next
  case (Step m)
  show ?case unfolding nid_S[OF Step(1)] eq_reflection[OF Step(2)]
    by (rule natD[OF natS[OF Step(1)]])
qed

end
