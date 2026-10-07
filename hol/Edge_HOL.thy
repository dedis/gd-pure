theory Edge_HOL
  imports Main
begin

text \<open>
  The programs of gd2/GD_Edge.thy, attempted in Isabelle/HOL with the
  standard tools: function (with and without domintros), partial_function
  (option and tailrec modes), and the wfrec combinator.  Attempts that HOL
  rejects are kept as comments, with the error Isabelle2025-2 reports.

  Summary
    1. Self-application: not expressible.  The term does not type-check, and
       the datatype that would make it typable is rejected.
    2. Open recursion over an arbitrary functional: partial_function rejects
       it (monotonicity), function accepts it but its domain is empty, so no
       equation about it is ever usable.  wfrec works, for a well-founded
       relation fixed in the definition, with the unfolding equation
       conditional on an admissibility property of F.
    3. Nested recursion: works, with function (domintros), a partial
       correctness lemma under the domain predicate, and a separate
       termination proof that uses it; or with partial_function (option),
       at the price of an option-valued function.
\<close>


section \<open>1. Recursion by self-application\<close>

text \<open>
  GD: SELF \<equiv> \<Lambda> k. \<Lambda> n. if n = 0 then 1 else n * (k \<cdot> k \<cdot> (P n)),
      and SELF \<cdot> SELF \<cdot> n = fact n by induction.

    definition SELF where
      "SELF = (\<lambda>k n. if n = 0 then 1 else n * k k (n - 1 :: nat))"

      *** Type unification failed: Occurs check!
      *** Type error in application: operator not of function type
      *** Operator:  k :: ??'a
      *** Operand:   k :: ??'a

  The usual way to make k k typable is a recursive type T = T \<Rightarrow> nat \<Rightarrow> nat:

    datatype self = Self "self \<Rightarrow> nat \<Rightarrow> nat"

      *** Inadmissible recursive occurrence of type "self" in type expression
      ***   "self \<Rightarrow> nat \<Rightarrow> nat"

  (HOLCF's domain package accepts such a type with continuous functions,
  but then every function involved has to be shown continuous, and the
  result lives in a lifted type, not in nat.)
\<close>


section \<open>2. Open recursion\<close>

text \<open>
  GD: rec F x \<equiv> F \<cdot> (\<Lambda> y. rec F y) \<cdot> x  for every F, and
      rec_N: if F k x N whenever k y N for all y < x, then rec F x N.

  partial_function needs the body to be monotone in the recursive call.  For
  an arbitrary F that is unprovable, in either mode:

    partial_function (option) recf ::
        "((nat \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> nat option"
      where "recf F x = F (recf F) x"

      *** Proof failed.
      ***  1. \<And>x a b. monotone option.le_fun option_ord (\<lambda>recf. a (\<lambda>y. recf (a, y)) b)

    partial_function (tailrec) recf ::
        "((nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
      where "recf F x = F (recf F) x"

      *** Proof failed.
      ***  1. \<And>x a b. monotone tailrec.le_fun tailrec_ord (\<lambda>recf. a (\<lambda>y. recf (a, y)) b)

  The function package accepts the definition, but it cannot see where F
  calls the recursion, so it assumes F may call it on every argument:
\<close>

function (domintros) recf :: \<open>((nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>recf F x = F (recf F) x\<close>
  by auto

text \<open>
  recf.domintros is  (\<And>y. recf_dom (F, y)) \<Longrightarrow> recf_dom (F, x),  so the
  domain is empty, and recf.psimps (recf_dom (F, x) \<Longrightarrow> recf F x = ...) never
  applies.  Nothing can be proved about recf, not even for F = FACTF below.
\<close>

lemma recf_dom_empty: \<open>\<not> recf_dom (F, x)\<close>
proof
  assume \<open>recf_dom (F, x)\<close>
  then show False by (induct rule: recf.pinduct) blast
qed

text \<open>
  What works is to fix a well-founded relation in the definition.  wfrec
  hands F the recursion cut down to the arguments below x; outside them F
  sees undefined.
\<close>

definition recw :: \<open>((nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a\<close>
  where \<open>recw F = wfrec less_than F\<close>

lemma recw_unfold: \<open>recw F x = F (cut (recw F) less_than x) x\<close>
  unfolding recw_def by (rule wfrec[OF wf_less_than])

text \<open>
  The equation  recw F = F (recw F)  holds only for F that ignore their
  argument outside the region below x (adm_wf).  This is HOL's counterpart of
  rec_N, with the difference that the relation is part of the definition,
  so an F that recurses some other way is not covered at all.
\<close>

lemma recw_fixpoint: \<open>adm_wf less_than F \<Longrightarrow> recw F = F (recw F)\<close>
  unfolding recw_def by (rule wfrec_fixpoint[OF wf_less_than])

fun fac :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>fac 0 = 1\<close>
| \<open>fac (Suc n) = Suc n * fac n\<close>

definition FACTF :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>FACTF r n = (if n = 0 then 1 else n * r (n - 1))\<close>

lemma recw_fac: \<open>recw FACTF n = fac n\<close>
proof (induct n)
  case 0
  show ?case by (subst recw_unfold) (simp add: FACTF_def)
next
  case (Suc n)
  show ?case by (subst recw_unfold) (simp add: FACTF_def cut_apply Suc)
qed


section \<open>3. Nested recursion\<close>

text \<open>
  The recipe of the function package tutorial (section "Nested recursion"):
  define with domintros, prove the result under the domain predicate by
  partial induction, then prove termination using that lemma.
\<close>

function (domintros) nz :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>nz 0 = 0\<close>
| \<open>nz (Suc n) = nz (nz n)\<close>
  by pat_completeness auto

lemma nz_is_zero:
  assumes trm: \<open>nz_dom n\<close>
  shows \<open>nz n = 0\<close>
  using trm by induct (auto simp: nz.psimps)

termination nz
  by (relation \<open>less_than\<close>) (auto simp: nz_is_zero)

lemma nz_zero: \<open>nz n = 0\<close>
  by (induct n) simp_all

function (domintros) nid :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>nid 0 = 0\<close>
| \<open>nid (Suc n) = Suc (nid (nid n))\<close>
  by pat_completeness auto

lemma nid_is_id:
  assumes trm: \<open>nid_dom n\<close>
  shows \<open>nid n = n\<close>
  using trm by induct (auto simp: nid.psimps)

termination nid
  by (relation \<open>less_than\<close>) (auto simp: nid_is_id)

lemma nid_id: \<open>nid n = n\<close>
  by (induct n) simp_all

text \<open>
  The alternative is partial_function (option), which needs no termination
  proof but changes the type: every caller of nzo has to go through bind.
\<close>

partial_function (option) nzo :: \<open>nat \<Rightarrow> nat option\<close>
  where \<open>nzo n = (if n = 0 then Some 0 else Option.bind (nzo (n - 1)) nzo)\<close>

lemma nzo_0: \<open>nzo 0 = Some 0\<close>
  by (subst nzo.simps) simp

lemma nzo_zero: \<open>nzo n = Some 0\<close>
proof (induct n)
  case 0
  show ?case by (rule nzo_0)
next
  case (Suc n)
  show ?case by (subst nzo.simps) (simp add: Suc nzo_0)
qed

end
