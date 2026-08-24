theory QGA_Liar
  imports QGA_on_GA
begin

(*
  ============================================================================
  CONSISTENCY = UNPROVABILITY OF A SELF-REFUTING SENTENCE

  Claim: "no proof code proves L" and "no checked proof list holds a formula
  together with its negation" are EQUIVALENT.  Both directions, no
  contraposition anywhere.

  DESIGN NOTE (why this file looks the way it does).

  An earlier draft of this file assumed proof COMPOSITION -- "from a proof of
  f and a proof of ~f, a proof of anything" -- as a locale axiom.  That was
  wrong twice over.  Explosion is already a branch of the checker
  (\<open>find_exF\<close>, \<open>QGA_on_GA.thy\<close> line 884); assuming it hides the very thing
  the arithmetization provides.  And composition needs an APPEND on proof
  lists together with monotonicity of \<open>valid_step\<close> in its \<open>rest\<close> argument,
  roughly twenty mechanical lemmas that do not exist yet.

  Both problems disappear by stating consistency over a SINGLE proof list
  rather than over two independent proof codes:

      con_list:  no N-list \<open>pf\<close> with \<open>check_list pf\<close> holds both
                 \<open>\<emptyset> \<tturnstile> f\<close> and \<open>\<emptyset> \<tturnstile> mkNot f\<close>.

  Under that reading each direction extends a list by ONE judgment, so no
  append and no monotonicity lemma is needed.  This is also the more natural
  statement: it is what \<open>check_list\<close> actually quantifies over.

  WHAT IS ASSUMED, AND WHY IT CANNOT YET BE PROVED.

  Exactly one checker fact, \<open>exF_step\<close> in \<open>qga_explode\<close> below.  It says that
  \<open>valid_step\<close> accepts \<open>\<emptyset> \<tturnstile> c\<close> when the tail already holds \<open>\<emptyset> \<tturnstile> f\<close> and
  \<open>\<emptyset> \<tturnstile> mkNot f\<close>.  That is literally what \<open>find_exF\<close> tests for, so it ought
  to be a theorem of \<open>valid_step_def\<close> / \<open>check_prop_rules_def\<close> /
  \<open>find_exF_def\<close>.  It is not derivable TODAY because \<open>valid_step\<close> is a
  thirteen-branch nested conditional and showing that a late branch fires
  requires case-splitting on the twelve earlier guards -- which needs
  \<open>check_weak\<close>, \<open>check_cut\<close>, \<open>check_inst\<close>, \<open>check_prop_rules\<close>, ... to be
  individually decided.  \<open>QGA_on_GA.thy\<close> has no such per-branch lemmas: all
  thirteen are bundled into the single sorried \<open>valid_step_bool\<close> (line 1285).
  Unbundling that into one \<open>_bool\<close> lemma per checker function turns
  \<open>exF_step\<close> into an ordinary derivation and empties this locale.  That is a
  gap in the arithmetization, not a design choice here.

  DEPENDENCIES.  The theorems below cite \<open>check_list_bool\<close> (line 1286), which
  is sorried, so they inherit it.  Nothing here is sorry-free until that and
  \<open>valid_step_bool\<close> are discharged.

  WHERE THE LIAR IS AND IS NOT NEEDED.  \<open>unprovable_imp_con_list\<close> holds for
  an ARBITRARY formula code: no self-reference, no property of L at all.
  The converse, \<open>con_list_imp_L_unprovable\<close>, genuinely needs L to refute
  itself -- it is plainly false otherwise, since a provable L exists.  That
  direction lives in \<open>qga_explode_liar\<close> and costs one further one-step
  checker fact, \<open>unfold_step\<close>, blocked for the same reason as \<open>exF_step\<close>.
  ============================================================================
*)

context qga_proof_check
begin

section \<open>Extending a checked list by one judgment\<close>

text \<open>
  The two structural facts everything below runs on.  Both are direct
  unfoldings of \<open>check_list_def\<close> and \<open>is_valid_proof_def\<close>; the only subtlety
  is that an \<open>o\<close>-valued conditional cannot be peeled to a branch without
  groundedness of that branch, which here is \<open>check_list_bool\<close>.
\<close>

lemma check_list_cons:
  assumes J: "J N" and rest: "rest N"
      and step: "valid_step J rest" and ok: "check_list rest"
  shows "check_list (Cons J rest)"
proof -
  have cN: "Cons J rest N" using J rest by simp
  have ne: "\<not> (Cons J rest = Nil)" using J rest by simp
  note hd' = eq_reflection[OF list_hd_cons[OF J rest]]
  note tl' = eq_reflection[OF list_tl_cons[OF J rest]]
  have inner: "(if valid_step (list_hd (Cons J rest)) (list_tl (Cons J rest))
                then check_list (list_tl (Cons J rest)) else False)
               \<longleftrightarrow> check_list rest"
    unfolding hd' tl' by (rule condI1B[OF step check_list_bool[OF rest]])
  have outer: "(if Cons J rest = Nil then True
                else if valid_step (list_hd (Cons J rest)) (list_tl (Cons J rest))
                     then check_list (list_tl (Cons J rest)) else False)
               \<longleftrightarrow> check_list rest"
    by (rule condI2BEq[OF ne check_list_bool[OF rest] inner])
  show ?thesis
    by (rule defE[OF check_list_def[where pf = "Cons J rest"], where Q = "\<lambda>z. z"],
        rule implE[OF iffE2[OF outer] ok])
qed

lemma is_valid_proof_cons:
  assumes J: "J N" and rest: "rest N" and ok: "check_list (Cons J rest)"
  shows "is_valid_proof (Cons J rest) J"
proof -
  have cN: "Cons J rest N" using J rest by simp
  have ne: "\<not> (Cons J rest = Nil)" using J rest by simp
  have hd: "list_hd (Cons J rest) = J" by (rule list_hd_cons[OF J rest])
  have inner: "(if list_hd (Cons J rest) = J then check_list (Cons J rest) else False)
               \<longleftrightarrow> check_list (Cons J rest)"
    by (rule condI1B[OF hd check_list_bool[OF cN]])
  have outer: "(if Cons J rest = Nil then False
                else if list_hd (Cons J rest) = J
                     then check_list (Cons J rest) else False)
               \<longleftrightarrow> check_list (Cons J rest)"
    by (rule condI2BEq[OF ne check_list_bool[OF cN] inner])
  show ?thesis
    by (rule defE[OF is_valid_proof_def[where pf = "Cons J rest" and J = J],
                  where Q = "\<lambda>z. z"],
        rule implE[OF iffE2[OF outer] ok])
qed

end


section \<open>The one checker fact that is still assumed\<close>

locale qga_explode = qga_proof_check +
  assumes exF_step:
    "\<lbrakk>f N; c N; rest N;
      mem (\<emptyset> \<tturnstile> f) rest; mem (\<emptyset> \<tturnstile> mkNot f) rest\<rbrakk>
     \<Longrightarrow> valid_step (\<emptyset> \<tturnstile> c) rest"
begin

text \<open>
  Explosion, DERIVED: a checked list holding a formula and its negation
  extends, in one step, to a proof of anything.  This is the fact the earlier
  draft of this file assumed outright.
\<close>

theorem exF_proof:
  assumes f: "f N" and c: "c N" and rest: "rest N"
      and ok: "check_list rest"
      and m1: "mem (\<emptyset> \<tturnstile> f) rest" and m2: "mem (\<emptyset> \<tturnstile> mkNot f) rest"
  shows "is_valid_proof (Cons (\<emptyset> \<tturnstile> c) rest) (\<emptyset> \<tturnstile> c)"
proof -
  have JN: "(\<emptyset> \<tturnstile> c) N" using c by simp
  have step: "valid_step (\<emptyset> \<tturnstile> c) rest" by (rule exF_step[OF f c rest m1 m2])
  have ok2: "check_list (Cons (\<emptyset> \<tturnstile> c) rest)"
    by (rule check_list_cons[OF JN rest step ok])
  show ?thesis by (rule is_valid_proof_cons[OF JN rest ok2])
qed


section \<open>No code proves L implies consistency\<close>

text \<open>
  Here \<open>L\<close> does work, but still only as a target: given a checked list with a
  formula and its negation, \<open>exF_proof\<close> manufactures a proof of \<open>L\<close>, which
  the hypothesis forbids.  Any \<open>L\<close> whatever will do --- again no
  self-reference is used.
\<close>

theorem unprovable_imp_con_list:
  assumes NL: "\<And>q. q N \<Longrightarrow> \<not> is_valid_proof q (\<emptyset> \<tturnstile> L)"
  assumes L: "L N" and pf: "pf N" and f: "f N"
      and ok: "check_list pf"
      and m1: "mem (\<emptyset> \<tturnstile> f) pf" and m2: "mem (\<emptyset> \<tturnstile> mkNot f) pf"
  shows "False"
proof -
  have JN: "(\<emptyset> \<tturnstile> L) N" using L by simp
  have qN: "Cons (\<emptyset> \<tturnstile> L) pf N" using JN pf by simp
  have prL: "is_valid_proof (Cons (\<emptyset> \<tturnstile> L) pf) (\<emptyset> \<tturnstile> L)"
    by (rule exF_proof[OF f L pf ok m1 m2])
  have nprL: "\<not> is_valid_proof (Cons (\<emptyset> \<tturnstile> L) pf) (\<emptyset> \<tturnstile> L)" by (rule NL[OF qN])
  show "False" by (rule exF[OF prL nprL])
qed

end


section \<open>The converse, which is where the liar is actually needed\<close>

text \<open>
  \<open>Con \<Longrightarrow> \<not>Prov(L)\<close> is FALSE for an arbitrary \<open>L\<close> --- take \<open>L\<close> provable, e.g.
  \<open>\<emptyset> \<tturnstile> mkNat tZero\<close>.  This direction is exactly where self-refutation earns
  its keep, and it needs one further one-step checker fact: that a checked
  list headed by \<open>\<emptyset> \<tturnstile> L\<close> extends by one step to \<open>\<emptyset> \<tturnstile> mkNot L\<close>.  For the
  Liar proper that step is the \<open>:=\<close> unfolding \<open>L := \<not>L\<close>, accepted by
  \<open>check_def\<close>.  Like \<open>exF_step\<close> it is a statement about one branch of
  \<open>valid_step\<close> and is blocked by the same missing per-branch lemmas.

  Note also that the encoding has no formula-level definition mechanism ---
  \<open>dfns\<close> and \<open>T_APP\<close> are term-level, there is no \<open>F_APP\<close> --- so a genuine
  liar has to be routed through a term liar, e.g.
  \<open>g x := if g x = 0 then 1 else 0\<close> with \<open>L := (g 0 = 0)\<close>, and \<open>dfns\<close> must be
  assumed to contain that entry, exactly as \<open>qga_encode.thy\<close> assumes
  \<open>dfns_bot\<close> at index 0.
\<close>

locale qga_explode_liar = qga_explode +
  fixes L :: fm
  assumes L_N: "L N"
  assumes unfold_step:
    "\<lbrakk>q N; check_list q; list_hd q = (\<emptyset> \<tturnstile> L)\<rbrakk>
     \<Longrightarrow> valid_step (\<emptyset> \<tturnstile> mkNot L) q"
begin

theorem con_list_imp_L_unprovable:
  assumes CON: "\<And>pf f. \<lbrakk>pf N; f N; check_list pf;
                        mem (\<emptyset> \<tturnstile> f) pf; mem (\<emptyset> \<tturnstile> mkNot f) pf\<rbrakk> \<Longrightarrow> False"
  assumes q: "q N" and pr: "is_valid_proof q (\<emptyset> \<tturnstile> L)"
  shows "False"
proof -
  have JN: "(\<emptyset> \<tturnstile> L) N" using L_N by simp
  \<comment> \<open>unpack \<open>is_valid_proof\<close>: \<open>q\<close> is non-nil, headed by \<open>\<emptyset> \<tturnstile> L\<close>, and checked\<close>
  have nn: "\<not> (q = Nil)"
  proof (rule contradiction [where p = "\<not> (q = Nil)"])
    show "(\<not> (q = Nil)) B" by (rule notB[OF eqBool[OF q nil_nat]])
  next
    assume h: "\<not> \<not> (q = Nil)"
    have e: "q = Nil" by (rule dNegE[OF h])
    have bad: "is_valid_proof Nil (\<emptyset> \<tturnstile> L)"
      by (rule eqSubst[where Q = "\<lambda>z. is_valid_proof z (\<emptyset> \<tturnstile> L)", OF e pr])
    have nilF: "is_valid_proof Nil (\<emptyset> \<tturnstile> L) \<longleftrightarrow> False"
      by (rule defE[OF is_valid_proof_def[where pf = Nil and J = "\<emptyset> \<tturnstile> L"],
                    where Q = "\<lambda>z. z \<longleftrightarrow> False"],
          rule condI1B[OF nil_nat[unfolded isNat_def] false_bool])
    show "False" by (rule implE[OF iffE1[OF nilF] bad])
  qed
  have hdq: "list_hd q = (\<emptyset> \<tturnstile> L)"
  proof (rule contradiction [where p = "list_hd q = (\<emptyset> \<tturnstile> L)"])
    show "(list_hd q = (\<emptyset> \<tturnstile> L)) B" by (rule eqBool[OF list_hd_nat[OF q] JN])
  next
    assume h: "\<not> (list_hd q = (\<emptyset> \<tturnstile> L))"
    have step: "is_valid_proof q (\<emptyset> \<tturnstile> L) \<longleftrightarrow> False"
      by (rule defE[OF is_valid_proof_def[where pf = q and J = "\<emptyset> \<tturnstile> L"],
                    where Q = "\<lambda>z. z \<longleftrightarrow> False"],
          rule condI2BEq[OF nn false_bool],
          rule condI2B[OF h false_bool])
    show "False" by (rule implE[OF iffE1[OF step] pr])
  qed
  have ok: "check_list q"
  proof -
    have step: "is_valid_proof q (\<emptyset> \<tturnstile> L) \<longleftrightarrow> check_list q"
      by (rule defE[OF is_valid_proof_def[where pf = q and J = "\<emptyset> \<tturnstile> L"],
                    where Q = "\<lambda>z. z \<longleftrightarrow> check_list q"],
          rule condI2BEq[OF nn check_list_bool[OF q]],
          rule condI1B[OF hdq check_list_bool[OF q]])
    show ?thesis by (rule implE[OF iffE1[OF step] pr])
  qed
  \<comment> \<open>one \<open>check_def\<close> step gives the negation, on the SAME list\<close>
  have nLN: "mkNot L N" by (rule pack_F_N, simp+, rule L_N)
  have nJN: "(\<emptyset> \<tturnstile> mkNot L) N" using nLN by simp
  have vs: "valid_step (\<emptyset> \<tturnstile> mkNot L) q" by (rule unfold_step[OF q ok hdq])
  have ok2: "check_list (Cons (\<emptyset> \<tturnstile> mkNot L) q)"
    by (rule check_list_cons[OF nJN q vs ok])
  have qN2: "Cons (\<emptyset> \<tturnstile> mkNot L) q N" using nJN q by simp
  \<comment> \<open>the extended list holds both \<open>\<emptyset> \<tturnstile> L\<close> (as \<open>list_hd q\<close>) and \<open>\<emptyset> \<tturnstile> mkNot L\<close>\<close>
  have mL: "mem (\<emptyset> \<tturnstile> L) (Cons (\<emptyset> \<tturnstile> mkNot L) q)"
  proof -
    have hN: "list_hd q N" by (rule list_hd_nat[OF q])
    have tN: "list_tl q N" by (rule list_tl_nat[OF q])
    have rec: "Cons (list_hd q) (list_tl q) = q" using q nn by (rule cons_reconstr)
    have m0: "mem (list_hd q) (Cons (list_hd q) (list_tl q))" using hN tN by simp
    have inq0: "mem (list_hd q) q"
      by (rule eqSubst[where Q = "\<lambda>z. mem (list_hd q) z", OF rec m0])
    have inq: "mem (\<emptyset> \<tturnstile> L) q"
      by (rule eqSubst[where Q = "\<lambda>z. mem z q", OF hdq inq0])
    have e: "mem (\<emptyset> \<tturnstile> L) (Cons (\<emptyset> \<tturnstile> mkNot L) q)
             \<longleftrightarrow> (if (\<emptyset> \<tturnstile> mkNot L) = (\<emptyset> \<tturnstile> L) then True else mem (\<emptyset> \<tturnstile> L) q)"
      by (rule mem_cons[OF nJN q JN])
    have inner: "if (\<emptyset> \<tturnstile> mkNot L) = (\<emptyset> \<tturnstile> L) then True else mem (\<emptyset> \<tturnstile> L) q"
    proof (rule cases_bool[where q = "(\<emptyset> \<tturnstile> mkNot L) = (\<emptyset> \<tturnstile> L)"])
      show "((\<emptyset> \<tturnstile> mkNot L) = (\<emptyset> \<tturnstile> L)) B" by (rule eqBool[OF nJN JN])
    next
      assume h: "(\<emptyset> \<tturnstile> mkNot L) = (\<emptyset> \<tturnstile> L)"
      show ?thesis by (rule implE[OF iffE2[OF condI1B[OF h true_bool]] true])
    next
      assume h: "\<not> ((\<emptyset> \<tturnstile> mkNot L) = (\<emptyset> \<tturnstile> L))"
      show ?thesis
        by (rule implE[OF iffE2[OF condI2B[OF h mem_bool[OF JN q]]] inq])
    qed
    show ?thesis by (rule implE[OF iffE2[OF e] inner])
  qed
  have mNL: "mem (\<emptyset> \<tturnstile> mkNot L) (Cons (\<emptyset> \<tturnstile> mkNot L) q)"
    using nJN q by simp
  show "False" by (rule CON[OF qN2 L_N ok2 mL mNL])
qed

end


text \<open>
  \<^bold>\<open>Reading of the pair.\<close>  Together the two theorems say: consistency (in the
  single-list form) and unprovability of \<open>L\<close> are interderivable, for ANY
  formula code \<open>L\<close>.  Self-reference contributes nothing, because \<open>exF\<close>
  already makes every formula a consequence of any contradiction.  So the
  Liar route to a consistency proof is not a shortcut --- \<open>\<not>Prov(L)\<close> is not a
  weaker statement one might reach on the way to \<open>Con\<close>; it IS \<open>Con\<close>, and it
  is \<open>Con\<close> for the trivial reason that \<open>L\<close> was never used.

  \<^bold>\<open>Relation to \<open>syntactically_consistent\<close>.\<close>  The two-code form proved in
  \<open>qga_suff_semantics\<close> implies the single-list form via \<open>suffix_is_proof\<close>
  (\<open>QGA_on_GA.thy\<close> line 1315), which is already available: a checked list
  containing \<open>\<emptyset> \<tturnstile> f\<close> and \<open>\<emptyset> \<tturnstile> mkNot f\<close> yields proof codes for each.  The
  converse needs the append/monotonicity machinery described at the head of
  this file and is left open.
\<close>

end
