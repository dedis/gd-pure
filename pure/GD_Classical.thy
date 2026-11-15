theory GD_Classical
  imports GD
begin

text \<open>
  Groundwork for proof automation. GD is paracomplete, so classical reasoning
  is not available in general --- but on formulas that are \<^emph>\<open>decided\<close> (\<open>p B\<close>)
  over terms that are \<^emph>\<open>grounded\<close> (\<open>a N\<close>) it is, because \<open>p B\<close> unfolds by
  definition to \<open>p \<or> \<not>p\<close>. This theory pins that down: the fragment is closed
  under the connectives, and the classical rules hold inside it.

  That is what would let an external first-order prover be used on a GD goal:
  its inferences are classical, so they are admissible exactly as far as this
  fragment reaches. Section 3 marks where it stops.
\<close>

section \<open>Closure of the decided fragment\<close>

text \<open>
  \<open>GD.thy\<close> proves the disjunction, conjunction and implication cases as
  anonymous \<open>[auto]\<close> rules. They are restated here under names, since a
  translation has to cite them.
\<close>

lemma eqB [auto]: "a N \<Longrightarrow> b N \<Longrightarrow> (a = b) B"
  by (rule eqBool)

lemma notB' [auto]: "p B \<Longrightarrow> (\<not>p) B"
  by (rule not_bool)

lemma disjB [auto]: "p B \<Longrightarrow> q B \<Longrightarrow> (p \<or> q) B"
  by auto

lemma conjB [auto]: "p B \<Longrightarrow> q B \<Longrightarrow> (p \<and> q) B"
  by auto

lemma implB [auto]: "p B \<Longrightarrow> q B \<Longrightarrow> (p \<longrightarrow> q) B"
  by auto

lemma iffB [auto]: "p B \<Longrightarrow> q B \<Longrightarrow> (p \<longleftrightarrow> q) B"
  unfolding iff_def by auto


section \<open>Classical reasoning inside it\<close>

lemma lem: "p B \<Longrightarrow> p \<or> \<not>p"
  unfolding bJudg_def by assumption

lemma classical: "p B \<Longrightarrow> (\<not>p \<Longrightarrow> p) \<Longrightarrow> p"
  by (rule cases_bool[where q="p"], assumption+)

lemma disj_syllogism: "p \<or> q \<Longrightarrow> \<not>p \<Longrightarrow> q"
  by (rule disjE1, assumption, rule exF, assumption+)

text \<open>De Morgan needs no decidedness --- both directions are primitive.\<close>

lemma deMorgan_disj: "\<not>(p \<or> q) \<Longrightarrow> \<not>p \<and> \<not>q"
  by (rule conjI, erule disjE2, erule disjE3)

lemma deMorgan_disj_rev: "\<not>p \<and> \<not>q \<Longrightarrow> \<not>(p \<or> q)"
  by (rule disjI3, erule conjE1, erule conjE2)

lemma deMorgan_conj: "\<not>(p \<and> q) \<Longrightarrow> \<not>p \<or> \<not>q"
  unfolding conj_def by (rule dNegE)

lemma deMorgan_conj_rev: "\<not>p \<or> \<not>q \<Longrightarrow> \<not>(p \<and> q)"
  unfolding conj_def by (rule dNegI)

text \<open>These do.\<close>

lemma hyp_syllogism:
  assumes p: "p B" and pq: "p \<longrightarrow> q" and qr: "q \<longrightarrow> r"
  shows "p \<longrightarrow> r"
proof (rule implI)
  show "p B" by (rule p)
next
  assume hp: "p"
  have hq: "q" using pq hp by (rule implE)
  show "r" using qr hq by (rule implE)
qed

lemma contrapos:
  assumes p: "p B" and q: "q B" and pq: "p \<longrightarrow> q"
  shows "\<not>q \<longrightarrow> \<not>p"
proof (rule implI)
  show "(\<not>q) B" using q by (rule not_bool)
next
  assume nq: "\<not>q"
  show "\<not>p"
  proof (rule cases_bool[where q="p"])
    show "p B" by (rule p)
  next
    assume hp: "p"
    have hq: "q" using pq hp by (rule implE)
    show "\<not>p" using hq nq by (rule exF)
  next
    assume "\<not>p" thus "\<not>p" .
  qed
qed

lemma peirce:
  assumes p: "p B" and q: "q B"
  shows "((p \<longrightarrow> q) \<longrightarrow> p) \<longrightarrow> p"
proof (rule implI)
  show "((p \<longrightarrow> q) \<longrightarrow> p) B" using p q by auto
next
  assume h: "(p \<longrightarrow> q) \<longrightarrow> p"
  show "p"
  proof (rule cases_bool[where q="p"])
    show "p B" by (rule p)
  next
    assume "p" thus "p" .
  next
    assume np: "\<not>p"
    have pq: "p \<longrightarrow> q"
    proof (rule implI)
      show "p B" by (rule p)
    next
      assume hp: "p"
      show "q" using hp np by (rule exF)
    qed
    show "p" using h pq by (rule implE)
  qed
qed


section \<open>Where the fragment stops\<close>

text \<open>
  It is not closed under quantification: \<open>(\<forall>x. Q x) B\<close> does not follow from
  pointwise \<open>\<And>x. x N \<Longrightarrow> (Q x) B\<close>. The only ways to prove a disjunction are
  \<open>disjI1\<close>, \<open>disjI2\<close>, \<open>disjE1\<close> from an existing one, and \<open>exF\<close>; for
  \<open>(\<forall>x. Q x) \<or> \<not>(\<forall>x. Q x)\<close> the first two would need the quantified formula
  or its negation already settled, and there is nothing to feed the others.
  Deciding it would mean deciding an infinite conjunction, which is the point
  of GD being paracomplete rather than an oversight.

  So the fragment where classical reasoning is licensed is the
  \<^emph>\<open>quantifier-free\<close> decided one. Quantifier rules still apply --- \<open>forallE\<close>,
  \<open>notForallI\<close> and \<open>notForallE\<close> need no decidedness, and quantifier De Morgan
  is primitive --- but a prover may not case-split on a quantified subformula.
\<close>

lemma all_elim_no_B: "\<forall>x. Q x \<Longrightarrow> a N \<Longrightarrow> Q a"
  by (rule forallE)

lemma not_all_no_B: "a N \<Longrightarrow> \<not>(Q a) \<Longrightarrow> \<not>(\<forall>x. Q x)"
  by (rule notForallI)

end
