theory GD_Data
  imports GD_Arith
begin

text \<open>
  Pairs: an opt-in extension of the kernel (like GD_ATI), adding
  S-expressions to the values.  Without it there are no data structures with
  case analysis: a lambda-encoded list cannot be inspected (no rule tells a
  term that behaves like nil apart from one that is nil), and a numeric
  encoding is unusable with unary numerals.

  Model (extends M2 of GD_Core).  A new kind of value, the pair \<langle>a, b\<rangle> of two
  unevaluated terms: pairs are lazy, like lam.
    fst t, snd t : head-evaluate t to \<langle>a, b\<rangle>, then evaluate a (resp. b);
                   no value otherwise;
    ispair t     : 1 if t evaluates to a pair, 0 if to a numeral, no value
                   otherwise (in particular for lam);
  Numerals, =, S, P and the conditional are unchanged, so S \<langle>a, b\<rangle>,
  \<langle>a, b\<rangle> = c and  if \<langle>a, b\<rangle> then ...  have no value.

  Data.  t D (defined below) holds when t evaluates to a finite tree whose
  leaves are numerals.  data_induct is induction on that tree; it is the
  counterpart of ind and is sound for the same reason (t is ~ its value,
  O3, and the meta-level induction runs over the finite tree).

  Axioms: the three computation rules are head steps (O4); data_induct is
  the only new principle.
\<close>

axiomatization
  pair   :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (\<open>\<langle>_,/ _\<rangle>\<close>) and
  fst    :: \<open>tm \<Rightarrow> tm\<close> and
  snd    :: \<open>tm \<Rightarrow> tm\<close> and
  ispair :: \<open>tm \<Rightarrow> tm\<close>
where
  fst_pair [simp]:    \<open>fst \<langle>a, b\<rangle> \<equiv> a\<close> and                     (* O4 *)
  snd_pair [simp]:    \<open>snd \<langle>a, b\<rangle> \<equiv> b\<close> and                     (* O4 *)
  ispair_pair [simp]: \<open>ispair \<langle>a, b\<rangle> \<equiv> 1\<close> and                  (* a pair is a value *)
  ispair_N:           \<open>n N \<Longrightarrow> ispair n = 0\<close>                    (* n ~ its numeral, O3 *)

lemma ispair_N_eq [simp]: \<open>n N \<Longrightarrow> ispair n \<equiv> 0\<close>
  by (rule eq_reflection, rule ispair_N)

gd_def isData :: \<open>tm \<Rightarrow> tm\<close>  (\<open>_ D\<close> [21] 20)
  where \<open>x D \<equiv> if ispair x then (fst x D) \<and> (snd x D) else (x N)\<close>

axiomatization where
  data_induct [case_names HQ Num Pair]:
    \<open>\<lbrakk>x D;
      \<And>n. n N \<Longrightarrow> PROP Q n;
      \<And>a b. a D \<Longrightarrow> b D \<Longrightarrow> PROP Q a \<Longrightarrow> PROP Q b \<Longrightarrow> PROP Q \<langle>a, b\<rangle>\<rbrakk>
     \<Longrightarrow> PROP Q x\<close>


section \<open>Basic facts\<close>

lemma data_N [auto]:
  assumes n: \<open>n N\<close>
  shows \<open>n D\<close>
  unfolding isData_def[of n] eq_reflection[OF ispair_N[OF n]] condF[OF zero_false] by (rule n)

lemma data_pair [auto]:
  assumes a: \<open>a D\<close> and b: \<open>b D\<close>
  shows \<open>\<langle>a, b\<rangle> D\<close>
  unfolding isData_def[of \<open>\<langle>a, b\<rangle>\<close>] ispair_pair condT[OF one_true] fst_pair snd_pair
  by (rule conjI[OF a b])

lemma data_pair_E:
  assumes h: \<open>\<langle>a, b\<rangle> D\<close>
  shows \<open>a D\<close> and \<open>b D\<close>
proof -
  have c: \<open>(a D) \<and> (b D)\<close>
    using h unfolding isData_def[of \<open>\<langle>a, b\<rangle>\<close>] ispair_pair condT[OF one_true] fst_pair snd_pair .
  show \<open>a D\<close> by (rule conjE1[OF c])
  show \<open>b D\<close> by (rule conjE2[OF c])
qed

lemma data_cases [case_names HQ Num Pair]:
  assumes x: \<open>x D\<close>
  shows \<open>(x N \<Longrightarrow> PROP R) \<Longrightarrow> (\<And>a b. a D \<Longrightarrow> b D \<Longrightarrow> x \<equiv> \<langle>a, b\<rangle> \<Longrightarrow> PROP R) \<Longrightarrow> PROP R\<close>
proof (rule data_induct[where Q=\<open>\<lambda>y. ((y N \<Longrightarrow> PROP R) \<Longrightarrow>
    (\<And>a b. a D \<Longrightarrow> b D \<Longrightarrow> y \<equiv> \<langle>a, b\<rangle> \<Longrightarrow> PROP R) \<Longrightarrow> PROP R)\<close>, OF x])
  fix n
  assume n: \<open>n N\<close>
  assume h: \<open>n N \<Longrightarrow> PROP R\<close>
  show \<open>PROP R\<close> by (rule h[OF n])
next
  fix a b
  assume a: \<open>a D\<close> and b: \<open>b D\<close>
  assume h: \<open>\<And>c d. c D \<Longrightarrow> d D \<Longrightarrow> \<langle>a, b\<rangle> \<equiv> \<langle>c, d\<rangle> \<Longrightarrow> PROP R\<close>
  show \<open>PROP R\<close> by (rule h[inst_all, OF a b], rule Pure.reflexive)
qed

lemma ispair_B [auto]:
  assumes x: \<open>x D\<close>
  shows \<open>(ispair x) B\<close>
  using x
proof (rule data_cases)
  assume \<open>x N\<close>
  then show \<open>(ispair x) B\<close> by simp
next
  fix a b
  assume \<open>a D\<close> \<open>b D\<close> and e: \<open>x \<equiv> \<langle>a, b\<rangle>\<close>
  show \<open>(ispair x) B\<close> unfolding e by simp
qed

text \<open>Surjective pairing for data.\<close>

lemma pair_eta:
  assumes x: \<open>x D\<close> and p: \<open>ispair x\<close>
  shows \<open>x \<equiv> \<langle>fst x, snd x\<rangle>\<close>
  using x
proof (rule data_cases)
  assume n: \<open>x N\<close>
  have \<open>0\<close> using n p by simp
  then show \<open>x \<equiv> \<langle>fst x, snd x\<rangle>\<close> by (rule false_elim)
next
  fix a b
  assume \<open>a D\<close> \<open>b D\<close> and e: \<open>x \<equiv> \<langle>a, b\<rangle>\<close>
  show \<open>x \<equiv> \<langle>fst x, snd x\<rangle>\<close> unfolding e by simp
qed

lemma not_ispair_N:
  assumes x: \<open>x D\<close> and p: \<open>\<not> ispair x\<close>
  shows \<open>x N\<close>
  using x
proof (rule data_cases)
  assume \<open>x N\<close>
  then show \<open>x N\<close> .
next
  fix a b
  assume \<open>a D\<close> \<open>b D\<close> and e: \<open>x \<equiv> \<langle>a, b\<rangle>\<close>
  have \<open>0\<close> using p unfolding e by simp
  then show \<open>x N\<close> by (rule false_elim)
qed


section \<open>Size and strong induction on data\<close>

text \<open>data_induct gives induction hypotheses for the two components of a pair
  only.  Constructors that nest pairs (a tree node is \<langle>l, \<langle>v, r\<rangle>\<rangle>) need them
  for deeper parts, so here is course-of-values induction on the size.\<close>

gd_def dsize :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>dsize x \<equiv> if ispair x then S (dsize (fst x) + dsize (snd x)) else 0\<close>

lemma dsize_num [simp]: \<open>n N \<Longrightarrow> dsize n \<equiv> 0\<close>
  using dsize_def[of n] by simp

lemma dsize_pair [simp]: \<open>dsize \<langle>a, b\<rangle> \<equiv> S (dsize a + dsize b)\<close>
  using dsize_def[of \<open>\<langle>a, b\<rangle>\<close>] by simp

lemma dsize_N [auto]:
  assumes x: \<open>x D\<close>
  shows \<open>dsize x N\<close>
  using x
proof (rule data_induct)
  fix n
  assume \<open>n N\<close>
  then show \<open>dsize n N\<close> by simp
next
  fix a b
  assume \<open>a D\<close> \<open>b D\<close> and \<open>dsize a N\<close> \<open>dsize b N\<close>
  then show \<open>dsize \<langle>a, b\<rangle> N\<close> by simp
qed

lemma dsize_fst:
  assumes a: \<open>a D\<close> and b: \<open>b D\<close>
  shows \<open>dsize a < dsize \<langle>a, b\<rangle> = 1\<close>
  unfolding dsize_pair
  by (rule leq_imp_less_S[OF dsize_N[OF a] add_N[OF dsize_N[OF a] dsize_N[OF b]]
        leq_add[OF dsize_N[OF a] dsize_N[OF b]]])

lemma dsize_snd:
  assumes a: \<open>a D\<close> and b: \<open>b D\<close>
  shows \<open>dsize b < dsize \<langle>a, b\<rangle> = 1\<close>
  unfolding dsize_pair eq_reflection[OF add_comm[OF dsize_N[OF a] dsize_N[OF b]]]
  by (rule leq_imp_less_S[OF dsize_N[OF b] add_N[OF dsize_N[OF b] dsize_N[OF a]]
        leq_add[OF dsize_N[OF b] dsize_N[OF a]]])

lemma data_strong_induct [case_names HQ Step]:
  assumes x: \<open>x D\<close>
    and step: \<open>\<And>y. y D \<Longrightarrow> (\<And>z. z D \<Longrightarrow> dsize z < dsize y = 1 \<Longrightarrow> PROP Q z) \<Longrightarrow> PROP Q y\<close>
  shows \<open>PROP Q x\<close>
proof -
  have H: \<open>PROP Q y\<close> if n: \<open>n N\<close> and y: \<open>y D\<close> and e: \<open>dsize y = n\<close> for n y
    using n y e
  proof (induct less n arbitrary: y)
    case (Step n y)
    show \<open>PROP Q y\<close>
    proof (rule step[inst_all, OF Step(3)])
      fix z
      assume z: \<open>z D\<close> and lt: \<open>dsize z < dsize y = 1\<close>
      have lt': \<open>dsize z < n = 1\<close> using lt unfolding eq_reflection[OF Step(4)] .
      show \<open>PROP Q z\<close>
        by (rule Step(2)[inst_all, OF dsize_N[OF z] lt' z natD[OF dsize_N[OF z]]])
    qed
  qed
  show \<open>PROP Q x\<close> by (rule H[OF dsize_N[OF x] x natD[OF dsize_N[OF x]]])
qed

end
