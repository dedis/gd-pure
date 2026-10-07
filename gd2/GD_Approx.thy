theory GD_Approx
  imports GD_Arith
begin

text \<open>
  Is approx still needed, now that gd_def is definitional?  It is not
  derivable in general, and it is what partial correctness rests on.  Three
  cases show where the line is.

  (1) Productive divergence: no approx needed.  If every unfolding step
      produces part of the result (an S), a value would have to be infinitely
      large, and ordinary induction on the value refutes it: ups below.

  (2) Termination by a measure: no approx needed.  The fuel bound comes from
      the measure, so approx is derivable (evn in GD_Def_Test).

  (3) Silent divergence: approx needed.  If the recursion can run forever
      without producing anything (a search that never succeeds, loop x \<equiv> loop x),
      the kernel has no rule saying that such a term has no value, and
      partial-correctness statements are not provable without approx.
      find_correct below is the example.

  Why find_correct is not provable without approx.  Equate every term with
  no head normal form (Omega, loop 0, find 4 below) with 0: in pure lambda
  calculus this is Barendregt's theory H, which is consistent, and the GD
  rules other than approx only ever relate terms through head steps
  (beta, condT/condF, unfolding) and through values, so they cannot tell an
  unsolvable term apart from 0 either.  In that reading find 4 = 0 and
  good 0 is false, so  find 4 N \<Longrightarrow> good (find 4)  fails.  approx rules this
  model out: it says a value must have been reached after finitely many
  unfoldings.  (This is an argument, not a formal proof: making it one means
  extending the consistency of H to GD's constants and quantifier.)
\<close>


section \<open>(1) Productive divergence, without approx\<close>

gd_def ups :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>ups x \<equiv> S (ups (S x))\<close>

lemma ups_value_E:
  assumes v: \<open>v N\<close> and h: \<open>ups x = v\<close>
  shows \<open>PROP R\<close>
  using v h
proof (induct v arbitrary: x)
  case (Base x)
  have e: \<open>S (ups (S x)) = 0\<close> using Base(1) unfolding ups_def[of x] .
  have n: \<open>ups (S x) N\<close> by (rule natSE, rule eq_natL[OF e])
  show "PROP ?case" by (rule exF[OF e sucNonZero[OF n]])
next
  case (Step w x)
  have e: \<open>S (ups (S x)) = S w\<close> using Step(3) unfolding ups_def[of x] .
  show "PROP ?case" by (rule Step(2)[inst_all, OF sucInj[OF e]])
qed

theorem ups_diverges: \<open>ups x N \<Longrightarrow> PROP R\<close>
  by (rule ups_value_E, assumption, rule natD)


section \<open>(3) Silent divergence: partial correctness needs approx\<close>

text \<open>A search for the first n with n * n = n + 6, starting anywhere.  From
  0 it finds 3; from 4 on it runs forever without producing anything.\<close>

gd_def good :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>good n \<equiv> n * n = n + 6\<close>

gd_def find :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>find n \<equiv> if good n then n else find (S n)\<close>

gd_approx find

lemma find_fuel_correct:
  assumes k: \<open>k N\<close> and h: \<open>find_fuel k n N\<close>
  shows \<open>good (find_fuel k n)\<close>
  using k h
proof (induct k arbitrary: n)
  case (Base n)
  have \<open>\<bottom> N\<close> using Base(1) unfolding find_fuel_def[of 0 n] condT[OF zero_eq] .
  then show ?case by (rule botE)
next
  case (Step j n)
  have e: \<open>find_fuel (S j) n \<equiv> if good n then n else find_fuel j (S n)\<close>
    unfolding find_fuel_def[of \<open>S j\<close> n] condF[OF sucNonZero[OF Step(1)]]
      eq_reflection[OF predSuc[OF Step(1)]]
    by (rule Pure.reflexive)
  show ?case unfolding e
  proof (rule cond_NE[OF Step(3)[unfolded e]])
    assume g: \<open>good n\<close> and \<open>n N\<close>
    show \<open>good (if good n then n else find_fuel j (S n))\<close> unfolding condT[OF g] by (rule g)
  next
    assume g: \<open>\<not> good n\<close> and v: \<open>find_fuel j (S n) N\<close>
    show \<open>good (if good n then n else find_fuel j (S n))\<close>
      unfolding condF[OF g] by (rule Step(2)[inst_all, OF v])
  qed
qed

theorem find_correct:
  assumes h: \<open>find n N\<close>
  shows \<open>good (find n)\<close>
proof (rule find_approx[OF h])
  fix k
  assume k: \<open>k N\<close> and e: \<open>find_fuel k n = find n\<close>
  have \<open>good (find_fuel k n)\<close> by (rule find_fuel_correct[OF k eq_natL[OF e]])
  then show \<open>good (find n)\<close> unfolding eq_reflection[OF e] .
qed

text \<open>The same proof gives  find n N \<Longrightarrow> 6 \<le> find n * find n  and any other
  property of the value; and for loop x \<equiv> loop x it gives  loop x N \<Longrightarrow> PROP R
  (GD_Def_Test).  None of these is provable without approx, by the argument
  above.  Total-correctness facts, on the other hand, do not need it:\<close>

lemma find_0: \<open>find 0 = 3\<close>
  by (simp add: find_def good_def)

end
