theory GD_Def_Test
  imports GD_Core
begin

text \<open>Exercises every path of gd_def.  Expected results are in the comments.\<close>

text \<open>Single recursive definition: unfolding, fuel and approx axioms.\<close>

gd_def up :: "tm \<Rightarrow> tm \<Rightarrow> tm"
  where "up x y \<equiv> if x = y then 0 else S (up (S x) y)"

thm up_def up_raw_def
  (* up_def is a theorem; up_raw_def is the Pure definition of up as a component of fix *)

gd_approx up

thm up_def up_fuel_def up_approx
  (* up_fuel ?k ?x ?y \<equiv> if ?k = 0 then \<bottom> else (if ?x = ?y then 0 else S (up_fuel (P ?k) (S ?x) ?y)) *)

gd_def loop :: "tm \<Rightarrow> tm"
  where "loop x \<equiv> loop x"

gd_approx loop

thm loop_approx

text \<open>Mutual recursion: the block shares one fuel argument.\<close>

gd_def evn :: "tm \<Rightarrow> tm" and odd :: "tm \<Rightarrow> tm"
  where "evn x \<equiv> if x = 0 then 1 else odd (P x)"
    and "odd x \<equiv> if x = 0 then 0 else evn (P x)"

gd_fuel evn
  (* fuel versions only: the section below derives approx for evn without the axiom *)

thm evn_fuel_def odd_fuel_def

section \<open>Parity fuel bounds proved without approximation axioms\<close>

text \<open>
  These proofs use the four unfolding equations, natural-number induction,
  and the core equality/conditional rules. Neither evn_approx nor odd_approx
  is used. For natural x, the explicit fuel bound is S x.
\<close>

lemma parity_zero_eq: "0 = 0"
  using nat0 unfolding isNat_def .

lemma evn_zero_unfold: "evn 0 \<equiv> 1"
  using evn_def[of 0] unfolding condT[OF parity_zero_eq] .

lemma odd_zero_unfold: "odd 0 \<equiv> 0"
  using odd_def[of 0] unfolding condT[OF parity_zero_eq] .

lemma evn_suc_unfold:
  assumes x: "x N"
  shows "evn (S x) \<equiv> odd x"
  using evn_def[of "S x"]
  unfolding condF[OF sucNonZero[OF x]] eq_reflection[OF predSuc[OF x]] .

lemma odd_suc_unfold:
  assumes x: "x N"
  shows "odd (S x) \<equiv> evn x"
  using odd_def[of "S x"]
  unfolding condF[OF sucNonZero[OF x]] eq_reflection[OF predSuc[OF x]] .

lemma evn_fuel_zero_unfold:
  assumes k: "k N"
  shows "evn_fuel (S k) 0 \<equiv> 1"
  using evn_fuel_def[of "S k" 0]
  unfolding condF[OF sucNonZero[OF k]] condT[OF parity_zero_eq] .

lemma odd_fuel_zero_unfold:
  assumes k: "k N"
  shows "odd_fuel (S k) 0 \<equiv> 0"
  using odd_fuel_def[of "S k" 0]
  unfolding condF[OF sucNonZero[OF k]] condT[OF parity_zero_eq] .

lemma evn_fuel_suc_unfold:
  assumes k: "k N" and x: "x N"
  shows "evn_fuel (S k) (S x) \<equiv> odd_fuel k x"
  using evn_fuel_def[of "S k" "S x"]
  unfolding condF[OF sucNonZero[OF k]] condF[OF sucNonZero[OF x]]
    eq_reflection[OF predSuc[OF k]] eq_reflection[OF predSuc[OF x]] .

lemma odd_fuel_suc_unfold:
  assumes k: "k N" and x: "x N"
  shows "odd_fuel (S k) (S x) \<equiv> evn_fuel k x"
  using odd_fuel_def[of "S k" "S x"]
  unfolding condF[OF sucNonZero[OF k]] condF[OF sucNonZero[OF x]]
    eq_reflection[OF predSuc[OF k]] eq_reflection[OF predSuc[OF x]] .

definition parity_fuel_property :: "tm \<Rightarrow> prop" where
  "parity_fuel_property x \<equiv>
    ((evn_fuel (S x) x = evn x) &&& (odd_fuel (S x) x = odd x))"

lemma parity_fuel_property_nat:
  assumes x: "x N"
  shows "PROP parity_fuel_property x"
proof (rule ind[OF x])
  have e: "evn_fuel (S 0) 0 = evn 0"
    unfolding evn_fuel_zero_unfold[OF nat0] evn_zero_unfold
    using natS[OF nat0] unfolding isNat_def .
  have o: "odd_fuel (S 0) 0 = odd 0"
    unfolding odd_fuel_zero_unfold[OF nat0] odd_zero_unfold
    by (rule parity_zero_eq)
  show "PROP parity_fuel_property 0"
    unfolding parity_fuel_property_def by (rule e, rule o)
next
  fix n
  assume n: "n N" and hyp: "PROP parity_fuel_property n"
  note ih = hyp[unfolded parity_fuel_property_def]
  have e: "evn_fuel (S (S n)) (S n) = evn (S n)"
    unfolding evn_fuel_suc_unfold[OF natS[OF n] n] evn_suc_unfold[OF n]
    by (rule Pure.conjunctionD2[OF ih])
  have o: "odd_fuel (S (S n)) (S n) = odd (S n)"
    unfolding odd_fuel_suc_unfold[OF natS[OF n] n] odd_suc_unfold[OF n]
    by (rule Pure.conjunctionD1[OF ih])
  show "PROP parity_fuel_property (S n)"
    unfolding parity_fuel_property_def by (rule e, rule o)
qed

lemma evn_fuel_exact:
  assumes x: "x N"
  shows "evn_fuel (S x) x = evn x"
  by (rule Pure.conjunctionD1[OF parity_fuel_property_nat[OF x, unfolded parity_fuel_property_def]])

lemma odd_fuel_exact:
  assumes x: "x N"
  shows "odd_fuel (S x) x = odd x"
  by (rule Pure.conjunctionD2[OF parity_fuel_property_nat[OF x, unfolded parity_fuel_property_def]])

lemma evn_input_nat:
  assumes terminated: "evn x N"
  shows "x N"
proof -
  have value: "(if x = 0 then 1 else odd (P x)) N"
    using terminated unfolding evn_def[of x] .
  have decided: "(x = 0) B" by (rule condE[OF value])
  have alternatives: "(x = 0) \<or> \<not> (x = 0)"
    using decided unfolding isBool_def .
  show "x N"
  proof (rule disjE1[OF alternatives])
    assume eq: "x = 0"
    show "x N" by (rule eq_natL[OF eq])
  next
    assume neq: "\<not> (x = 0)"
    show "x N" by (rule neqE1[OF neq])
  qed
qed

theorem evn_fuel_when_terminates:
  "evn x N \<Longrightarrow> evn_fuel (S x) x = evn x"
  by (rule evn_fuel_exact, rule evn_input_nat, assumption)

theorem evn_approx_proved:
  assumes terminated: "evn x N"
    and use_fuel: "\<And>k. k N \<Longrightarrow> evn_fuel k x = evn x \<Longrightarrow> PROP R"
  shows "PROP R"
proof (rule use_fuel[where k="S x"])
  show "S x N" by (rule natS[OF evn_input_nat[OF terminated]])
  show "evn_fuel (S x) x = evn x"
    by (rule evn_fuel_when_terminates[OF terminated])
qed

section \<open>What approx adds: loop\<close>

text \<open>
  For evn the fuel bound comes from a termination measure, so approx is
  derivable.  For loop there is no measure: loop x N is the only information.
  With loop_approx, loop x N is contradictory for every x.  Without it we do
  not know a proof: no rule concludes that a term has no value except botE.
\<close>

lemma loop_fuel_bot:
  assumes k: "k N"
  shows "loop_fuel k x \<equiv> \<bottom>"
proof (rule ind[where Q="\<lambda>j. (loop_fuel j x \<equiv> \<bottom>)", OF k])
  show "loop_fuel 0 x \<equiv> \<bottom>"
    using loop_fuel_def[of 0 x] unfolding condT[OF parity_zero_eq] .
next
  fix j
  assume j: "j N" and ih: "loop_fuel j x \<equiv> \<bottom>"
  show "loop_fuel (S j) x \<equiv> \<bottom>"
    using loop_fuel_def[of "S j" x]
    unfolding condF[OF sucNonZero[OF j]] eq_reflection[OF predSuc[OF j]] ih .
qed

lemma loop_no_value:
  assumes v: "loop x N"
  shows "PROP R"
proof (rule loop_approx[OF v])
  fix k
  assume k: "k N" and eq: "loop_fuel k x = loop x"
  have "\<bottom> N"
    using eq_natL[OF eq] unfolding loop_fuel_bot[OF k] .
  then show "PROP R" by (rule botE)
qed

lemma "loop 0 N \<Longrightarrow> loop 0 = S (S (S (S (S 0))))"
  by (rule loop_no_value)


text \<open>
  Mutual recursion goes in one block.  Splitting it (h calling a declared g,
  g defined later in terms of h) would be a cyclic definition, which Pure
  rejects; this is why gd_decl is gone.
\<close>

gd_def h :: "tm \<Rightarrow> tm" and g :: "tm \<Rightarrow> tm"
  where "h x \<equiv> if x = 0 then 0 else g (P x)"
    and "g x \<equiv> h x"

thm h_def g_def

text \<open>Recursion under \<forall>: accepted with its unfolding equation, but a warning
  and no approx axiom (condition A5).\<close>

gd_def w :: "tm \<Rightarrow> tm"
  where "w x \<equiv> if x = 0 then (\<forall>n. w (S n) = 1) else if x = 1 then 1 else w (P x)"

thm w_def

(* gd_approx w  -- rejected: not finitary (A5) *)

print_gd_defs

text \<open>Each of these must be rejected\<close>

(* A2: pattern on the left
gd_def bad1 :: "tm \<Rightarrow> tm" where "bad1 (P x) \<equiv> x"
*)

(* A2: repeated variable
gd_def bad2 :: "tm \<Rightarrow> tm \<Rightarrow> tm" where "bad2 x x \<equiv> x"
*)

(* A3: variable only on the right
gd_def bad3 :: "tm \<Rightarrow> tm" where "bad3 x \<equiv> y"
*)

(* A4: two equations
gd_def bad4 :: "tm \<Rightarrow> tm" where "bad4 x \<equiv> 0" and "bad4 x \<equiv> 1"
*)

(* A1: an equation for a constant not declared in the block
gd_def bad0 :: "tm \<Rightarrow> tm" where "bad0 x \<equiv> 0" and "up x y \<equiv> 0"
*)

(* redefining an existing constant (rejected by Pure: duplicate declaration)
gd_def up :: "tm \<Rightarrow> tm \<Rightarrow> tm" where "up x y \<equiv> 0"
*)

(* A1: higher-order type
gd_def bad5 :: "(tm \<Rightarrow> tm) \<Rightarrow> tm" where "bad5 F \<equiv> F 0"
*)


text \<open>
  This is an intentionally adversarial test of gd_def, not a library result.
  The helper parameter is named fn: h is already a constant in this theory.
  No extra axiomatization, sorry, or oracle is used. The return value v
  generalizes the original example (v = 1); using v = 0 as well yields
  an actual contradiction.
\<close>

definition roll :: "tm \<Rightarrow> tm \<Rightarrow> tm" where
  "roll v fn \<equiv> \<Lambda> n. if n = 0 then v else fn \<cdot> P n"

definition sweep :: "tm \<Rightarrow> tm \<Rightarrow> tm" where
  "sweep v fn \<equiv> \<forall>n. fn \<cdot> n = v"

gd_def walk :: "tm \<Rightarrow> tm" and total :: "tm \<Rightarrow> tm"
  where "walk v \<equiv> roll v (walk v)"
    and "total v \<equiv> sweep v (walk v)"

text \<open>The revised A5 rejects approximation for these helpers.\<close>

(*
thm walk_approx total_approx

lemma audit_meta_cong:
  assumes eq: "a \<equiv> b"
  shows "F a \<equiv> F b"
  unfolding eq by (rule reflexive)

lemma audit_zero_eq: "0 = 0"
  using nat0 unfolding isNat_def .

lemma audit_walk_step:
  "walk v \<cdot> n \<equiv> if n = 0 then v else walk v \<cdot> P n"
  using audit_meta_cong[OF walk_def[of v], where F="\<lambda>fn. fn \<cdot> n"]
  unfolding roll_def beta .

lemma audit_walk_value:
  assumes v: "v N" and n: "n N"
  shows "walk v \<cdot> n = v"
proof (rule ind[OF n])
  show "walk v \<cdot> 0 = v"
    unfolding audit_walk_step[of v 0] condT[OF audit_zero_eq]
    using v unfolding isNat_def .
next
  fix x
  assume x: "x N" and ih: "walk v \<cdot> x = v"
  show "walk v \<cdot> S x = v"
    unfolding audit_walk_step[of v "S x"] condF[OF sucNonZero[OF x]]
      eq_reflection[OF predSuc[OF x]] by (rule ih)
qed

lemma audit_total_true:
  assumes v: "v N"
  shows "total v"
  unfolding total_def sweep_def
  by (rule forallI, rule audit_walk_value[OF v], assumption)

lemma audit_fuel_zero: "walk_fuel 0 v \<equiv> \<bottom>"
  using walk_fuel_def[of 0 v] unfolding condT[OF audit_zero_eq] .

lemma audit_fuel_suc:
  assumes k: "k N"
  shows "walk_fuel (S k) v \<equiv> roll v (walk_fuel k v)"
  using walk_fuel_def[of "S k" v]
  unfolding condF[OF sucNonZero[OF k]] eq_reflection[OF predSuc[OF k]] .

lemma audit_diagonal:
  assumes k: "k N"
  shows "walk_fuel k v \<cdot> k \<equiv> \<bottom> \<cdot> 0"
proof (rule ind[OF k])
  show "walk_fuel 0 v \<cdot> 0 \<equiv> \<bottom> \<cdot> 0"
    unfolding audit_fuel_zero by (rule reflexive)
next
  fix x
  assume x: "x N" and ih: "walk_fuel x v \<cdot> x \<equiv> \<bottom> \<cdot> 0"
  show "walk_fuel (S x) v \<cdot> S x \<equiv> \<bottom> \<cdot> 0"
    unfolding audit_fuel_suc[OF x] roll_def beta condF[OF sucNonZero[OF x]]
      eq_reflection[OF predSuc[OF x]] by (rule ih)
qed

lemma audit_total_fuel_zero: "total_fuel 0 v \<equiv> \<bottom>"
  using total_fuel_def[of 0 v] unfolding condT[OF audit_zero_eq] .

lemma audit_total_fuel_suc:
  assumes k: "k N"
  shows "total_fuel (S k) v \<equiv> sweep v (walk_fuel k v)"
  using total_fuel_def[of "S k" v]
  unfolding condF[OF sucNonZero[OF k]] eq_reflection[OF predSuc[OF k]] .

lemma audit_finite_fuel_consequence:
  assumes k: "k N"
  shows "total_fuel k v = 1 \<Longrightarrow> \<bottom> \<cdot> 0 = v"
proof (rule ind[where Q="\<lambda>j. (total_fuel j v = 1 \<Longrightarrow> \<bottom> \<cdot> 0 = v)", OF k])
  assume val: "total_fuel 0 v = 1"
  have "\<bottom> N" using eq_natL[OF val] unfolding audit_total_fuel_zero .
  then show "\<bottom> \<cdot> 0 = v" by (rule botE)
next
  fix x
  assume x: "x N"
  assume ih: "total_fuel x v = 1 \<Longrightarrow> \<bottom> \<cdot> 0 = v"
  assume val: "total_fuel (S x) v = 1"
  have all: "\<forall>n. walk_fuel x v \<cdot> n = v"
    using trueI[OF val] unfolding audit_total_fuel_suc[OF x] sweep_def .
  have "walk_fuel x v \<cdot> x = v" by (rule forallE[OF all x])
  then show "\<bottom> \<cdot> 0 = v" unfolding audit_diagonal[OF x] .
qed

theorem audit_bottom_application:
  assumes v: "v N"
  shows "\<bottom> \<cdot> 0 = v"
proof (rule total_approx[OF eq_natL[OF trueE[OF audit_total_true[OF v]]]])
  fix k
  assume k: "k N" and val: "total_fuel k v = total v"
  have "total_fuel k v = 1"
    using val unfolding eq_reflection[OF trueE[OF audit_total_true[OF v]]] .
  then show "\<bottom> \<cdot> 0 = v" by (rule audit_finite_fuel_consequence[OF k])
qed

lemma audit_one_zero: "1 = 0"
  by (rule eq_trans[OF eqSym[OF audit_bottom_application[OF natS[OF nat0]]]
        audit_bottom_application[OF nat0]])

theorem audit_contradiction: "PROP R"
  by (rule exF[OF audit_one_zero sucNonZero[OF nat0]])

text \<open>
  Both 1 = 0 and its negation are now theorems. Thus the currently accepted
  approximation schemes are inconsistent, independently of theory merging.
  This file must not be treated as a sound library until the issue is fixed.
\<close>

*)

end
