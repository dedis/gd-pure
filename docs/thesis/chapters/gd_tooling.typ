// =====================================================
// The tooling chapter. Tackles automation to make GD
// a usable proof assistant.
// =====================================================

#import "../style.typ": definition-box
#import "../formalisms.typ": *
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#show: codly-init.with()
#codly(zebra-fill: none)

= Tooling for Isabelle/GD

There are two main motivations for formalizing GD in Pure. On one hand, it enables studying GD reflectively in an instance of itself. On the other hand, having implemented GD in Pure, we have effectively obtained an interactive theorem prover based on the axioms of GD. In its current state however, Isabelle/GD is not a very usable theorem prover. There is no proof automation, no term rewriting, and no easy way to formalize higher level mathematics. Users can only reason about natural numbers and only use axioms or previously proven lemmas in their proofs.

This chapter aims for making Isabelle/GD more usable as a proof assistant and, towards that end, introduces a rewrite engine and a proof-search procedure for automating simple proofs, as well as a multitude of simpler methods to facilitate even fully manual reasoning.

As an initial motivation, here is how cumbersome a simple proof looks like in the current version of GD.

// TODO SCK: proof of leq_refl. Making use of induction,
// natural number case distinction, rewrites with eqSubst.
// Then, the following order
// 
// 1. unfold_def tac
// 2. cases tac
// 3. induct tac
// 4. rewrite engine (no more eqSubst everywhere)
// 5. auto rewrite engine with all gd_simp
// 6. rewrite engine with proof search wrapper: gd_auto

Before:
```Isabelle
lemma cons_is_list:
  assumes n_nat: "n N"
  assumes xs_list: "is_list xs"
  shows "is_list (Cons n xs)"
apply (rule eqSubst[where a="True"])
apply (unfold_def is_list_def)
apply (rule eqSym)
apply (rule condI2BEq)
apply (gd_auto)
apply (rule n_nat)
apply (rule list_nat)
apply (rule xs_list)
apply (gd_auto)
proof -
  show "(if Cons n xs = Cons n xs ∧ is_list xs ∧ (n N) then True else False) = True"
    apply (rule condI1B)
    apply (rule conjI)+
    apply (fold isNat_def)
    apply (rule cons_nat)
    apply (rule n_nat)
    apply (rule list_nat)
    apply (rule xs_list)
    apply (rule xs_list)
    apply (rule n_nat)
    apply (rule true_bool)
    done
  show "True" by (rule true)
qed
```

After:
```Isabelle
lemma cons_is_list [gd_auto]:
  shows "n N ⟹ xs N ⟹ is_list xs ⟹ is_list (Cons n xs)"
by (unfold_def is_list_def, simp)
```
