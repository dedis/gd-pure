// =====================================================
// The inductive datatype chapter. Formalizes required
// number theory to be able to express cantor pairings.
// Then, writes a package that encodes arbitrary data-
// types into the formalized integers.
// =====================================================

#import "../style.typ": definition-box
#import "../formalisms.typ": *
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#show: codly-init.with()
#codly(zebra-fill: none)

= Encoding Inductive Datatypes in GD
<inductive>
With _Isabelle/GD_ now being a more convenient proof assistant, the next goal is to make it easier to extend the domain of discourse beyond just natural numbers. Modern proof assistants, like _Isabelle/HOL_ or Rocq, contain fancy definitional mechanisms that allow for easy definition of things like inductive datatypes, recursive predicates, infinitary sets, and so on.

These definitional packages are effectively _theory compilers_, as they take a simple high-level definition, like an inductive datatype declaration, and map it to definitions, axioms, and automatically proven lemmas, encoding the high-level definition in lower-level existing primitives.

The goal of this chapter is to take the key steps towards such a definitional mechanism for inductive datatypes in _Isabelle/GA_ and encode them into the existing natural number theory. That is, any inductive datatype should be definable and conveniently usable without adding any axioms.

The roadmap towards this lofty goal is as follows:

- Formalize enough basic number theory to be able to define cantor pairings and the key properties about them.
- Manually encode an inductive datatype into the natural numbers using the cantor pairing infrastructure from the first step. Define a type membership predicate, define the constructors as cantor pairings of their arguments and prove the necessary lemmas (such as all constructors being disjoint, the type membership predicate returning true for all values of the constructors, induction over the datatype, and so on).
- Plan out a semantic type system embedded within the single syntactic type of `num` in _Pure_ and introduce tooling for it.
- Write a definitional package that parses an inductive datatype declaration and compiles it into the necessary definitions, lemmas, and accompanying proofs.

== Next
- cantor pairing formalization; cantor pairing and projection functions recursive formalizations and mutual termination proofs; key theorems
- add some key theorems for arithmetic that were proven, or at least give a number to get an idea.

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
