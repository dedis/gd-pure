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

With Isabelle/GD now being a slightly more convenient proof assistant, the next goal is to make it easier to extend the domain of discourse. Modern proof assistants, like Isabelle/HOL, contain fancy definitional mechanisms that allow for easy definition of things like inductive datatypes, recursive predicates, infinitary sets, and so on.

These definitional packages are effectively _theory compilers_, as they take a simple high-level definition, like an inductive datatype declaration, and map it to definitions, axioms, and automatically proven lemmas, encoding the high-level definition in lower level existing primitives.

The  goal of this chapter is to provide a definitional mechanism for inductive datatypes in Isabelle/GD and encode them under the hood into the existing formalization of natural numbers. That is, any inductive datatype should be definable and conveniently usable without adding any axioms.

The roadmap towards this lofty goal is as follows:

- Formalize enough basic number theory to be able to define cantor pairings and some basic properties about them.
- Manually encode an inductive datatype. Define a type membership predicate, define the constructors as cantor pairings of their arguments and prove the necessary lemmas (such as all constructors being disjoint, the type membership predicate returning true for all values of the constructors, induction over the datatype, and so on).
- Write a definitional package that parses an inductive datatype declaration and compiles it into the necessary definitions, lemmas, and accompanying proofs.
