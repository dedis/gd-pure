// =====================================================
// The background chapter. Introduces the Isabelle Pure
// logic and Grounded Arithmetic.
// =====================================================

#import "../style.typ": definition-box
#import "../formalisms.typ": *

= Background

== Grounded Deduction (GD)

== Isabelle/Pure

Pure is the minimal meta-logic in Isabelle. The popular Isabelle/HOL fragment is formalized atop Pure, as are all other object logics in Isabelle. Aside from a bare-bones logic, Pure provides infrastructure to define datatypes and axioms to facilitate the formalization of object logics in it.
=== Syntax of Pure

The core syntax of Pure is a typed lambda calculus with type variables, universal quantification, equality, and implication. Propositions are terms of the distinct type `prop`. Propositions in Pure are thus terms and not types, like they are in type-theory based provers like Rocq or Lean.

#definition-box("Type Syntax")[
  #pure-types
]

#definition-box("Term Syntax")[
  #pure-terms
]

The symbols used for implication, equality, and universal quantification are non-standard to leave the standard symbols free for object logics atop Pure.

Even though Pure has type variables, it provides no construct to capture them as an argument, and thus also has no for-all type like the polymorphic lambda calculus System F.

=== Deduction Rules

The implication operator in Pure expresses logical entailment.The deduction rules for the implication and universal quantifier are unsurprising:

#definition-box("Implication Deduction Rules")[
  #pure-implication-rules
]

#definition-box("Universal Quantification Deduction Rules")[
  #pure-forall-rules
]

An object logic in Pure is created by adding new axioms, constants, and types.
