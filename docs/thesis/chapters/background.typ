// =====================================================
// The background chapter. Introduces the Isabelle Pure
// logic and Grounded Arithmetic.
// =====================================================

#import "../style.typ": definition-box
#import "../formalisms.typ": *

= Background

== Isabelle/Pure

Pure is the minimal meta-logic in Isabelle. The popular Isabelle/HOL fragment is formalized atop Pure, as are all other object logics in Isabelle. Pure is designed to be as generic as possible to allow implementing a wide range of object logics inside it. Aside from a bare-bones logic, Pure thus provides infrastructure to define types and axioms to facilitate the formalization of object logics in it.

Unfortunately, there is no single document that lays out the syntax, axioms, and derivation rules of Pure in its entirety. The following is an attempt at providing such a characterization of Pure, combining information from two Isabelle papers @isabelle00 @isabelle89 and the Isabelle reference manual @isabelle_ref.

=== Syntax of Pure

The core syntax of Pure is a typed lambda calculus, augmented with type variables, universal quantification, equality, and implication.

Propositions are terms of the distinct type `prop`. Propositions in Pure are thus terms and not types, like they are in type-theory based provers like Rocq or Lean.

#definition-box("Type Syntax")[
  #pure-types
]

#definition-box("Term Syntax")[
  #pure-terms
]

The symbols used for implication, equality, and universal quantification are non-standard to leave the standard symbols free for object logics atop Pure.

Even though Pure has type variables, it provides no construct to capture them as an argument, and thus also has no for-all type like the polymorphic lambda calculus System F.

=== Equality, Implication, and Quantification as Type Constructors

The connectives equality, implication, and universal quantification are all type constructors of the `prop` type with the following polymorphic type signatures.

#definition-box(none)[
  #pure-type-constructors
]

The arguments of $equiv$ are the two operands to compare, the arguments for $arrow.double.long$ are the sequent and consequent respectively, while the arguments of $and.big$ are the type whose inhabitants are quantified over and the term that represents the body of the quantifier.

Since type variables denote only a single, albeit arbitrary, type, there is technically one instance of each connective for every given type. For example, for any type $sigma$, there is a constant $equiv_sigma "":: sigma => sigma => "prop"$.

=== Deduction Rules

The operational semantics of the underlying lamdba calculus and its typing rules are standard and thus omitted. The following discusses the more interesting deduction rules.

Relative to an object logic with a set of defined axioms $Omega$, any axiom $omega in Omega$ can always be derived, as can any assumption $gamma in Gamma$.

#definition-box("Basic Rules")[
  #pure-basic-rules
]

The implication and universal quantification introduction and elimination rules are standard.

#definition-box("Implication Deduction Rules")[
  #pure-implication-rules
]

#definition-box("Universal Quantification Deduction Rules")[
  #pure-forall-rules
]

For equality, besides the expected deduction rules corresponding to the equivalence relation properties, there are also deduction rules for equality of lambda abstractions and `prop`, the latter of which is defined as equivalence of truth values ($a <=> b$).

#definition-box("Equality Deduction Rules")[
  #pure-equality-rules
]

The $lambda$-conversion rules facilitate equivalence reasoning for lambda abstractions. The rules are $alpha$-conversion, $beta$-conversion and extensionality. The notation $a[y\/x]$ expresses the substitution of $x$ with $y$ in $a$, that is, all occurences of $x$ in $a$ are replaced with $y$.

#definition-box("Lambda Conversion Rules")[
  #pure-lambda-conversion-rules
]

Finally, the equivalence elimination rule:

#definition-box("Equivalence Elimination")[
  #equiv-elimination-rule
]

=== Formalizing Object Logics in Pure

An object logic in Pure is created by adding new types, constants and axioms. That is, the Pure logic is extended.

// Object logic deduction rules are meta-level axioms.

// TODO put the typedef stuff here
// typedecl o
// judgement Trueprop :: <o => prop>
// axiomatization eq :: <['a, 'a] => o>
//   where refl: <a = a> and
//         subst: <a = b ==> P(a) ==> P(b)
// definition, abbreviation (latter typed - why?)

== Grounded Deduction (GD)
