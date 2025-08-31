// =====================================================
// The background chapter. Introduces the Isabelle Pure
// logic and Grounded Arithmetic.
// =====================================================

#import "../style.typ": definition-box
#import "../formalisms.typ": *
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#show: codly-init.with()
#codly(zebra-fill: none)

= Background

== Isabelle/Pure
Isabelle provides a barebones logical framework called _Pure_. It contains a minimal meta-logic, which is a typed lambda calculus with few additional connectives, some keywords to add types and constants to said calculus, and a structured proof language called Isar.

Any object logic in Isabelle, for example the highly mature Isabelle/HOL fragment, are formalized atop Pure.

Isabelle is implemented in Standard ML (SML), and implementing an object logic directly in Pure almost always requires writing SML for things like proof automation, providing keywords or definitional mechanisms for users, or various other tooling such as code extraction.

Unfortunately, there is no single document that lays out the syntax, axioms, and derivation rules of the Pure calculus in their entirety. The following is an attempt at providing such a characterization, combining information from two Isabelle papers @isabelle00 @isabelle89 and the Isabelle reference manual @isabelle_ref.

=== Syntax of Pure

The core syntax of Pure is a typed lambda calculus, augmented with type variables, universal quantification, equality, and implication.

Propositions are terms of the distinct type `prop`. Propositions in Pure are thus terms and not types, like they are in type-theory based provers like Rocq or Lean.

#definition-box("Type Syntax")[
  #pure-types
]

#definition-box("Term Syntax")[
  #pure-terms
]

The symbols used for implication, equality, and universal quantification are non-standard to leave the standard symbols free for object logics.

Even though Pure has type variables, it provides no construct to capture them as an argument, and thus also has no for-all type like the polymorphic lambda calculus System F.

=== Equality, Implication, and Quantification as Type Constructors

The connectives equality, implication, and universal quantification are all type constructors of the `prop` type with the following polymorphic type signatures.

#definition-box(none)[
  #pure-type-constructors
]

The arguments of $equiv$ are the two operands to compare, the arguments for $arrow.double.long$ are the sequent and consequent respectively, while the argument of $and.big$ is a function from the type whose inhabitants are quantified over to the term that represents the body of the quantifier.

Since type variables denote only a single, albeit arbitrary, type, there is technically one instance of each polymorphic connective for every given type. For example, for any type $sigma$, there is a constant $equiv_sigma "":: sigma => sigma => "prop"$.

=== Deduction Rules

The operational semantics of the underlying lamdba calculus and its typing rules are standard and thus omitted. The following discusses the more interesting deduction rules, which make Pure a logical framework.

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

For equality, besides the expected deduction rules corresponding to the equivalence relation properties, there are also deduction rules for equality of lambda abstractions and `prop`, the latter of which is defined as equivalence of truth values ($a arrow.double.long b$ and $b arrow.double.long a$).

#definition-box("Equality Deduction Rules")[
  #pure-equality-rules
]

The $lambda$-conversion rules facilitate equivalence reasoning for lambda abstractions. The rules are $alpha$-conversion, $beta$-conversion and extensionality. The notation $a[y\/x]$ expresses the substitution of $x$ with $y$ in $a$, that is, all occurences of $x$ in $a$ are replaced with $y$.

#definition-box("Lambda Conversion Rules")[
  #pure-lambda-conversion-rules
]

Finally, the equivalence substitution rule:

#definition-box("Equivalence Elimination")[
  #equiv-elimination-rule
]

=== Formalizing Object Logics in Pure

An object logic in Pure is created by adding new types, constants and axioms. That is, the Pure logic is extended.

It is convention to define a new propositional type in an object logic, which is used as the type of propositions in the _object_ logic, as opposed to the _meta_ logic, which is Pure.

This is achieved using the $"typedecl"$ keyword, which declares a syntactic type in the Pure calculus. This type has no known inhabitants or any other information yet.

$ "typedecl" o $

Any information about $o$ must be axiomatized. For example, the following declares typed constants $"disj"$ and $"True"$ and axiomatizes certain rules about them.

```Isabelle
axiomatization
  True :: ‹o› and
  disj :: ‹o ⇒ o ⇒ o›  (infixr ‹∨› 30)
where
  true:   ‹True›
  disjI1: ‹P ⟹ P ∨ Q› and
  disjI2: ‹Q ⟹ P ∨ Q› and
```

The axiomatized rules here simply state that $"True"$ holds and that from either $P$ or $Q$, $P or Q$ can be derived. Here, $P$ and $Q$ are implicitly universally quantified, ranging over all terms of type `prop`. That is, $P$ and $Q$ can be substituted for any term of the correct type (which is `o` for both $P$ and $Q$ here).
Now, the type `o` has knows inhabitants and structure. However, Isabelle (or rather, Pure) cannot reason about it, because it cannot connect the type `o` meaningfully with its meta-theory. To resolve this, a judgment must translate from the object-level proposition type `o` to the meta-level type `prop`.

```Isabelle
judgment
  Trueprop :: ‹o ⇒ prop›  (‹_› 5)
```

The syntax annotation $(‹\_› med 5)$ means that any term of type `o` is implicitly augmented with the $"Trueprop"$
 judgment. The very low precedence value of 5 ensures that the $"Trueprop"$ judgment is only applied to top-level terms. For example, the term $x or "True"$ is the same as $"Trueprop" (x or "True")$ and both are of type `prop` due to the $"Trueprop"$ predicate converting the formula to that type.

As you might have noticed, we have made use of this implicit conversion from `o` to `Prop` already in the axiomatization block from earlier. That is, the $"Trueprop"$ judgment must be declared before the axiomatization block, else the latter will just report a typing error.

Now, we can state and prove a first lemma in this tiny object logic, using the previously defined axioms.

```Isabelle
lemma "x ∨ True"
apply (rule disjI2)
apply (rule true)
done
```

Applying $"disjI2"$ 'selects' the second disjunct to prove, which results in the subgoal $"True"$, which in turn we can solve using the $"true"$ axiom.

This short introduction suffices for now, as we will later implement a much richer logic, Grounded Deduction, using these same basic constructs. We can clearly see that implementing an object logic in Pure actually extends Pure, in the sense that it adds new types and deduction rules. For example, our extension added a type and three symbols to the existing syntax of Pure. If we call the tiny logic formalized above Pure', the following is its type and term syntax:

#definition-box("Type Syntax of Pure'")[
  #pure-prime-types
]

#definition-box("Term Syntax of Pure'")[
  #pure-prime-terms
]
 
Further, we can view the added axioms as new inference rules, with the explicit $"Trueprop"$ function application.

#definition-box(none)[
  #or-intro-rules
]

#definition-box(none)[
  #true-axiom
]

It is technically possible to avoid declaring a new proposition type for an object logic and instead use `prop` directly as the type of propositions. However, doing so means that the (object) logic immediately inherits the built-in connectives and deduction rules, such as implication $(arrow.long.double)$ and universal quantification $(and.big)$, and the sequent-style reasoning built into the kernel.

Such a structure reduces the control one has over the logic and keeps many reasoning principles implicit.

== Grounded Deduction (GD)

This subsection provides a full characterization of the GD logic that is later formalized.

GD makes definitions first-class objects in the logic and allows arbitrary references of the symbol currently being defined or other, previously defined symbols, in the expanded term.

To prevent immediate inconsistency, GD must weaken other deduction rules commonly seen in classical logic. Specifically, GD adds a so-called _habeas quid_ sequent to many inference rules. Intuitively, this means that in certain inference rules, a (sub)term must first be shown to terminate. The following formalization is based on the GD formalization in @GD.
