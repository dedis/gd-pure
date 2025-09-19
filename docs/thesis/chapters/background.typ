// =====================================================
// The background chapter. Introduces the Isabelle Pure
// logic and Grounded Arithmetic.
// =====================================================

#import "@preview/ouset:0.2.0": ouset
#import "../style.typ": *
#import "../formalisms.typ": *
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#show: codly-init.with()
#codly(zebra-fill: none)

= Background

== Isabelle/Pure
Isabelle provides a logical framework called _Pure_. It contains a minimal meta-logic, which is a typed lambda calculus with few additional connectives, some keywords to add types and constants to said calculus, and a structured proof language called Isar. Any object logic in Isabelle, for example the highly mature Isabelle/HOL fragment, are formalized atop _Pure_.

Isabelle itself is implemented in the Standard ML (SML) programming language, and implementing an object logic _Pure_ almost always requires writing SML for things like proof automation, providing keywords, methods, or definitional mechanisms for users, and various other tooling such as code extraction.

This subsection provides a formalization of the _Pure_ calculus.

Unfortunately, there is no single document that lays out the syntax, axioms, and derivation rules of the _Pure_ calculus in their entirety. The following is an attempt at providing such a characterization, combining information from two Isabelle papers @isabelle00 @isabelle89 and the Isabelle reference manual @isabelle_ref.

=== Syntax of Pure

The core syntax of _Pure_ is a typed lambda calculus, augmented with type variables, universal quantification, equality, and implication.

Propositions are terms of the distinct type `prop`. Propositions in _Pure_ are thus terms and not types, like they are in type-theory based provers like Rocq or Lean.

#definition-box("Type Syntax")[
  #pure-types
]

#definition-box("Term Syntax")[
  #pure-terms
]

The symbols used for implication, equality, and universal quantification are non-standard to leave the standard symbols free for object logics.

Even though _Pure_ has type variables, it provides no construct to capture them as an argument, and thus also has no for-all type like the polymorphic lambda calculus System F.

=== Equality, Implication, and Quantification as Type Constructors

The connectives equality, implication, and universal quantification are all type constructors of the `prop` type with the following polymorphic type signatures.

#definition-box(none)[
  #pure-type-constructors
]

The arguments of $equiv$ are the two operands to compare, the arguments for $arrow.double.long$ are the sequent and consequent respectively, while the argument of $and.big$ is a function from the type whose inhabitants are quantified over to the term that represents the body of the quantifier.

Since type variables denote only a single, albeit arbitrary, type, there is technically one instance of each polymorphic connective for every given type. For example, for any type $sigma$, there is a constant $equiv_sigma "":: sigma => sigma => "prop"$.

=== Deduction Rules

The operational semantics of the underlying lamdba calculus and its typing rules are standard and thus omitted. The following discusses the more interesting deduction rules, which make _Pure_ a logical framework.

Relative to an object logic with a set of defined axioms $Alpha$ any axiom $alpha in Alpha$ can always be derived, as can any assumption $gamma in Gamma$.

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

An object logic in _Pure_ is created by adding new types, constants and axioms. That is, the _Pure_ logic is extended.

It is convention to define a new propositional type in an object logic, which is used as the type of propositions in the _object_ logic, as opposed to the _meta_ logic, which is _Pure_.

This is achieved using the $"typedecl"$ keyword, which declares a syntactic type in the _Pure_ calculus. This type has no known inhabitants or any other information yet.

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
Now, the type `o` has knows inhabitants and structure. However, Isabelle (or rather, _Pure_) cannot reason about it, because it cannot connect the type `o` meaningfully with its meta-theory. To resolve this, a judgment must translate from the object-level proposition type `o` to the meta-level type `prop`.

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

This short introduction suffices for now, as we will later implement a much richer logic, Grounded Deduction, using these same basic constructs. We can clearly see that implementing an object logic in _Pure_ actually extends _Pure_, in the sense that it adds new types and deduction rules. For example, our extension added a type and three symbols to the existing syntax of _Pure_. If we call the tiny logic formalized above _Pure'_, the following is its type and term syntax:

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

== Grounded Arithmetic (GA)
<ga-ref>

This subsection provides a full characterization of GA, a first-order formalization of arithmetic based on the principles of GD. This is the fragment that is later formalized in Isabelle.

GA makes definitions first-class objects in the logic and allows arbitrary references of the symbol currently being defined or other, previously defined symbols, in the expanded term.

To prevent immediate inconsistency, GA must weaken other deduction rules commonly seen in classical logic. Specifically, GA adds a so-called _habeas quid_ sequent to many inference rules. Intuitively, this means that in certain inference rules, a (sub)term must first be shown to terminate.

=== BGA Formalization

We start by formalizing the syntax and axioms of _Basic Grounded Arithmetic_ (_BGA_), the quantifier-free fragment of GA, based on the formalization in @GD. This formulation later adds quantifiers by encoding them as unbounded computations in _BGA_, yielding full _GA_. This however requires a sophisticated encoding using Gödel-style reflection, i.e. encoding its own term syntax into natural numbers, which is out of scope for a formalization in _Pure_. Thus, we will later add quantifiers by simply axiomatizing them.

The primitive term syntax of BGA is the following.

#definition-box("BGA Primitive Term Syntax")[
  #bga-term-syntax
]

It is noteworthy that the GA term syntax mixes expressions that are natural numbers and expressions that are formulas into the same syntactic category. For example, the expression $S(x) = x or x$ is a valid term according to the syntax, despite the left-hand side shape clearly indicating a natural number, while the right hand side shape indicates a truth value.

Besides the primitives, other constants and logical connectives are defined as notational shorthands using the primitives.

#definition-box("Notational Shorthands")[
  #ga-definitional-shorthands
]

The surprising shorthands are $a #nat$ and $p #bool$. The latter is a predicate over $p$ deciding whether it is a binary truth value. In a logic with the law of excluded middle, $p #bool$ would be a tautology for any $p$, but in a logic without it, it can be interpreted as a termination certificate for truth values. Similarly, $a #nat$ can be interpreted as a termination certificate for natural number expressions. The shorthand itself is surprising, because if equality is reflexive, $a = a$ is true for any $a$. In GA however, equality is not reflexive as we will soon see, and a proof of $a = a$ is equivalent to a termination proof of the expression.

The syntax does not mean much without a set of axioms giving them meaning. We start with listing the propositional logic axioms.

In the following, $Gamma$ denotes a set of background assumptions. For completeness sake, the explicit structural rules governing this set of assumptions is listed here. Since $Gamma$ is a set, the usually explicit rules for permuting and duplicating assumptions are not needed.

#definition-box("Structural Rules")[
  #structural-rules
]

#definition-box("Propositional Logic Axioms")[
  #bga-prop-logic-axioms
]

Rules such as $not not "IE"$ with a double-line are bidirectional, i.e. they serve as both an introduction and elimination rule.

The propositional axioms are fairly standard, but inclusion of double negation elimination is notable, as this is common in classical logics, but omitted in computational logics.

#definition-box("Equality Axioms")[
  #bga-eq-axioms
]

The equality axioms notably omit reflexivity. Symmetry of equality is an axiom, as is equality substitution in an arbitrary context $K$. Transitivity of equality can be deduced using equality substitution.

#definition-box("Natural Number Axioms", font_size: 0.9em)[
  #bga-nat-axioms
]

The natural number axioms are fairly close to the standard Peano axioms, with some notable exceptions.

The _grounding_ equality is the $0I$ axiom, postulating that $0 nat$, or, by unfolding the definition, $0 = 0$. Using the $S=I E$ axiom, $suc(a) nat$ can be deduced for any $a$ for which $a nat$ is already known. The induction axiom $"ind"$ has an additional premise of $a nat$, i.e. it requires proof that the expression induction is performed over is indeed a (terminating) natural number.

Conditional evaluation is a primitive in _GA_ and its behavior must thus be axiomatized. The two inference rules correspond to the positive and negative evaluation of the condition, and they both require that the expression from the corresponding branch is shown to be terminating (i.e. $a nat$ and $b nat$ respectively). This additional premise prevents equalities of potentially non-terminating expressions to be deduced.

==== Grounded Contradiction
Although _GA_ is not classical, a contradiction rule can be derived. The resulting inference rule has an additional $p bool$ premise not present in the classical version, which demands $p$ is first shown to have a truth value. To get a feeling for the logic, we construct the proof explicitly in a natural deduction style derivation tree.

#theorem("Grounded Contradiction")[
  #grounded-contradiction
]
#proof(tree(grounded-contradiction-deriv))

==== Grounded Implication
Impliciation is not a primitive in _GA_, but rather the shorthand $a arrow.r b equiv not a or b$. From this definition, the classical elimination rule _modus ponens_ can be derived. However, only a weakened introduction rule, with the now familiar additional _habeas quid_ premise, can be derived.

#theorem("Modus Ponens")[
  #modus-ponens
]
#proof(tree(modus-ponens-deriv))

#theorem("Implication Introduction")[
  #implI
]
#proof(tree(implI-deriv))

==== Definitional Axioms
Finally, the axioms for definitions allow arbitrary substitution of a symbol with its definition body (and the other way around) in any context. The vector notation $vec(a)$ denotes an argument vector for the defined function symbol.

#definition-box("Definition Axioms")[
  #bga-def-axioms
]

=== GA with Axiomatized Quantifiers
As already mentioned, the creators of _GA_ claim that quantifiers can be encoded into BGA using the powerful definitional mechanism @GD, yielding full _GA_ "for free". However, as this will not be feasible in the formalization within _Pure_, the following axiomatizes the quantifiers instead.

#definition-box("Quantifier Axioms")[
  #bga-quantifier-axioms
]

Besides the additional _habeas quid_ premises, the quantifier axioms are standard.

Since the quantifiers are primitive here, they must be added to the primitive term syntax, yielding the full _GA_ primitive term syntax.

#definition-box("GA Primitive Term Syntax")[
  #ga-term-syntax
]

This set of axioms is now a full formalization of a grounded flavor of first-order arithmetic, which we just refer to as _GA_ from now on.
