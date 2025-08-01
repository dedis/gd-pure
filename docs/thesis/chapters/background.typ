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

Any object logics in Isabelle, for example the popular Isabelle/HOL fragment, are formalized atop a logic framework called Pure. Pure is designed to be as generic as possible to allow implementing a wide range of object logics atop it. It provides infrastructure to define types and axioms to facilitate the formalization of object logics.

Unfortunately, there is no single document that lays out the syntax, axioms, and derivation rules of Pure in their entirety. The following is an attempt at providing such a characterization, combining information from two Isabelle papers @isabelle00 @isabelle89 and the Isabelle reference manual @isabelle_ref.

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

The axiomatized rules simply state that $"True"$ holds and that from either $P$ or $Q$, $P or Q$ can be derived. Here, $P$ and $Q$ are implicitly universally quantified, ranging over all terms of type $"Prop"$. That is, $P$ and $Q$ can be substituted for any term.
Now, the type $o$ has knows inhabitants and structure. However, Isabelle (or rather, Pure) cannot reason about it, because it can only reason about terms of type $"Prop"$. To resolve this, a judgment must translate from the object-level proposition type $o$ to the meta-level type $"Prop"$.

```Isabelle
judgment
  Trueprop :: ‹o ⇒ prop›  (‹_› 5)
```

The syntax annotation $(‹\_› med 5)$ means that any term of type $o$ is implicitly augmented with the $"Trueprop"$
 judgment. The very low precedence value of 5 ensures that the $"Trueprop"$ judgment is only applied to top-level terms. For example, the term $x or "True"$ is the same as $"Trueprop" (x or "True")$ and both are of type $"Prop"$ due to the $"Trueprop"$ predicate converting the formula to that type.

As you might have noticed, we have made use of this implicit conversion from $o$ to $"Prop"$ already in the axiomatization block from earlier. That is, the $"Trueprop"$ judgment must be declared before the axiomatization block, else the latter will just report a typing error.

Now, we can state and prove a first lemma in this tiny object logic, using the previously defined axioms.

```Isabelle
lemma "x ∨ True"
apply (rule disjI2)
apply (rule true)
done
```
This short introduction suffices for now, as we will later implement a much richer logic, Grounded Deduction, using these same basic constructs. We can clearly see that implementing an object logic in Pure actually extends Pure, in the sense that it adds new types and deduction rules. For example, our extension added a type and two symbols to the existing syntax of Pure. If we call the tiny logic formalized above Pure', the following is its type and term syntax:

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

It is technically possible to avoid declaring a new proposition type for an object logic and instead use $"Prop"$ directly as the type of propositions. However, doing so means that the logic immediately inherits the built-in connectives and deduction rules, such as implication $(arrow.long.double)$ and universal quantification $(and.big)$, and the sequent-style reasoning built into the kernel.

This implicit structure reduces the control one has over the logic, and as a result, the best practice is to take a clean-slate approach, declare a new type for object-level propositions, and define a separate set of connectives and inference rules for it.

== Grounded Deduction (GD)
Grounded deduction is a logical framework developed recently at EPFL. Its development is motivated by the observation that in logics of both classical and intuitionistic tradition, there is inherently no definitional freedom. That is, definitions must describe provably terminating expressions. The reason for this is that without such restrictions in place, logics built on either tradition would be immediately inconsistent.

To see this, consider the definition
$ L equiv not L. $

Let us imagine that this is a valid definition in a classical logic (that is, a logic that at least has the law of excluded middle (LEM) and double negation elimination). We may then reason about its truth value using the LEM.

Let us first prove that $L$ holds by contradiction.

Assuming $not L$, we can derive $not not L$ by the definition and then $L$ via double negation elimination. Since we derived both $L$ and $not L$ from hypothetically assuming $not L$, a contradiction, this allows us to definitely conclude $L$.

However, having proven $L$, we can also derive $not L$ by applying the definition, and thus derived a contradiction in the logic itself, making it inconsistent.

What went wrong? The law of excluded middle forces a truth value on any term in classical logic, thus circular or non-sensical definitions such as $L equiv not L$, for which no truth value can or should be assigned, cannot be admitted.

Intuitionistic logic discards the law of excluded middle and is thus safe from a proof by contradiction like the one shown above. However, in intuitionistic tradition, lambda calculus terms are interpreted as proof terms, witnessing the truth of the proposition encoded by their type. Lambda functions of type $A => B$ are then interpreted as producing a proof of $B$ given a proof of $A$, which however means that they must always terminate.

To see this, consider the following attempt at a definition of an (ill-founded) term of type $forall alpha. alpha$, i.e., a proof of every proposition:

$ "prove_anything" := Lambda alpha. "prove_anything" alpha $

Here, the construct $Lambda$ is the type-level analogue of lambda abstraction: it abstracts over a type variable and substitutes it in the body. That is, if $e$ has type $T$, then $Lambda alpha. e$ has type $forall alpha. T$. If such a term were permitted in the logic, it would type-check as having type $forall alpha. alpha$. Instantiating it at any type $P$ yields a term of type $P$, i.e., a proof of $P$ for arbitrary $P$, making every proposition in the logic trivially provable.

What went wrong this time? Functions in intuitionistic logics represent logical implication. If a function has type $A => B$, the function must provide proof of $B$, that is, return a term $b: B$ given any term $a: A$. The function _witnesses_ the implication of $A$ to $B$. If the function does not terminate however, this proof is not actually constructed and assuming the hypothetical resulting proof term leads to inconsistency.

Having shown that the presence of arbitrarily recursive definitions leads to logical inconsistency in both widely recognized schools of logic, let us now motivate why a formal system resistant to arbitrary  definitional recursion would be desirable in the first place.
In computer science in particular, the need for an ability to define arbitrary recursion is immediate; virtually every popular programming language is turing complete, which requires arbitrary recursion. Also, many programs are not designed to terminate at all, like operating system kernels or web servers.
Additionally, the ability to state paradoxical definitions and use a formal system to reason about them is of interest in and of itself. A less trivial example of such a paradoxical recursive definition than the Liar’s paradox stated above would be Yablo’s paradox. This paradox is notable, because unlike the classical liar sentence (“This sentence is false”), it constructs a self-referential paradox without direct self-reference, using an infinite sequence of sentences.

Let us consider an infinite list of sentences $(Y_n)_(n in N)$, where each sentence $Y_n$ is defined as follows:

$ Y_n equiv forall k. k > n => not Y_k $

That is, each sentence $Y_n$ asserts that all sentences following it are untrue.

Now suppose that one of the sentences $Y_i$ is true. Then, by its definition, all $Y_j$ with $j > i$ must be false. In particular, $Y_(i+1)$​is false, which means that there must exist some $k > i+1$ such that $Y_k$ is true. But this contradicts the statement by $Y_i$ that all $Y_j$ with $j > i$ are false, in particular $Y_k$. Hence, no $Y_i$​can be true.

But then, $not Y_i$ holds for all $i in N$. This however means that $Y_0$ must be true, as its claim of $not Y_i$ for any $i > 0$ is indeed fulfilled. A seemingly paradoxical setup, even though there is no direct self-reference. No truth value can be assigned to any of the $Y_i$.

GD makes definitions first-class object in the logic and allows arbitrary recursion in their definitions, including to other, previously-defined symbols.
// TODO SCK: what about mutual recursion?
To prevent immediate inconsistency, GD must of course weaken other deduction rules. Specifically, GD adds a "habeas quid" precondition to many inference rules. This is achieved by defining typing predicates. blabla[...]
