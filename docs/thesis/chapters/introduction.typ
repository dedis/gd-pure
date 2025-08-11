= Introduction


== Motivation: Recursive Definitions in Classical and Constructive Logic

We start with the simple observation that in logics of both classical and constructive tradition, there is inherently no definitional freedom. That is, definitions must describe provably terminating expressions. The reason for this is that without such restrictions in place, logics built on either tradition would be immediately inconsistent.

To see this, consider the definition
$ L equiv not L. $

Let us imagine that this is a valid definition in a classical logic (that is, a logic that at least has the law of excluded middle (LEM) and double negation elimination). We may then reason about its truth value using the LEM.

Let us first prove that $L$ holds by contradiction.

Assuming $not L$, we can derive $not not L$ by the definition and then $L$ via double negation elimination. Since we derived both $L$ and $not L$ from hypothetically assuming $not L$, a contradiction, this allows us to definitely conclude $L$.

However, having proven $L$, we can also derive $not L$ by applying the definition, and thus derived a contradiction in the logic itself, making it inconsistent.

What went wrong? The law of excluded middle forces a truth value on any term in classical logic, thus circular or non-sensical definitions such as $L equiv not L$, for which no truth value can or should be assigned, cannot be admitted.

Constructive logics discard the law of excluded middle and are thus safe from a proof by contradiction like the one shown above. However, in intuitionistic tradition, lambda calculus terms are interpreted as proof terms, witnessing the truth of the proposition encoded by their type. Lambda functions of type $A => B$ are then interpreted as producing a proof of $B$ given a proof of $A$, which however means that they must always terminate.

To see this, consider the following attempt at a definition of an (ill-founded) term of type $forall alpha. alpha$, i.e., a proof of every proposition:

$ "prove_anything" := Lambda alpha. "prove_anything" alpha $

Here, the construct $Lambda$ is the type-level analogue of lambda abstraction: it abstracts over a type variable and substitutes it in the body. That is, if $e$ has type $T$, then $Lambda alpha. e$ has type $forall alpha. T$.

If such a term were permitted in the logic, it would type-check as having type $forall alpha. alpha$. Instantiating it at any type $P$ yields a term of type $P$, i.e., a proof of $P$ for arbitrary $P$, making every proposition in the logic trivially provable.

What went wrong this time? Functions in constructive logics represent logical implication. If a function has type $A => B$, the function must provide proof of $B$, that is, return a term $b: B$, given any term $a: A$. The function _witnesses_ the implication of $A$ to $B$. If the function does not terminate on an input however, this proof is not actually constructed and assuming the hypothetical resulting proof term leads to inconsistency.

== Enter GD

Grounded deduction (GD) is a logical framework developed recently at EPFL, whose development was motivated by precisely the observation made above. The project aims to axiomatize a consistent formal system, in which arbitrary recursion in definitions is permitted, which is still as expressive as possible. There is an ongoing formalization project of GD in the proof assistant Isabelle/HOL, which already yielded a consistency proof of the quantifier-free fragment of GD, showing great promise for the credibility of GD. However, the other aim of GD is to show that it is also expressive and importantly, usable as a tool for formalizing mathematics itself. The formalization in the mature HOL logic enables studying meta-logical properties of GD, such as consistency. However, it is not suitable for providing GD as a tool for formal reasoning itself for two main reasons.

- Formalizing GD within a mature metalogic such as HOL adds the axioms of the metalogic to the trusted base of GD, which is undesirable from a meta-logical perspective.
- A logic is developed largely for idealistic reasons; the authors believe its reasoning principles are the right ones for at least some domain. Formalizing such a logic within another rich logic means that its reasoning principles are simply embedded in the, likely very different principles, of the meta-logic, defeating that purpose.

It is thus highly desirable to formalize a foundational formal system like GD atop a very minimal meta-logic.

This is exactly what Isabelle provides with the Pure framework: A minimal, generic logical calculus to formalize object logics on top of. Any object logic in Isabelle, including Isabelle/HOL, are formalized atop Pure.

This thesis aims to fully axiomatize GD in Pure, yielding essentially an interactive theorem prover Isabelle/GD, which can be used for formal reasoning based directly on the reasoning principles and axioms of GD.
