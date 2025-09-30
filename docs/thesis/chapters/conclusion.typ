// =====================================================
// The inductive datatype chapter. Formalizes required
// number theory to be able to express cantor pairings.
// Then, writes a package that encodes arbitrary data-
// types into the formalized integers.
// =====================================================

#import "../style.typ": *
#import "../formalisms.typ": *

= Conclusion
This thesis set out to test whether Grounded Arithmetic (_GA_) can function as a practical foundation for formal reasoning. The development of Isabelle/GA demonstrates that this is indeed possible.

_GA_ supports productive reasoning, allowing for the straightforward definition of basic number-theoretic functions, along with proofs of many of their simpler properties. A central question was whether the _habeas quid_ premises carried by many _GA_ inference rules would pose a major obstacle. This turned out to be manageable: termination proofs were as simple as expected, even for non-primitive recursive functions such as Ackermann's function. Throughout the formalization, no unexpected inconsistencies arose, in line with the complementary metalogical results of the _GD_ authors, but important as a confirmation from direct mechanization.

The Isabelle/Pure framework adapted well to the demands of _GA_. The built-in simplifier was configured with little effort, though _GA_’s habeas quid premises required dedicated automation through a custom subgoal solver. With these adaptations, reasoning in Isabelle/GA reached a level of usability approaching that of classical reasoning.

The recursive definitional mechanism native to _GA_ proved highly effective. It enabled the construction of nontrivial functions such as Cantor pairing and its inverses using recursive and even mutually recursive definitions, along with proofs of termination and properties like the strict growth property of the Cantor pairing function ($x < angle.l x, y angle.r$ for $x >= 2$ and $y < angle.l x, y angle.r$ for $y >= 1$). Without a mature arithmetic library, these proofs would not have been possible using the standard analytic closed-form definition. This highlights recursion as a central asset of _GA_, providing expressivity "out of the box".

The framework for encoding arbitrary inductive datatypes further confirmed _GA_'s expressive power. Distinctness, injectivity, exhaustiveness, closure, and induction were all proved for a manually encoded `List` datatype. This construction mainly serves as a blueprint for future tooling: a definitional datatype mechanism for Isabelle/GA, comparable to Isabelle/HOL’s inductive datatype package.

Several lessons emerge from these results. _GA_ works as intended: its natural deduction style axioms translated almost directly into Isabelle/Pure and its definitional freedom enabled the formalization of nontrivial functions and proofs without reliance on a large library of arithmetic results.

Future work should extend these foundations by developing an inductive datatype compiler, following the blueprint from @inductive, and by improving proof automation through a dedicated proof search procedure. Building on inductive datatype support, another line of work could pursue reflective reasoning in Isabelle/GA, enabling meta-reasoning about GA within GA itself, as envisioned by the original GD authors @GD. In conclusion, this thesis demonstrates that grounded reasoning can be practical, and that _GA_ has the potential to mature into a serious alternative foundation for reasoning about computation.
