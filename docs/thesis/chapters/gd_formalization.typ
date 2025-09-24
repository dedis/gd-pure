// =====================================================
// The formalization chapter. Gives the entire formali-
// zation of GD in Pure.
// =====================================================

#import "../style.typ": *
#import "../formalisms.typ": *
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#show: codly-init.with()
#codly(zebra-fill: none)

= Formalizing GA in Pure
<ga-in-pure>

This chapter aims to translate the full formalization of _GA_ in @ga-ref into Isabelle/Pure. Formally, this means that _GA_ is embedded into the _Pure_ calculus, using it as a meta-logic. The typed lambda calculus _Pure_ is fully characterized in @pure-ref. In the following, all types mentioned are part of the _Pure_ type system. _GA_ itself has no real (conventional) notion of types, although the 'inherited' types of _Pure_ can also be interpreted as syntactic _GA_ types.

== Proposotional Axioms
We first declare a syntactic Isabelle type for truth values in _GA_ `o` and a function to convert from `o` to the type of truth values of the _Pure_ calculus `prop`, as explained in @how-to-pure.

```Isabelle
typedecl o

judgment
  Trueprop :: ‹o ⇒ prop›  (‹_› 5)
```

Now, we can declare constants $"disj"$ and $"not"$, with the propositional axioms from @bga-ref.

```Isabelle
axiomatization
  disj :: ‹o ⇒ o ⇒ o›  (infixr ‹∨› 30) and
  not :: ‹o ⇒ o› (‹¬ _› [40] 40)
where
  disjI1: ‹P ⟹ P ∨ Q› and
  disjI2: ‹Q ⟹ P ∨ Q› and
  disjI3: ‹⟦¬P; ¬Q⟧ ⟹ ¬(P ∨ Q)› and
  disjE1: ‹⟦P ∨ Q; P ⟹ R; Q ⟹ R⟧ ⟹ R› and
  disjE2: ‹¬(P ∨ Q) ⟹ ¬P› and
  disjE3: ‹¬(P ∨ Q) ⟹ ¬Q› and
  dNegI: ‹P ⟹ (¬¬P)› and
  dNegE: ‹(¬¬P) ⟹ P› and
  exF: ‹⟦P; ¬P⟧ ⟹ Q›
```

This immediately introduces the infix notation $a or b$ for $"disj" a " " b$ and $not a$ for $"not" a$, where `infixr` means that the provided syntax is an infix operator that associates to the right. The precedence of the $not$ operator is 40, it thus binds stronger than the $or$ operator with precedence 30.

In general, a rule in the natural deduction style formalization from @ga-ref of the following shape:

#definition-box(none)[
  #nat-deduct-rule
]

Is translated into the following shape in Isabelle:

```Isabelle
(A1 ⟹ P1) ⟹ (A2 ⟹ P2) ⟹ ... ⟹ (An ⟹ Pn) ⟹ C
``` 

Or, equivalently:
```Isabelle
⟦A1 ⟹ P1; A2 ⟹ P2; ...; An ⟹ Pn⟧ ⟹ C
``` 
Potential background assumptions $Gamma$ do not need to be explicitly managed in Isabelle. What we consider a derivation, i.e. $tack.r$ in _GA_ is just implication $impl$ in Pure.

Theorems in this section that are explicitly presented in a _theorem block_ keep using the natural deduction style to be consistent with @pure-ref and @ga-ref. In this notation, deducability from assumptions is denoted $tack.r$, while in Isabelle the corresponding symbol is $==>$, i.e. meta-level implication.

== Natural Number Axioms

We declare a type `num` for natural numbers.

```Isabelle
typedecl num
```

Before the majority of natural number axioms, we define equality and some connectives derived from the primitives. We axiomatize equality with unrestricted substitution and symmetry. Equality is not just defined for `num`, but for any type `'a`, where `'a` is a generic type variable. As expected, equality is a binary infix operator associating to the left.

```Isabelle
axiomatization
  eq :: ‹'a ⇒ 'a ⇒ o›  (infixl ‹=› 45)
where
  eqSubst: ‹⟦a = b; Q a⟧ ⟹ Q b› and
  eqSym: ‹a = b ⟹ b = a›
```

Transitivity can be proven using the substitution axiom.

```Isabelle
lemma eq_trans: "a = b ⟹ b = c ⟹ a = c"
by (rule eqSubst[where a="b" and b="c"], assumption)
```
However, transitivity is not a very useful lemma, as it just as efficient to directly use equality substitution.

Inequality, the $bool$ and $nat$ judgments, and other logical operators can now be defined in terms of the axiomatized primitives. Notably, $bool$ is explicitly typed at $o to o$, meaning that e.g. the term $suc("zero") bool$ is rejected by the Isabelle parser, as it is not well-typed. Similarly, $nat$ is explicitly typed at $"num" to o$, only accepting an argument of type $"num"$.

```Isabelle
definition neq :: ‹num ⇒ num ⇒ o› (infixl ‹≠› 45)
  where ‹a ≠ b ≡ ¬ (a = b)›
definition bJudg :: ‹o ⇒ o› (‹_ B› [21] 20)
  where ‹(p B) ≡ (p ∨ ¬p)›
definition isNat :: ‹num ⇒ o› (‹_ N› [21] 20)
where "x N ≡ x = x"
definition conj :: ‹o ⇒ o ⇒ o› (infixl ‹∧› 35)
  where ‹p ∧ q ≡ ¬(¬p ∨ ¬q)›
definition impl :: ‹o ⇒ o ⇒ o› (infixr ‹⟶› 25)
  where ‹p ⟶ q ≡ ¬p ∨ q›
definition iff :: ‹o ⇒ o ⇒ o› (infixl ‹⟷› 25)
  where ‹p ⟷ q ≡ (p ⟶ q) ∧ (q ⟶ p)›
```

As an example, all the introduction and elimination rules for conjunction $and$ can be proven now:

```Isabelle
lemma conjE1:
  assumes p_and_q: "p ∧ q"
  shows "p"
apply (rule dNegE)
apply (rule disjE2[where Q="¬q"])
apply (fold conj_def)
apply (rule p_and_q)
done

lemma conjE2:
  assumes p_and_q: "p ∧ q"
  shows "q"
apply (rule dNegE)
apply (rule disjE3[where P="¬p"])
apply (fold conj_def)
apply (rule p_and_q)
done

lemma conjI:
  assumes p: "p"
  assumes q: "q"
  shows "p ∧ q"
apply (unfold conj_def)
apply (rule disjI3)
apply (rule dNegI)
apply (rule p)
apply (rule dNegI)
apply (rule q)
done
```

We can now axiomatize the `zero` constant and `pred` and `suc` functions. Compared to the formalization in @ga-ref, there is an additional axiom here stating $P(0) = 0$. This will allow stating some convenient lemmas later, for example that for any $n$ with $n nat$, $P(n) <= n$.

``` Isabelle
axiomatization
  zero :: ‹num›                        and
  suc :: ‹num ⇒ num›     (‹S(_)› [800]) and
  pred :: ‹num ⇒ num›    (‹P(_)› [800])
where
  nat0: ‹zero N› and
  sucInj: ‹S a = S b ⟹ a = b› and
  sucCong: ‹a = b ⟹ S a = S b› and
  predCong: ‹a = b ⟹ P a = P b› and
  eqBool: ‹⟦a N; b N⟧ ⟹ (a = b) B› and
  eqBoolB: ‹⟦x B; y B⟧ ⟹ (x = y) B› and
  sucNonZero: ‹a N ⟹ S a ≠ zero› and
  predSucInv: ‹a N ⟹ P(S(a)) = a› and
  pred0: ‹P(zero) = zero› and
  ind: ‹⟦a N; Q zero; ⋀x. x N ⟹ Q x ⟹ Q S(x)⟧ ⟹ Q a›
```

The following two crucial inference rules can be proven from these axioms, whose proof is given directly in the Isabelle formalization.

#theorem("Natural Number Typing Rules")[
  #nat-typing-rules
]

#proof(
```Isabelle
lemma natS:
  assumes a_nat: "a N"
  shows "S a N"
apply (unfold isNat_def)
apply (rule sucCong)
apply (fold isNat_def)
apply (rule a_nat)
done

lemma natP:
  assumes a_nat: "a N"
  shows "P a N"
apply (unfold isNat_def)
apply (rule predCong)
apply (fold isNat_def)
apply (rule a_nat)
done
```)

The constants $"True"$ and $"False"$ can now be defined as canonical truth and falsehood $"True" equiv (0 = 0)$ and $"False" equiv (S(0) = 0)$.

```Isabelle
definition True
  where ‹True ≡ zero = zero›
definition False
  where ‹False ≡ S(zero) = zero›
```

== Grounded Contradiction
The grounded contradiction lemma proven as a derivation tree in @contradiction can now be proven in the Isabelle formalization.

#definition-box("Grounded Contradiction")[
  #grounded-contradiction
]

```Isabelle
lemma grounded_contradiction:
  assumes p_bool: ‹p B›
  assumes notp_q: ‹¬p ⟹ q›
  assumes notp_notq: ‹¬p ⟹ ¬q›
  shows ‹p›
proof (rule disjE1[where P="p" and Q="¬p"])
  show "p ∨ ¬p"
    using p_bool unfolding GD.bJudg_def .
  show "p ⟹ p" by assumption
  show "¬p ⟹ p"
  proof -
    assume not_p: "¬p"
    have q: "q" using notp_q[OF not_p] .
    have not_q: "¬q" using notp_notq[OF not_p] .
    from q and not_q show "p"
      by (rule exF)
  qed
qed
```

== Syntax Translation for Natural Numbers
The axiomatized symbols for natural numbers are of the shape $(["SP"]^+ "zero")$ as a regex. For example, `zero` and `S(S(P zero))` are natural numbers in this GA formalization. It would be better to use the familiar base 10 system, such that the user can write a base-10 number and it is correctly interpreted as the corresponding `num` expression by Isabelle. Luckily, Isabelle provides powerful syntax translation support.

The following snippet achieves this by first declaring an implicit conversion function from numerical tokens (resulting from user input) to the natural number type `num`. The annotation `("_")` means it is applied to all such tokens implicitly. Then, an SML file called _peano\_numerals.ML_ provides the function _parse\_gd\_numeral_, which translates a number in base 10 to the `num` version (for example 3 to $suc(suc(suc("zero")))$).

Finally, the command _parse\_translation_ specifies that the previously declared `_gd_num` constant performs the action specified by the _parse\_gd\_numeral_ function.

```Isabelle
syntax
  "_gd_num" :: "num_token ⇒ num"    ("_")

ML_file "peano_numerals.ML"

parse_translation ‹
  [(@{syntax_const "_gd_num"}, Peano_Syntax.parse_gd_numeral)]
›
```
As mentioned before, Isabelle is implemented mostly in (a dialect of) Standard ML (SML). The SML infrastructure of Isabelle is not meant to be completely abstracted away from the (advanced) user, but rather does Isabelle provide a rich API of SML functions and types, which is collectively referred to as Isabelle/ML. A syntax translation is precisely the kind of task that can be implemented in SML, hooking into the Isabelle implementation itself.

The following are the contents of the _peano\_numerals.ML_ file, providing the translation logic from a string representation of a base-10 number to a `num` expression.

```SML
structure Peano_Syntax = struct

  fun nat_to_peano 0 = Syntax.const @{const_syntax "zero"}
    | nat_to_peano n = Syntax.const @{const_syntax "suc"} $ nat_to_peano (n - 1)

  fun parse_gd_numeral _ [Free (s, _)] =
        (case Int.fromString s of
           SOME n => nat_to_peano n
         | NONE => error ("Not a numeral: " ^ s))
    | parse_gd_numeral _ _ = error "Unexpected numeral syntax"

end
```
The function `Int.fromString` is part of the Isabelle/ML API and tries to convert the input string to an (SML) `Int`. The translation from `Int` is then straightforward -- `0` is translated to `zero` and `n` to $sucf$ prepended to the recursive translation of `n-1`.

== Quantifier Axiomatization
The quantifier axioms exactly implement the ones from the pen-and-paper formalization in @quantifiers, displayed again here for reference.

#definition-box(none)[
  #bga-quantifier-axioms
]

A crucial detail is the explicit typing of the quantifiers at the type $("num" arrow.r.double o) arrow.r.double o$. It makes the quantifiers range only over $"num"$, crucial as _GA_ aims to be a first-order theory over the natural numbers. In a higher-order theory, the quantifiers would range over any type and be typed at $('a arrow.r.double o) arrow.r.double o$, where $'a$ is a generic type variable.

```Isabelle
axiomatization
  forall :: "(num ⇒ o) ⇒ o"  (binder "∀" [8] 9) and
  exists :: "(num ⇒ o) ⇒ o"  (binder "∃" [8] 9)
where
  forallI: "⟦⋀x. x N ⟹ Q x⟧ ⟹ ∀x. Q x" and
  forallE: "⟦∀c'. Q c'; a N⟧ ⟹ Q a" and
  existsI: "⟦a N; Q a⟧ ⟹ ∃x. Q x" and
  existsE: "⟦∃i. Q i; ⋀a. a N ⟹ Q a ⟹ R⟧ ⟹ R"
```

== Conditional Evaluation Axiomatization

Conditional evaluation cannot seem to be derived from primitives axiomatized so far and must thus be an axiomatized primitive itself.

The syntax of the conditional operator, with the desired shape of the application $"cond" a " " b " " c$ being $cond(a,b,c)$, seems complicated, but Isabelle is well-equipped to handle syntax like this, with the ability to specify the 'holes' in a syntax expression like in the following declaration. This type of notation is called mixfix in Isabelle, as it mixes infix and prefix notation.

Notably, the two branches of the operator and the return type are typed at the generic $'a$, indicating that the conditional operator in this formalization is polymorphic. Contrary to the pen-and-paper formalization in @bga-ref, this allows for returning truth values in a conditional evaluator (or any other type at that, for example functions of type $"num" to "num"$), for example the constants `True` and `False`. Although these could be encoded with natural numbers just as well, this requires equality checks of a result and is less elegant. Due to the _habeas quid_ premises of the two branching axioms, making the arguments of the syntactic construct generic is not sufficient, it just means that the parser won't reject a term such as $cond(c, "True","False")$. Since neither $"True" nat$ nor $"False" nat$ can be proven, this term cannot be 'reduced' using either `condI1` or `condI2`. Thus, there are three additional axioms for conditional evaluation over values of type `o`, mirroring the ones for conditional evaluation over `num`, but with the _habeas quid_ premise of $bool$ instead of $nat$. Now, $cond("True","True","False") = "True"$ can be proven using the axiom `condI1B`.

```Isabelle
consts
  cond :: ‹o ⇒ 'a ⇒ 'a ⇒ 'a› (‹if _ then _ else _› [25, 24, 24] 24)

axiomatization where
  condI1: ‹⟦c; a N⟧ ⟹ (if c then a else b) = a› and
  condI2: ‹⟦¬c; b N⟧ ⟹ (if c then a else b) = b› and
  condT: ‹⟦c B; a N; b N⟧ ⟹ if c then a else b N› and
  condI1B: ‹⟦c; d B⟧ ⟹ (if c then d else e) = d› and
  condI2B: ‹⟦¬c; e B⟧ ⟹ (if c then d else e) = e› and
  condTB: ‹⟦c B; d B; e B⟧ ⟹ if c then d else e B›
```

== Definitional Mechanism Axiomatization
The axioms in the formalization in @bga-ref don't make it entirely clear what the definitional operator with the symbol $equiv$ is. It is not part of the primitive syntax, making it meta-logical, in the sense that it is outside the logical calculus. However, it is also a premise in the definitional axioms, implying it behaves like a proposition:

#definition-box(none)[
  #bga-def-axioms
]

The most straightforward implementation of such a mechanism in Isabelle is to just treat it as any other logical connective. Its definition and axiomatization make it conceptually very similar to equality =.

Like equality, the definitional mechanism is polymorphic, allowing the left-hand side and right-hand side of the definition to be of any (albeit the same) type. The first axiom, called `defE`, is exactly the same as equality substitution, and allows the left-hand side of a definition (the _symbol_), to be substituted by its right-hand side (the _expansion_) in any context. Instead of symmetry, the second equality axiom, the definitional operator has the introduction axiom `defI`, which 'folds' a definition, i.e. replaces the right-hand side of a definition with the left-hand-side in any context.

```Isabelle
axiomatization
  def :: ‹'a ⇒ 'a ⇒ o› (infix ‹:=› 10)
where
  defE: ‹⟦a := b; Q b⟧ ⟹ Q a› and
  defI: ‹⟦a := b; Q a⟧ ⟹ Q b›
```

This means that a definition $a := b$ is just another proposition of type `o`. For example is the sentence $3 = 0 or L := L$ a well-formed term of type `o`, as long as $L$ is a previously declared constant.

However, with the current set of axioms, a statement of the shape $a := b$ cannot possibly be proven, as there is no rule that introduces the definitional operator. However, the 'truth' of a definition can be assumed, for example in the following lemma.

```Isabelle
lemma
  assumes l_def: "l := 0"
  shows "l = 0"
apply (rule defE[OF l_def])
apply (fold isNat_def)
apply (rule nat0)
done
```

The proof first unfolds the definition of `l` using the `defE` axiom, yielding the goal state $0 = 0$, which can be proven by folding the definition of $nat$, resulting in $0 nat$, whose truth is postulated by the `nat0` axiom.

To get a 'globally visible' definition, the definition must be axiomatized. This does not axiomatize any properties about the defined symbol, it just axiomatizes the 'equivalence' of the left-hand side with the right-hand side, which, together with the axioms `defE` and `defI` means they can be substituted for each other in any context. The formalization of _GA_ in Isabelle/HOL by the authors includes a consistency proof of the axioms given any fixed finite set of definitions @GD. Thus, axiomatizing definitions maintains consistency, as long as there is only a single definition per symbol.

== Defining Arithmetic Functions in GA

Having axiomatized full _GA_ in Isabelle/Pure, the next step is to define basic arithmetic functions and prove some lemmas about them.

The recursive definitions of the arithmetic functions are straightforward and correspond to case distinctions over the second argument (of zero and non-zero).

```Isabelle
axiomatization
  add   :: "num ⇒ num ⇒ num"  (infixl "+" 60) and
  sub   :: "num ⇒ num ⇒ num"  (infixl "-" 60) and
  mult  :: "num ⇒ num ⇒ num"  (infixl "*" 70) and
  div   :: "num ⇒ num ⇒ num"                  and
  less  :: "num ⇒ num ⇒ num"  (infix "<" 50)  and
  leq   :: "num ⇒ num ⇒ num"  (infix "≤" 50)
where
  add_def:   "add x y  := if y = 0 then x else S(add x (P y))"       and
  sub_def:   "sub x y  := if y = 0 then x else P(sub x (P y))"       and
  mult_def:  "mult x y := if y = 0 then 0 else (x + mult x (P y))"   and
  leq_def:   "leq x y  := if x = 0 then 1
                          else if y = 0 then 0
                          else (leq (P x) (P y))"                    and
  less_def:  "less x y := if y = 0 then 0
                          else if x = 0 then 1
                          else (less (P x) (P y))"                   and
  div_def:   "div x y  := if x < y = 1 then 0 else S(div (x - y) y)"
```

These definitions show the necessity of the predecessor function $predf$ in _GA_. The comparison functions $<=$ and $<$ are defined to compute natural numbers, where 1 encodes truth and 0 falsehood. Note that the division function does not terminate for $y=0$.

The functions $>$ and $>=$ can now be defined in terms of $<$ and $<=$.

```Isabelle
definition greater :: "num ⇒ num ⇒ num" (infix ">" 50) where
  "greater x y ≡ 1 - (x ≤ y)"

definition geq :: "num ⇒ num ⇒ num" (infix "≥" 50) where
  "geq x y ≡ 1 - (x < y)"
```

A first property provable about the `less` function is that `x < 0` is always false, i.e. `x < 0 = 0`.

#theorem("Less than zero is false")[
  #not-less-zero
]

#proof[
  Unfolding the definition `less_def` using the `defE` axiom results in the goal state:

  1. $(cond(0=0,0,cond(x=0, 1, pred(x) < pred(0)))) = 0$

  As the condition holds, applying the `condI1` axiom results in the goal state:

  1. $0 = 0$
  2. $0 nat$

  These can both be discharged easily. The latter is the axiom `nat0` and the former is the unfolded version of this axiom, stated by the lemma `zeroRefl`.
  ```Isabelle
  lemma less_0_false: "(x < 0) = 0"
  apply (rule defE[OF less_def])
  apply (rule condI1)
  apply (rule zeroRefl)
  apply (rule nat0)
  done
  ```
]

== Termination Proofs
Due to the _habeas quid_ premises of so many axioms, an expression like $a + b$ becomes truly useful only if $a + b nat$ is provable. With the interpretation that $a nat$ is a termination certificate for $a$, $a nat ==> b nat ==> a + b nat$ is essentially a termination proof of the `add` function, conditioned on its operands also being terminating natural numbers themselves.

#theorem("Termination of " + `add`)[
  #add-term
]

#proof[
  By induction over the second argument.

  ```Isabelle
  lemma add_terminates:
    assumes x_nat: ‹x N›
    assumes y_nat: ‹y N›
    shows ‹add x y N›
  proof (rule ind[where a=y])
    show "y N" by (rule y_nat)
    show "add x 0 N"
      proof (rule defE[OF add_def])
        show "if (0 = 0) then x else S(add x P(0)) N"
          apply (rule eqSubst[where a="x"])
          apply (rule eqSym)
          apply (rule condI1)
          apply (rule zeroRefl)
          apply (rule x_nat)
          apply (rule x_nat)
          done
      qed
    show ind_step: "⋀a. a N ⟹ ((x + a) N) ⟹ ((x + S(a)) N)"
      proof (rule defE[OF add_def])
        fix a
        assume a_nat: "a N" and BC: "add x a N"
        show "if (S(a) = 0) then x else S(add x P(S(a))) N"
          proof (rule condT)
            show "S(a) = 0 B"
              apply (rule eqBool)
              apply (rule natS)
              apply (rule a_nat)
              apply (rule nat0)
              done
            show "x N" by (rule x_nat)
            show "S(add x P(S(a))) N"
              apply (rule GD.natS)
              apply (rule eqSubst[where a="x+a"])
              apply (rule eqSubst[where a="a" and b="P(S(a))"])
              apply (rule eqSym)
              apply (rule predSucInv)
              apply (rule a_nat)
              apply (fold isNat_def)
              apply (rule BC)
              apply (rule BC)
              done
          qed
      qed
  qed
  ```
]

Termination proofs of subtraction and multiplication follow the same structure, as they also recurse to the immediate predecessor in the second argument. This recursive structure exactly mirrors induction over the corresponding argument, which is why these proofs are so straightforward, despite spelling them out at the axiom level at this point.

Things get a bit more interesting with the $<=$ function, as it recurses in both arguments. The solution is to prove a stronger lemma, which universally quantifies over one argument, and then perform induction over the other argument.

#theorem("Termination of " + `leq`)[
  #leq-term
]

#proof[
  By induction over the second argument in the strengthened proposition $forall x. #h(0.5em) x <= y nat$.

  ```Isabelle
  lemma leq_terminates:
    shows "x N ⟹ y N ⟹ x ≤ y N"
  proof -
    have H: "y N ⟹ ∀x. x ≤ y N"
    proof (rule ind[where a="y"], simp)
      show "∀x'. x' ≤ 0 N"
        apply (rule forallI)
        apply (rule defE[OF leq_def])
        apply (rule condT)
        apply (rule eqBool)
        apply (assumption)
        apply (rule nat0)
        apply (rule natS)
        apply (rule nat0)
        apply (rule eqSubst[where a="0"])
        apply (rule eqSym)
        apply (rule condI1)
        apply (rule zeroRefl)
        apply (rule nat0)+
        done
      show "⋀x. x N ⟹ (∀xa. xa ≤ x N) ⟹ (∀xa. xa ≤ S(x) N)"
        proof -
          fix x
          assume H: "∀xa. xa ≤ x N"
          show "x N ⟹ ∀xa. xa ≤ S(x) N"
            proof (rule forallI)
              fix xa
              show "x N ⟹ xa N ⟹ xa ≤ S(x) N"
                apply (rule defE[OF leq_def])
                apply (rule condT)
                apply (rule eqBool)
                apply (assumption)
                apply (rule nat0)+
                apply (rule natS, rule nat0)
                apply (rule condT)
                apply (rule eqBool)
                apply (rule natS, assumption)
                apply (rule nat0)+
                apply (rule eqSubst[where a="x" and b="P S x"])
                apply (rule eqSym, rule predSucInv, assumption)
                apply (rule forallE[where a="P xa"])
                apply (rule H)
                apply (rule natP, assumption)
                done
            qed
        qed
    qed
    then show "x N ⟹ y N ⟹ x ≤ y N"
      by (rule forallE)
  qed
  ```
]

Although the key ideas of the proof are straightforward -- the strengthening of the proposition in line 4 and applying induction over the second argument on line 5 are only one line each -- this is clouded by a lot of effort to discharge the _habeas quid_ premises and other simple things like replacing a $pred(suc(x))$ with $x$ in a subexpression. The latter currently requires an appication of equality substitution, an application of equality symmetry, and then applying the `predSucInv` axiom.

This issue is tackled in @tooling, where a lot of proof automation and tactics are introduced to simplify reasoning.

The next goal is to prove termination of the division function. This poses two new challenges.

1. The function does not terminate for y = 0.
2. The recursive pattern is does not mirror induction, i.e. it does not recurse to the immediate predecessor.

The former is solved relatively easily. One option is to add $not y = 0$ as an explicit assumption to the termination proof. Another, more elegant, option is to restate the theorem in the following way: $x nat ==> y nat ==> "div" x " " suc(y) nat$. Now, it holds for any natural numbers $x$ and $y$.

To solve the second problem, a strong induction lemma needs to be proven first. This then allows assuming the induction hypothesis for any $y' <= y$ when proving the statement for $suc(y)$.

The only difference to the induction axiom is that the hypothesis in the induction step is stronger -- instead of $ctxt(x)$ it is now $and.big y. #h(0.5em) y <= x = 1 ==> ctxt(y)$ (in Isabelle notation) or $y <= x = 1 tack.r ctxt(y)$ (in natural deduction style notation).

#theorem("Strong Induction")[
  #strong-induct
]

#proof[
  By induction over $a$ in the strengthened object-level proposition $forall x. #h(0.5em) (x <= a = 1 ) --> ctxt(x)$.
 
  ```Isabelle
  lemma strong_induction:
    shows "a N ⟹ Q 0 ⟹ (⋀x. x N ⟹ (⋀y. y N ⟹ y ≤ x = 1 ⟹ Q y) ⟹ (Q S(x))) ⟹ Q a"
  proof -
    have q: "a N ⟹ Q 0 ⟹ (⋀x. x N ⟹ (⋀y. y N ⟹ y≤x = 1 ⟹ Q y) ⟹ (Q S(x))) ⟹
             ∀x. (x ≤ a = 1) ⟶ Q x"
      apply (rule ind[where a="a"], assumption)
      apply (rule forallI implI)+
      apply (rule eqBool, rule leq_terminates, assumption)
      apply (rule nat0, rule natS, rule nat0)
      proof -
        fix x
        show "x N ⟹ x ≤ 0 = 1 ⟹ Q 0 ⟹ Q x"
          apply (rule eqSubst[where a="0" and b="x"], rule eqSym)
          apply (rule leq_0, assumption+)
          done
        show "a N ⟹ x N ⟹
              Q 0 ⟹
              (⋀x. x N ⟹ (⋀y. y N ⟹ y ≤ x = 1 ⟹ Q y) ⟹ Q (S x)) ⟹
              ∀xa. xa ≤ x = 1 ⟶ Q xa ⟹
              ∀xa. xa ≤ (S x) = 1 ⟶ Q xa"
          apply (rule forallI implI)+
          apply (rule eqBool, rule leq_terminates, assumption)
          apply (rule natS, assumption)
          apply (rule natS, rule nat0)
          proof -
            fix xa
            assume xa_nat: "xa N"
            assume hyp: "∀x'. x' ≤ x = 1 ⟶ Q x'"
            assume step: "(⋀x. x N ⟹ (⋀y. y N ⟹ y ≤ x = 1 ⟹ Q y) ⟹ Q (S x))"
            assume xa_leq_sx: "xa ≤ S x = 1"
            have H: "xa ≤ x = 1 ⟶ Q xa"
              by (rule forallE[where a="xa"], rule hyp, rule xa_nat)
            show "x N ⟹ Q xa"
              apply (rule disjE1[where P="xa ≤ x = 1" and Q="¬ xa ≤ x = 1"])
              apply (fold GD.bJudg_def)
              apply (rule eqBool)
              apply (rule leq_terminates)
              apply (rule xa_nat, assumption)
              apply (rule natS, rule nat0)
              apply (rule implE[where a="xa ≤ x = 1"])
              apply (rule H)
              apply (assumption)
              proof -
                assume xa_not_leq_x: "¬ xa ≤ x = 1"
                have xa_eq_sx: "x N ⟹ xa = S x"
                  apply (rule leq_suc_not_leq_implies_eq)
                  apply (rule xa_nat, assumption)
                  apply (rule xa_not_leq_x)
                  apply (rule xa_leq_sx)
                  done
                have q_sx: "x N ⟹ Q S(x)"
                  apply (rule step)
                  apply (assumption)
                  apply (rule implE)
                  apply (rule forallE)
                  apply (rule hyp, assumption+)
                  done
                show "x N ⟹ Q xa"
                  apply (rule eqSubst[where a="S x" and b="xa"])
                  apply (rule eqSym)
                  apply (rule xa_eq_sx, assumption)
                  apply (rule q_sx, assumption)
                  done
              qed
          qed
      qed
      assume step: "(⋀x. x N ⟹ (⋀y. y N ⟹ y≤x = 1 ⟹ Q y) ⟹ (Q S(x)))"
      show "a N ⟹ Q 0 ⟹ Q a"
        apply (rule implE[where a="a ≤ a = 1"])
        apply (rule forallE[where Q="λx. (x ≤ a = 1) ⟶ Q x"])
        apply (rule q)
        apply (assumption+)
        apply (rule step)
        apply (assumption+)
        apply (rule leq_refl)
        apply (assumption)
        done
  qed
  ```
]

It is necessary to use the object level connectives (i.e. $forall$ instead of $and.big$ and $-->$ instead of $==>$) in the stronger proposition induction is performed over, since the induction axiom only works over expressions of type `o` (i.e. the object-level truth value type) and not of type `prop` (which the meta-level connectives $==>$ and $and.big$ are defined on). Thus, applying the _GA_ induction axiom on the corresponding meta-level proposition $and.big x. #h(0.5em) (x <= a = 1) ==> ctxt(x)$ would not work. It is simply a type error.

The idea of this proof is again very straightforward, but spelling it out using the axioms is lengthy and challenging.

Using the strong induction lemma, termination of the division function defined earlier can be proven.

#theorem("Termination of " + `div`)[
  #div-term
]

#proof[
  By strong induction over the second argument.

  ```Isabelle
  lemma div_terminates:
    shows "x N ⟹ y N ⟹ div x S(y) N"
  apply (rule strong_induction[where a="x"], assumption)
  apply (rule defE[OF div_def], simp)
  proof -
    fix x
    assume hyp: "⋀ya. ya N ⟹ ya ≤ x = 1 ⟹ (div ya (S y) N)"
    show "x N ⟹ y N ⟹ div (S x) (S y) N"
      apply (rule defE[OF div_def])
      apply (rule condT, simp)
      apply (rule hyp, simp+)
      done
  qed
  ```
]

This proof is much shorter than the previous ones despite significantly higher complexity. The magic lies in the `simp` method, which invokes the simplifier. This theorem was proven much later than the previous termination proofs and using a lot of automation. The simplifier applies numerous previously proven lemmas here, for example to automatically solve the base case of $"div" 0 " " suc(y) nat$.

@tooling goes into how automation is introduced into an axiomatized logic in _Pure_.

The authors of _GA_ place a lot of emphasis on primitive recursion as a 'benchmark' for the expressivitiy of _GA_. Namely, they proved that all primitive recursive functions can be expressed and proven terminating in _GA_. While such a proof is out of reach for this formalization, it is more fitting for this formalization to show that _GA_ can actually go beyond that. The Ackermann function is famously not primitive recursive @ack. With the tooling from @tooling, a termination proof of the Ackermann function is surprisingly simple to spell out in _GA_, using the standard approach of nested induction.

Consider the following standard definition of the Ackermann function in _GA_.

```Isabelle
axiomatization
  ack :: "num ⇒ num ⇒ num"
where
  ack_def: "ack x y := if x = 0 then y + 1
                       else if y = 0 then ack (P x) 1
                       else ack (P x) (ack x (P y))"
```

#theorem("Termination of " + `ack`)[
  #ack-term
]

#proof[
  By nested induction using a helper lemma.

  The outer induction ranges over the second argument and proves the stronger statement $forall n. #h(0.5em) "ack" m " " n nat$.
  
  ```Isabelle
  lemma [simp]: "n N ⟹ ack 0 n = n + 1"
  by (unfold_def ack_def, simp)

  lemma "n N ⟹ m N ⟹ ack m n N"
  apply (rule forallE[where a="n"])
  apply (induct m)
  apply (rule forallI, simp)
  apply (rule forallI)
  proof -
    fix x z
    show "x N ⟹ ∀y. ack x y N ⟹ z N ⟹ ack (S x) z N"
      apply (induct z)
      apply (unfold_def ack_def)
      apply (subst rule: condI2, simp)
      apply (subst rule: condI1, simp+)
      apply (rule forallE[where a="1"], simp)
      apply (rule forallE[where a="1"], simp)
      apply (subst rule: condI1, simp+)
      apply (rule forallE[where a="1"], simp)
      apply (rule forallE[where a="1"], simp)
      apply (unfold_def ack_def)
      apply (subst rule: condI2, simp+)
      apply (subst rule: condI2, simp+)
      apply (rule forallE, simp)+
      apply (rule forallI, simp+)
      apply (rule forallE, simp)
      done
  qed
  ```
]
