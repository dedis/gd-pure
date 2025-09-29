// =====================================================
// The inductive datatype chapter. Formalizes required
// number theory to be able to express cantor pairings.
// Then, writes a package that encodes arbitrary data-
// types into the formalized integers.
// =====================================================

#import "../style.typ": *
#import "../formalisms.typ": *
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#show: codly-init.with()
#codly(zebra-fill: none)

= Encoding Inductive Datatypes in GA
<inductive>
With _Isabelle/GA_ now being a more convenient proof assistant, the next goal is to make it easier to extend the domain of discourse beyond just natural numbers. Modern proof assistants, like _Isabelle/HOL_ or Rocq, contain powerful definitional mechanisms that allow for straightforward specification of things like inductive datatypes, recursive predicates, infinitary sets, and so on.

These definitional packages are effectively _theory compilers_, as they take a high-level definition, like an inductive datatype declaration, and map it to definitions, axioms, and automatically proven lemmas, encoding the high-level definition in lower-level existing primitives.

The goal of this chapter is to take the key steps towards such a definitional mechanism for inductive datatypes in _Isabelle/GA_ and encode them into the existing natural number theory. That is, any inductive datatype should be definable and conveniently usable without adding any axioms.

The roadmap towards this lofty goal is as follows:

- Formalize enough basic number theory to be able to define cantor pairings and the key properties about them.
- Manually encode an inductive datatype into the natural numbers using the cantor pairing infrastructure from the first step. Define a type membership predicate, define the constructors as cantor pairings of their arguments and prove the necessary lemmas (such as all constructors being disjoint, the type membership predicate returning true for all values of the constructors, induction on the datatype, and so on).
- Plan out a semantic type system consisting of encoded types embedded within the single syntactic type of `num` in _Pure_ and introduce tooling for it.
- Write a definitional package that parses an inductive datatype declaration and compiles it into the necessary definitions, lemmas, and accompanying proofs.

== Inductive Datatypes In General
<inductive-general>
In general, an inductive datatype is specificed by a list of constructors, where each constructor has a finite number of arguments (possibly zero), each constrained by a type (which may itself be an inductive datatype, and in particular may be the datatype currently being defined). The datatype itself is then given by the least fixed point of the monotone operator that closes a set under these constructors @paulson-inductive.

For example, the following is an inductive definition of a list datatype:

```Pseudo
datatype List =
  Nil
| Cons Nat List
```

There are two constructors, one called `Nil` with no arguments (i.e. a constant), and one called `Cons` with two arguments, one of type `Nat` and one of type `List` itself. The set of `List`s is the least fixed point of the operator that closes under these two constructors. Intuitively, this least fixed point is the limit of successive approximations; starting with the empty set, the first closure step adds `Nil`, the next adds all `List`s of the form `Cons n Nil`, the next adds all lists of the form `Cons n (Cons m Nil)`, and so on, eventually producing all finite lists.

An inductive datatype defined in this way satisfies the following properties:

- *Closure* (generation): applying a constructor to arguments (that are valid elements of their respective types) yields a valid element of the type, e.g. $n nat ==> "is_list xs" ==> "is_list (Cons n xs)"$ and $"is_list Nil"$.
- *Exhaustiveness*: every element of the datatype must be built from some constructor; there are no “extra” elements beyond the closure.
- *Distinctness*: different constructors build different elements, e.g. $"Nil" eq.not "Cons" n "xs"$ for any $n$, $"xs"$.
- *Injectivity*: each constructor is injective in its arguments, e.g. $"Cons" n "xs" eq "Cons" n "xs" ==> n eq m and "xs" eq "ys"$.
- *Induction principle*: properties of elements of the datatype can be proved by showing they hold for each constructor case, assuming the property for recursive arguments.

The goal now is to find an encoding of an inductive datatype into the natural numbers such that all these properties are fulfilled and can be proved in _GA_ itself without adding any axioms.

== Encoding: Constructors
The constructor encoding is responsible for ensuring the latter three properties *distinctness*, *injectivity*, and the *induction principle*. The first two can be ensured by an injective encoding function, and the third is ensured by an encoding function that is strictly monotonous in all recursive arguments (i.e. the ones of the same type).

The encoding of choice is a right-associative extension to the Cantor pairing function to Cantor tuples, where each constructor with arguments $a_1,...,a_n$ is encoded as follows:

$ angle.l "type_tag", "constructor_tag", a_1, ..., a_(n-1), a_n angle.r  $

Due to right-associativity, this is equivalent to :

$ angle.l "type_tag", angle.l "constructor_tag",  angle.l a_1, angle.l ..., angle.l a_(n-1), a_n angle.r ... angle.r angle.r angle.r angle.r $

Where the notation $angle.l dot,dot angle.r$ is the well-known Cantor pairing function, which is a bijection on the natural numbers and strictly monotonous in both arguments for $n >= 2$. It is defined as follows @cpair:

#definition-box("Cantor Pairing Function")[
  #align(center)[
    #cpair
  ]
]

== Encoding: Type Membership Predicates
Since the values of the inductive datatypes are encoded as natural numbers (`num`), they must be of the syntactic Isabelle type `num` themselves. Thus, to determine 'type membership', e.g. whether a given `num` is considered an encoded `List`, there has to be a predicate that decides this. For `List`, such a type membership predicate shall be called `is_list`, and the idea is that $"is_list" a$ is a proposition-level (`o`) type membership certificate, similar to how $x nat$ is a certificate for a terminating natural number. Thus, _GA_ can be viewed as having a 'dynamic' type system embedded within the propositional syntax itself, where the types are $bool$, $nat$, and now also inductive datatypes such as `List`.

Since the type membership predicate effectively determines the inhabitants of the type, it is responsible for the first two properties, *closure* and *exhaustiveness*. Formally, the type membership predicate, which is called $"is_"tau$ for a given coded type $tau$, should fulfill the following properties. For each $tau$ constructor $C_i$ and its arguments $a_(i,1),...,a_(i,n_i)$ with their respective type constraints $tau_(i,1),...,tau_(i,n_i)$:

1. #text[
  *Closure of the type membership predicate*:
  For each constructor $C_i$, if all its arguments fulfill their corresponding type membership predicates, then $C_i$ applied to these arguments must fulfill its type membership predicate:
  $ "is_"tau_"i1" gap a_"i1" ==> ... ==> "is_"tau_"in" gap a_"in" ==> "is_"tau gap (C_i gap a_"i1" gap ... gap a_"in") $
  ]

2. #text[
  *Exhaustiveness of the type membership predicate*:
  If the type membership predicate $"is_"tau$ is fulfilled by a value $x$, then there must exist a constructor and a set of corresponding arguments fulfilling their type membership predicates, such that $x$ equals the constructor applied to these arguments.

  $ &"is_"tau gap x ==> \
   &exists a_(1,1) gap ... gap a_(1,n_1). gap "is_"tau_(1,1) gap a_(1,1) and ... and "is_"tau_(1,n_1) gap a_(1,n_1) and x = (C_1 gap a_(1,1) gap ... gap a_(1,n_1)) &or \
   &... quad &or \
   &exists a_(m,1) gap ... gap a_(m,n_m). gap "is_"tau_(m,1) gap a_(m,1) and ... and "is_"tau_(m,n_m) gap a_(m,n_m) and x = (C_m gap a_(m,1) gap ... gap a_(m,n_m))
  $
  ]

For the `List` type, these two criteria evaluate to:
- For `Nil`: $"is_list Nil"$ \
   For `Cons`: $n nat ==> "is_list xs" ==> "is_list Cons n xs"$
- $"is_list x" ==> x = "Nil" or exists n "xs". gap n nat and "is_list xs" and x = ("Cons n xs")$

For an inductive datatype $tau$, the type membership predicate $"is_"tau$ must invert the encoding for each constructor, i.e. treat it like a Cantor tuple, extract its elements, and check if it matches the encoding. This guarantees closure, while the bijectivity of the encoding guarantees exhaustiveness. We will make this more precise and prove it explicitly later. 

For the `List` datatype, the `is_list` predicate fulfilling these properties is the following:

```Isabelle
is_list_def: "is_list x := if x = 0
                             then False
                           else if x = Nil
                             then True
                           else if is_cons x
                             then True
                           else False"
and
is_cons_def: "is_cons x := (cpi 1 x = list_type_tag)
                            ∧ (cpi 2 x = list_cons_tag)
                            ∧ ((cpi 3 x) N)
                            ∧ (is_list (cpi' 4 x))"
```

Where $"cpi" i x$ extracts the i'th element of a Cantor tuple (with at least $i+1$ elements) and $"cpi" i x$ extracts the i'th element of a Cantor tuple with exactly $i$ elements.

The general idea of the type membership predicate is to check for each constructor, whether the argument matches its encoding shape, and if so, whether all (encoded) arguments recursively fulfill their respective predicates.
== Cantor Tuples in GA
So far, we have identified the required properties to make an inductive datatype encoding work and have then identified a scheme for defining constructors and a type membership predicate that are expected to fulfill all these properties. Next, we have to formalize the basis for this encoding, namely Cantor pairings and the associated infrastructure to be able to 'extract' elements from one.

Since the Cantor pairing function is bijective, there is an inverse function mapping each natural number $z$ to the unique pair $(x,y)$ with $z = angle.l x, y angle.r$. In the following, let $"cpx"(z)$ denote the first component of this inverse, i.e. the unique $x$ such that there exists an $x'$ with $z = angle.l x, x' angle.r$. Analogously, let $"cpy"(z)$ denote the second component of the inverse.

The standard definition of Cantor pairs and the inverses $"cpx"(z)$ and $"cpy"(z)$ are analytic closed form expressions, which is what the initial formalization in GA used as well. However, it turns out that in order to prove properties about these functions when they are defined in such a way, a highly mature library of arithmetic lemmas is required. This was especially apparent when trying to prove the growth property $x < angle.l x, y angle.r$ (for $x >= 2$). However, maybe unexpectedly, many of these properties turned out to be much easier to prove in _GA_ when these functions are defined recursively.

Thus, the following recursive _GA_ definition of a Cantor pair is used from now on:

```Isabelle
cpair_def: "cpair x y := if y = 0 then div (x * S(x)) 2
                         else cpair x P(y) + x + y + 2"
```

Termination follows by induction on the second argument.

#theorem("Termination of " + `cpair`)[
  #cpair-term
]

#proof[
  ```Isabelle
  lemma cpair_terminates [auto]: "x N ⟹ y N ⟹ ⟨x, y⟩ N"
  apply (induct y, simp)
  apply (unfold_def cpair_def, simp)+
  done
  ```
]

To provide syntax for general Cantor k-tuples ($angle.l a_1, a_2, ..., a_k angle.r$), the following snippet translates such tuples into right associative nested `cpair`s.

```Isabelle
nonterminal cpair_args

syntax
  "_cpair"      :: "num ⇒ cpair_args ⇒ num"        ("⟨_,_⟩")
  "_cpair_arg"  :: "num ⇒ cpair_args"               ("_")
  "_cpair_args" :: "num ⇒ cpair_args ⇒ cpair_args" ("_,_")
translations
  "⟨x, y⟩" == "CONST cpair x y"
  "_cpair x (_cpair_args y z)" == "_cpair x (_cpair_arg (_cpair y z))"
```

The inverse functions $"cpx"(z)$ and $"cpy"(z)$ can also be defined mutually recursively:

```Isabelle
cpx_def: "cpx x := if x = 0 then 0
                   else if cpx (P x) = 0 then S(cpy P(x))
                   else P(cpx (P x))" and
cpy_def: "cpy x := if cpx (P x) = 0 then 0
                   else S(cpy (P x))"
```

Despite the mutually inductive structure, termination is quite straightforward, as each recursive call is on a smaller argument.

#theorem("Termination of " + `cpx` + " and " + `cpy`)[
  #cpx-cpy-term
]

#proof[
  The termination proof is mutual as well, by induction on $"cpx" x nat and "cpy" x nat$.

  ```Isabelle
  lemma cpx_cpy_terminate: "x N ⟹ (cpx x N) ∧ (cpy x N)"
  apply (induct x, simp)
  apply (unfold_def cpx_def, simp)
  apply (subst rule: condI2)
  apply (rule condT, simp)
  apply (rule conjE1, simp)
  apply (rule conjE2, simp)
  apply (rule conjE1, simp)
  apply (rule condT, simp)
  apply (rule conjE1, simp)
  apply (rule conjE2, simp)
  apply (rule conjE1, simp)
  apply (unfold_def cpy_def, simp)
  apply (rule condT, simp)
  apply (rule conjE1, simp)
  apply (rule conjE2, simp)
  done
  ```
]

Before proving the critical injectivity property of the `cpair` function, the two following lemmas are required:

#theorem("Projection Lemmas for " + `cpx` + " and " + `cpy`)[
 #cpx-cpy-proj 
]

These are well-known properties of the encoding and are given without explicit proof in _GA_, mostly due to time constraint for this thesis. A lemma in Isabelle can be stated and subsequently used without proof by using the `sorry` keyword.

```Isabelle
lemma cpx_proj [simp]: "a N ⟹ b N ⟹ cpx ⟨a, b⟩ = a"
sorry

lemma cpy_proj [simp]: "a N ⟹ b N ⟹ cpy ⟨a, b⟩ = b"
sorry
```

Now, injectivity can be proved:

#theorem("Injectivity of " + `cpair`)[
  #cpair-inj
]

#proof[
  ```Isabelle
  lemma cpair_inj:
    assumes eq: "⟨a, b⟩ = ⟨c, d⟩"
    shows "a N ⟹ b N ⟹ c N ⟹ d N ⟹ a = c ∧ b = d"
  proof -
    have H: "a N ⟹ b N ⟹ cpx ⟨a, b⟩ = cpx ⟨c, d⟩"
      by (rule eqSubst[OF eq], simp)
    have a_eq_c: "a N ⟹ b N ⟹ c N ⟹ d N ⟹ a = c"
      apply (rule eqSubst[where a="cpx ⟨a, b⟩" and b="a"], simp)
      apply (rule eqSubst[where a="cpx ⟨c, d⟩" and b="c"], simp)
      apply (rule H, simp)
      done
    have H2: "a N ⟹ b N ⟹ cpy ⟨a, b⟩ = cpy ⟨c, d⟩"
      by (rule eqSubst[OF eq], simp)
    have b_eq_d: "a N ⟹ b N ⟹ c N ⟹ d N ⟹ b = d"
      apply (rule eqSubst[where a="cpy ⟨a, b⟩" and b="b"])
      apply (rule cpy_proj, assumption+)
      apply (rule eqSubst[where a="cpy ⟨c, d⟩" and b="d"])
      apply (rule cpy_proj, assumption+)
      apply (rule H2, assumption+)
      done
    show "a N ⟹ b N ⟹ c N ⟹ d N ⟹ a = c ∧ b = d"
      apply (rule conjI)
      apply (rule a_eq_c)
      apply (simp)
      apply (rule b_eq_d)
      apply (simp)
      done
  qed
  ```
]

The next key property is that a Cantor pair is strictly larger than both its argument (for $x >= 2$ and $y >= 1$). This is critical for proving the induction lemma for `List`s later.

#theorem("Cantor pairing strictly dominates components")[
  #cpair-strict-mono-l-r
]

#proof[
  ```Isabelle
  lemma cpair_strict_mono_r [simp]: "x N ⟹ y N ⟹ (S y) < ⟨x, (S y)⟩ = 1"
  proof (induct y)
    case Base
      show "x N ⟹ y N ⟹ 1 < ⟨x,1⟩ = 1"
        apply (rule less_le_trans[where b="2"], simp)
        apply (unfold_def cpair_def, simp)
        done
  next
    case (Step xa)
    show "x N ⟹ y N ⟹ xa N ⟹ S xa < ⟨x, (S xa)⟩ = 1 ⟹ S S xa < ⟨x, (S S xa)⟩ = 1"
      apply (unfold_def cpair_def, simp)
      apply (rule less_le_trans[where b="S S xa + 2"])
      apply (simp add: add_assoc)+
      done
  qed
  ```

  ```Isabelle
  lemma [simp]:
    "x N ⟹ y N ⟹ S S x < ⟨(S S x), y⟩ = 1"
  apply (induct y)
  apply (unfold_def cpair_def, simp)
  apply (rule less_le_trans[where b="div (2 * (S S S x)) 2"], simp)
  apply (simp add: mult_div_inv)
  apply (rule leq_mono_div, simp+)
  apply (unfold_def cpair_def, simp)
  done
  ```
]

The next key lemma to prove is the reconstruction lemma, stating that the pair $("cpx" z, "cpy" z)$ constitutes the inverse of the Cantor pairing.

#theorem("Reconstruction Lemma")[
  #reconstr-lemma
]

#proof[
  Using surjectivity of the Cantor pairing function and the projection lemmas.

  ```Isabelle
  lemma [auto]: "z N ⟹ z = ⟨cpx z, cpy z⟩"
  apply (rule existsE[where Q="λb. z=⟨cpx z,b⟩"])
  apply (rule existsE[where Q="λc. ∃i. z=⟨c,i⟩"])
  apply (simp)
  proof -
    fix a
    show "z N ⟹ a N ⟹ ∃i. z = ⟨a,i⟩ ⟹ ∃i. z = ⟨cpx z,i⟩"
      apply (subst "a = cpx z")
      apply (rule existsE[where Q="λi. z=⟨a,i⟩"])
      apply (simp+)
      done
    show "z N ⟹ a N ⟹ z = ⟨cpx z,a⟩ ⟹ z = ⟨cpx z,cpy z⟩"
      apply (subst "a = cpy z")
      apply (subst "⟨cpx z, a⟩ = z")
      apply (subst rule: cpy_proj)
      done
  qed
  ```
]

The proof of this theorem relies on the surjectivity of the Cantor pairing function on the natural numbers, which is another of its well-known properties. In the GA formalization, this fact is stated without proof, as proving it would have exceeded the scope and time constraints of this thesis.

#theorem("Surjectivity of the Cantor pairing function")[
  #cpair-surj 
]

```Isabelle
lemma cpair_surjective [auto]: "a N ⟹ ∃b c. a = ⟨b,c⟩"
sorry
```

To project the $i$-th component of a Cantor $k$-tuple, we first define $"cpi'" i$ to return the $i$-th element of a right-associated Cantor $i$-tuple.

```Isabelle
cpi'_def: "cpi' n z := if n = 0 then 0
                       else if n = 1 then z
                       else cpy (cpi' (n-1) z)"
```

Intuitively, `cpi' i` performs $i$ successive selections of the second component (`cpy`) of the outermost Cantor pair. If the value is a Cantor $i$-tuple, the result is exactly the $i$-th element. In the other case where the value is a Cantor $k$-tuple with $k > i$, the term $"cpi'" i gap z$ yields the suffix Cantor $k-i+1$-tuple beginning at the $i$-th position and thus an additional `cpx` application is required to extract the $i$-th position. This is what the `cpi` function does:

```Isabelle
definition cpi :: "num ⇒ num ⇒ num" where
  "cpi i x ≡ cpx (cpi' i x)"
```

The termination proof of `cpi'` is by induction over the first argument and omitted here, although it is included in the Isabelle formalization. The next interesting lemma is a version of the reconstruction lemma for Cantor 4-tuples. The lemma is stated for 4-tuples specifically, since the `Cons` constructor of the `List` datatype is encoded as a Cantor 4-tuple.

#theorem("Reconstruction lemma for Cantor 4-tuples")[
  #reconstr-4-tuple
]

#proof[
  Stated in a slightly different way for ease of application. Using the reconstruction lemmas for `cpx` and `cpy`.

  ```Isabelle
  lemma cp4_reconstr: "x N ⟹ a N ⟹ b N ⟹ c N ⟹ d N ⟹ cpi 1 x = a ⟹ cpi 2 x = b ⟹
         cpi 3 x = c ⟹ cpi' 4 x = d ⟹
         x = ⟨a,b,c,d⟩"
  apply (rule cpair_eq_I, simp)
  apply (subst "cpi 1 x = cpx x", auto)
  apply (rule cpair_eq_I, simp)
  apply (subst "cpi 2 x = cpx (cpy x)", auto)
  apply (rule cpair_eq_I, simp)
  apply (subst "cpi 3 x = cpx (cpy (cpy x))", auto)
  apply (subst "cpi' 4 x = cpy (cpy (cpy x))", auto)
  done
  ```
]

== The Encoded List Datatype
With the Cantor pairing infrastructure, everything is ready for defining the full `List` datatype and proving all the properties required for an inductive datatype in @inductive-general.

`List` is introduced as a type synonym for the `num` type. This means Isabelle treats `List` as `num` internally, but it can still be written as a type by the user. The definition of the constructors and the `is_list` predicate were already given previously and are restated here for completeness sake.

```Isabelle
type_synonym List = num

definition list_type_tag where
  "list_type_tag ≡ 1"

definition list_nil_tag where
  "list_nil_tag ≡ 1"

definition list_cons_tag where
  "list_cons_tag ≡ 2"

definition Nil :: "List" where
  "Nil ≡ ⟨list_type_tag,list_nil_tag⟩"

definition Cons :: "num ⇒ List ⇒ List" where
  "Cons n xs ≡ ⟨list_type_tag,list_cons_tag,n,xs⟩"

axiomatization
  is_list :: "num ⇒ o" and
  is_cons :: "num ⇒ o"
where
  is_cons_def: "is_cons x := (cpi 1 x = list_type_tag)
                              ∧ (cpi 2 x = list_cons_tag)
                              ∧ ((cpi 3 x) N)
                              ∧ (is_list (cpi' 4 x))" and
  is_list_def: "is_list x := if x = 0
                               then False
                             else if x = Nil
                               then True
                             else if is_cons x
                               then True
                             else False"
```

The first important lemma states termination of the `is_list` predicate, which essentially means that type membership checking is decidable.

#theorem("Termination of " + `is_list` + " and " + `is_cons`)[
  #is-list-cons-term
]

#proof[
  First, prove that `Nil` and `Cons` are terminating natural numbers for any arguments (`nil_nat` and `cons_nat`). Then, prove termination of `is_list` and `is_cons` mutually inductively using the strong induction lemma.
  
  ```Isabelle
  lemma nil_nat [auto]: "Nil N"
  unfolding Nil_def list_type_tag_def by simp

  lemma cons_nat [auto]: "n N ⟹ xs N ⟹ Cons n xs N"
  unfolding Cons_def list_type_tag_def by simp

  lemma list_cons_term [auto]: "x N ⟹ (is_list x B) ∧ (is_cons x B)"
  proof (induct strong x)
    case Base
      show "x N ⟹ (is_list 0 B) ∧ (is_cons 0 B)"
        apply (unfold_def is_list_def)
        apply (unfold_def is_cons_def)
        apply (unfold_def is_list_def)
        apply (simp)
        done
  next
    case (Step xa)
      fix y
      assume hyp: "(⋀y. y N ⟹ y ≤ xa = 1 ⟹ (is_list y B) ∧ (is_cons y B))"
      from Step show ?case
        apply (unfold_def is_list_def)
        apply (unfold_def is_cons_def)
        apply (simp)
        apply (rule condTB, simp)+
        apply (rule conjE1, rule hyp, simp, rule le_suc_implies_leq, simp)+
        done
  qed

  ``` 
]

=== Proving Constructor Distinctness

Distinctness follows immediately from disjoint constructor tags in the encoding.

#theorem("List constructor distinctness")[
  #list-cons-distinct
]

#proof[
  ```Isabelle
  lemma [auto]: "n N ⟹ xs N ⟹ ¬ Nil = Cons n xs"
  unfolding Nil_def Cons_def by simp

  lemma [auto]: "n N ⟹ xs N ⟹ ¬ Cons n xs = Nil"
  unfolding Nil_def Cons_def by simp
  ```
]

=== Proving Injectivity of `Cons`

Injectivity reduces to injectivity of the Cantor pairing at each nesting level.

#theorem("Injectivity of Cons")[
  #cons-injectivity
]

#proof[
  ```Isabelle
  lemma
    "n N ⟹ m N ⟹ xs N ⟹ ys N ⟹ Cons n xs = Cons m ys ⟹ n = m ∧ xs = ys"
  unfolding Cons_def
  apply (rule cpair_inj)
  apply (rule cpair_inj_r, rule cpair_inj_r, simp)
  done
  ```
]

=== Proving Exhaustiveness

Exhaustiveness is essentially a case-distinction lemma and states that every element recognized by `is_list` is either `Nil` or has `Cons`-shape with well-typed arguments. We first prove a decoding lemma for `Cons`-shapes, then a decoding lemma for `List` in general, and finally the full case distinction rule.

#theorem("List exhaustiveness")[
  #list-exhaustiveness
]

#proof[
  ```Isabelle
  lemma cons_decode [auto]:
    "is_cons x ⟹ x N ⟹ ∃n xs. ((n N) ∧ is_list xs ∧ x = Cons n xs)"
  apply (rule existsI[where a="cpi 3 x"], simp+)
  apply (rule existsI[where a="cpi' 4 x"], simp+)
  apply (unfold Cons_def)
  apply (subst rule: cons_1_tag)
  apply (subst rule: cons_2_2)
  apply (rule cp4_reconstr, simp+)
  done

  lemma list_decode: "x N ⟹ is_list x ⟹ (x = Nil) ∨ (∃n xs. (n N) ∧ is_list xs ∧ (x = Cons n xs))"
  apply (rule implE[where a="is_list x"])
  apply (unfold_def is_list_def)
  apply (cases bool: "x=Nil", simp+)
  apply (rule implI, simp)
  apply (rule disjI1, simp)
  apply (cases bool: "is_cons x", simp+)
  apply (rule implI)
  apply (rule condTB, simp)+
  apply (simp+)
  apply (rule implI, simp)
  apply (rule exF[where P="False"], simp)
  done
  ```
]

#theorem("List cases", font_size: 0.9em)[
  #list-cases 
]

#proof[
  ```Isabelle
  lemma cases_list [case_names _ HQ Nil Cons, cases]: "is_list x ⟹
         (x N) ⟹
         (x = Nil ⟹ Q) ⟹
         (⋀n xs. n N ⟹ xs N ⟹ is_list xs ⟹ x = Cons n xs ⟹ Q)
         ⟹ Q"
  apply (rule disjE1[OF list_cases], simp, assumption)
  apply (rule existsE[where Q="λn. ∃xs. (n N) ∧ is_list xs ∧ x = Cons n xs"])
  apply (assumption)
  proof -
    fix a
    show "is_list x ⟹
       (x = Nil ⟹ Q) ⟹
       (⋀n xs. n N ⟹ xs N ⟹ is_list xs ⟹ x = Cons n xs ⟹ Q) ⟹
       ∃n xs. (n N) ∧ is_list xs ∧ x = Cons n xs ⟹
       a N ⟹ ∃xs. (a N) ∧ is_list xs ∧ x = Cons a xs ⟹ Q"
      apply (rule existsE[where Q="λxs. (a N) ∧ is_list xs ∧ x = Cons a xs"])
      apply (assumption)
      proof -
        fix aa
        show "
        (⋀n xs. n N ⟹ xs N ⟹ is_list xs ⟹ x = Cons n xs ⟹ Q) ⟹
          aa N ⟹ (a N) ∧ is_list aa ∧ x = Cons a aa ⟹ Q"
          apply (rule Pure.meta_mp[where P="a N"])
          apply (rule Pure.meta_mp[where P="is_list aa"])
          apply (rule Pure.meta_mp[where P="x = Cons a aa"])
          apply (assumption)
          apply (rule conjE2, simp)
          apply (rule conjE2, rule conjE1, simp)
          apply (rule conjE1, rule conjE1, simp)
          done
      qed
  qed
  ```
]

=== Proving Closure

Closure states that every constructor application yields an element of the encoded datatype. For `List`, this is immediate from the definition of `is_list` and the `Cons`-shape predicate.

#theorem("List closure")[
  #list-closure
]

#proof[
  ```Isabelle
  lemma [auto]: "¬ Nil = 0"
  unfolding Nil_def by simp

  lemma [auto]: "is_list Nil"
  by (unfold_def is_list_def, simp)
  ```

  ```Isabelle
  lemma [auto]: "n N ⟹ xs N ⟹ is_list xs ⟹ is_cons (Cons n xs)"
  unfolding Cons_def by (unfold_def is_cons_def, simp)

  lemma cons_is_list [auto]:
    "n N ⟹ xs N ⟹ is_list xs ⟹ is_list (Cons n xs)"
  apply (unfold_def is_list_def)
  apply (unfold_def is_cons_def)
  apply (unfold Cons_def)
  apply (simp)
  done
  ```
]

=== Proving `List` Induction

We derive an induction principle for `List` by strong induction on the `num` code, using the growth property $"xs" < "Cons" n "xs" = 1$ to justify the recursive call.

#theorem("List induction")[
  #list-induction
]

#proof[
  ```Isabelle
  lemma [simp]: "xs N ⟹ is_list xs ⟹ n N ⟹ xs < Cons n xs = 1"
  unfolding Cons_def by simp
  ```

  ```Isabelle
  lemma [case_names _ HQ Nil Cons, induct]:
    "is_list a ⟹ a N ⟹ Q Nil ⟹ (⋀x xs. x N ⟹ xs N ⟹ is_list xs ⟹ Q xs ⟹ Q (Cons x xs))
     ⟹ Q a"
  apply (rule implE[where a="is_list a"])
  apply (induct strong a)
  apply (rule implI, simp)
  apply (rule exF[where P="is_list 0"], simp)
  apply (rule implI, simp)
  proof -
    fix xa
    assume hyp: "(⋀y. y N ⟹ y ≤ xa = 1 ⟹ is_list y ⟶ Q y)"
    assume cons: "(⋀x xs. x N ⟹ xs N ⟹ is_list xs ⟹ Q xs ⟹ Q (Cons x xs))"
    show "a N ⟹ xa N ⟹ is_list S xa ⟹ Q Nil ⟹
          Q S xa"
      proof (cases "S xa", simp)
        case Nil
          from Nil show ?case
            by (simp+)
      next
        case (Cons n xs)
          from Cons and cons show ?case
            apply (simp)
            apply (rule cons, simp)
            apply (rule obj_impl)
            apply (rule hyp, simp)
            apply (rule le_suc_implies_leq, simp+)
            done
      qed
  qed
  ```
]

== Tooling for Inductive Datatypes
To make the induction and case distinction mechanisms of `List` useful, they are integrated with the existing `induct` and `cases` tactics.

The idea is that the induction lemma of an inductive type is annotated with the $tag("induct")$ tag, and the corresponding case distinction lemma is annotated with $tag("cases")$. To accommodate the new inductive types, the `induct` and `cases` tactics are extended accordingly. The behavior of the `induct` tactic is now as follows:

- If the argument `strong` is supplied, the strong induction lemma is applied.  
- Otherwise, the tactic iterates over all theorems annotated with the $tag("induct")$ attribute and proceeds as follows for each candidate theorem:  
  - Attempt to instantiate the theorem with the given term $x$.  
  - Check whether the first subgoal resulting from the instantiation can be discharged using only the assumptions currently available in the proof context (this check is performed without committing to the application).  
  - If this succeeds, the theorem is selected, applied to the goal, and the first subgoal is solved.  
  - Finally, the corresponding cases are generated from the theorem definition, making use of the `case_names` annotation.  

The following is the final code for the `induct` method, implementing the logic described above:

```SML
structure GD_Induct =
struct
  val induct_thm = @{thm ind}
  val strong_induct_thm = @{thm strong_induction}

  fun try_inst_thm ctxt t th =
    let val ct = Thm.cterm_of ctxt t in
      try (fn th => Drule.infer_instantiate' ctxt [SOME ct] th) th
    end

  fun closes_first_prem ctxt i th st =
    let
      val tac =
      DETERM (
        resolve_tac ctxt [th] i
        THEN ((SOLVED' (assume_tac ctxt)) i)
      )
    in
      Option.isSome (Seq.pull (tac st))
    end

  fun select_induct_thm ctxt t i st =
    let
      val induct_thms = Named_Theorems.get ctxt @{named_theorems induct}
      fun is_instantiable th =
        case (try_inst_thm ctxt t th) of
          NONE     => NONE
        | SOME th' => if (closes_first_prem ctxt i th' st) then SOME th else NONE
    in
      case (get_first is_instantiable induct_thms) of
        SOME th => th
      | NONE    => induct_thm
    end

  fun apply_tac tac st =
    let
      val res = DETERM tac st
    in
      case Seq.pull res of
        SOME (st', _) => st'
      | NONE => raise THM ("tactic failed", 0, [st])
    end

  fun induct_tac strong t =
    CONTEXT_SUBGOAL (fn (_, i) => fn (ctxt, st) =>
    let
      val th  = if strong then strong_induct_thm else (select_induct_thm ctxt t i st)
      val th' = try_inst_thm ctxt t th
      val tac =
        case th' of
          SOME th'' => DETERM (match_tac ctxt [th''] i)
        | NONE      => no_tac
      val st' = apply_tac tac st
      val (spec, _) = Rule_Cases.get th
      val cases_prop = Thm.prop_of (Rule_Cases.internalize_params st')
      val cases = Rule_Cases.make_common ctxt cases_prop spec
      val post_tac = TRY (SOLVED' (assume_tac ctxt) i)
    in
      CONTEXT_CASES cases post_tac (ctxt, st')
    end)

  fun gd_induct_method (strong, t) _ =
    Method.CONTEXT_METHOD (K (induct_tac strong t 1))
end

val parse_induct_args =
  Scan.lift (Scan.optional ((Args.$$$ "strong") >> K true) false)
  -- Args.term

val _ =
  Theory.setup
    (Method.setup @{binding induct}
    (parse_induct_args >> GD_Induct.gd_induct_method)
    "Apply rule ind with where a = <term>"
  )
```

== Future Work
This concludes the proof of all the required properties stated in @inductive-general. Thus, the encoding of `Nil` and `Cons` together with the `is_list` predicate constitute a full inductive datatype in _GA_. Since most of the steps undertaken to get there followed a clear template, in the future, an inductive datatype should be able to be compiled from a simple description of the constructors:

```Isabelle
declaretype List =
  Nil
  | Cons of "num" "List"
```

To make inductive datatypes truly practical in _GA_, it would be desirable to provide an accompanying definitional mechanism, accepting high-level specifications such as the following:

```Isabelle
fun sum :: "List ⇒ num" where
 sum_nil: "sum Nil = 0" and
 sum_cons: "sum (Cons n xs) = n + sum xs"
```

That is then compiled into the following encoding-aware recursive _GA_ definition:

```Isabelle
axiomatization
  sum :: "List ⇒ num"
where
  sum_def: "sum x := if x = Nil then 0
                     else if (is_cons x) then (cpi 3 x) + (sum (cpi' 4 x))
                     else omega"
```

From which a termination proof and the defining equations can be derived:

```Isabelle
lemma [auto]: "x N ⟹ is_list x ⟹ sum x N"
proof (induct x, simp)
  case Nil
  show ?case
    by (unfold_def sum_def, simp add: sum_def)
next
  case (Cons n xs)
  from Cons show ?case
    apply (unfold_def sum_def)
    apply (subst rule: condI2)
    apply (subst rule: condI1)
    apply (unfold Cons_def, simp+)
    apply (unfold_def is_cons_def, simp)
    done
qed

lemma [simp]: "sum Nil = 0"
by (unfold_def sum_def, simp)

lemma [simp]: "n N ⟹ xs N ⟹ is_list xs ⟹ sum (Cons n xs) = n + sum xs"
apply (rule eqSym)
apply (unfold_def sum_def)
apply (unfold_def is_cons_def)
apply (unfold Cons_def Nil_def, simp)
done
```

While a full implementation of these mechanisms is outside the scope of this thesis, the foundations have been developed, and what remains is largely an engineering task left for future work.
