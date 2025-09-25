// =====================================================
// The tooling chapter. Tackles automation to make GD
// a usable proof assistant.
// =====================================================

#import "../style.typ": *
#import "../formalisms.typ": *
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#show: codly-init.with()
#codly(zebra-fill: none)

= Tooling for Isabelle/GA
<tooling>
Having implemented _GA_ in _Pure_ effectively obtained an interactive theorem prover we term _Isabelle/GA_, based on the axioms of _GA_. In its current state however, _Isabelle/GA_ is not a very useful theorem prover. There is no proof automation, no term rewriting, and no easy way to formalize higher level mathematics. Users can only reason about natural numbers and only using axioms or previously proven lemmas, leading to highly verbose and cumbersome proofs, as seen in @ga-in-pure.

This chapter aims for making _Isabelle/GA_ more usable as a proof assistant and, towards that end, introduces various methods for simpler and cleaner reasoning, a simple auto-solver, and most importantly, compatibility with the powerful simplifier built into _Pure_. The goal is to mostly hide the axiomatic system of _GA_ behind abstract proof methods found in existing theorem provers and allow proofs to focus on their main idea, rather than being about mapping to specific axioms and discharging _habeas quid_ premises.

== (Un)folding (Recursive) Definitions
The first methods we implement are the `unfold_def` and `fold_def` methods, which take the name of a definition ($:=$) and (un)fold it once in the current goal state.

Example usage:
```Isabelle
apply (unfold_def mult_def)
apply (fold_def mult_def)
```

This corresponds exactly to:
```Isabelle
apply (rule defE[OF mult_def])
apply (rule defI[OF mult_def])
```

The method names are intentionally similar to the existing `unfold` and `fold`, which (un)fold an (non-recursive) Isabelle definition.

The implementation in SML is as follows:

```SML
structure Unfold_Def =
struct
  fun fold_def_method thm_name ctxt =
    SIMPLE_METHOD' (fn i =>
      let
        val defI_thm = Proof_Context.get_thm ctxt "defI"
        val target_thm = Proof_Context.get_thm ctxt thm_name
      in
        CHANGED (resolve_tac ctxt [defI_thm OF [target_thm]] i)
      end)

  fun unfold_def_method thm_name ctxt =
    SIMPLE_METHOD' (fn i =>
      let
        val defE_thm = Proof_Context.get_thm ctxt "defE"
        val target_thm = Proof_Context.get_thm ctxt thm_name
      in
        CHANGED (resolve_tac ctxt [defE_thm OF [target_thm]] i)
      end)
end

val _ =
  Theory.setup
    (Method.setup @{binding unfold_def}
      (Scan.lift Args.name >> Unfold_Def.unfold_def_method)
      "Unfold a definition using defE"
  )

val _ =
  Theory.setup
    (Method.setup @{binding fold_def}
      (Scan.lift Args.name >> Unfold_Def.fold_def_method)
      "Fold a definition using defI"
  )
```

The Isabelle/ML infrastructure is well-equipped to handle such method definitions and multiple components of the provided infrastructure are visible in the snippet:

1. *Parsing*: `Args.name` parses an identifier and the `>>` combinator passes the parsed argument on to the defined method.
2. *Tactic Combinators*: `resolve_tac` simply applies the given list of theorems (in this case a singleton list) to subgoal `i` of the given `context`. `CHANGED` takes a tactic and succeeds if and only if its argument tactic changed the goal state. That is, if there was no definition to fold/unfold, the method fails, even if the theorem application itself succeeds.
3. *Method registration*: `Method.setup` sets up the defined method at the given binding. `SIMPLE_METHOD'` converts a value of type $"int" => "tactic"$ (usually a function applying a tactic to the `i`'th subgoal, where `i` is ita argument) to a method.

== Configuring the Simplifier
_Pure_ already contains a simplifier. The rewrite rules it uses are theorems of the shape:

#align(center)[
  `complicated_expression` $equiv$ `simple_expression`
]

That is, the _Pure_ simplifier works on meta-level equations. When invoked, the simplifier tries to match the left-hand side of any rewrite equation in any subexpression and rewrites it to the right-hand side of the equation.

The simplifier uses theorems tagged with $tag("simp")$ as its rewrite rules. Its exact inner workings are not of interest here, but it is highly sophisticated and sublinear in the number of rewrite rules.

The first problem with using the simplifier in _GA_ is that the axioms allow deriving object-level equality (=), but not meta-level equality ($equiv$). Either, _GA_ needs its own simplifier, or it needs to seek 'compatibility' of object equality with meta equality.

The simple solution is to add an axiom to convert object equality to meta equality:

#definition-box("Equality Reflection Axiom")[
  #eq-reflection-axiom
]

This inference rule is not provable from either the _Pure_ axioms or the _GA_ axioms, which is why it needs to be axiomatized. Using it for rewrites however is completely safe, as any such rewrite can be achieved using the existing `eqSubst` axiom.

That is, the following lemma is provable in _GA_, and thus the axiom is admissible:

#theorem(none)[
  #eq-subst-corollary
]

#proof[
  By equality substitution.
  ```Isabelle
  lemma "a = b ⟹ Q b ⟹ Q a"
  apply (rule eqSubst[where a="b" and b="a"])
  apply (rule eqSym)
  apply (assumption+)
  done
  ```
]

If the simplifier proves a theorem, having substituted a term $b$ for $a$ (due to a meta-equality theorem), the proof of the original theorem (with no substitution) can be constructed using the above theorem and the equality $a = b$. Since the simplifier constructs the meta-equality from exactly such an equality $a = b$, no new theorems of type `o` can be proven from this axiom.

If a rewrite theorem (that is, a theorem tagged with $tag("simp")$) has any premises, the simplifier only rewrites if it can discharge all its premises. Thus, a key step in configuring the simplifier for _GA_ is to provide a competent solver that can discharge a wide range of commonly occuring premises such that the simplifier can apply more rewrites. Precisely such a solver is engineered in @subgoaler. For now, we already assume its existence at `GDAuto.gd_auto_tac` and use it in the following SML structure that configures the simplifier for _GA_. It achieves two main objectives:

1. Convert object equality theorems to meta equality theorems on the fly.
2. Set the solver for the simplifier.

```SML
structure GD_Simp =
struct
  fun convert_eq_to_meta_eq th: thm = th RS @{thm eq_reflection}

  fun match_object_rule th trm =
    case trm of
      Const (@{const_name GD.eq},  _) $ _ $ _  => [convert_eq_to_meta_eq th]
    | _ => []

  fun th_to_meta_eq_th _ th =
    case Thm.concl_of th of
       Const (@{const_name Pure.eq}, _) $ _ $ _ => [th]
     | Const (@{const_name GD.Trueprop}, _) $ x => match_object_rule th x
     | _ => []
end;

let
  val gd_solver =
    Raw_Simplifier.mk_solver "GD_solver" GDAuto.gd_auto_tac
  fun set_solver ctxt =
    Raw_Simplifier.setSolver (ctxt, gd_solver)
  fun set_ssolver ctxt =
    Raw_Simplifier.setSSolver (ctxt, gd_solver)
  fun configure ctxt =
    ctxt
    |> Simplifier.set_mksimps GD_Simp.th_to_meta_eq_th
    |> set_solver
    |> set_ssolver
in
  Theory.setup (Simplifier.map_theory_simpset configure)
end;
```

Now, theorems with either a top-level meta equality ($equiv$) or object equality (=) can be tagged with $tag("simp")$ and the simplifier will use them to rewrite subexpressions when invoked.

For example when invoking the simplifier from the following goal state:

1. $a nat ==> x nat ==> x * pred(suc(a)) nat$

```Isabelle
apply (simp)
```

The new goal state is:

1. $a nat ==> x nat ==> x * a nat$

The simplifier used the axiom `predSucInv` stating $a nat ==> pred(suc(a)) nat = a$ to rewrite $pred(suc(a))$ to $a$. This is because the `predSucInv` axiom was retroactively tagged with $tag("simp")$.

== A Subgoal Solver for _GA_
<subgoaler>

The main idea of the subgoal solver is very simple -- keep a set of lemmas of the following structure that should always be applied if the current subgoal matches their consequent:

#align(center)[
  `simple_premise` $==>$ `complicated_consequent`
]

Since this is not an equality, it cannot be applied to a subexpression. It can only be applied like a normal theorem, when the consequent actually matches the current goal. The instantiated premise(s) then become(s) the new goal. If there is no premise, the goal is solved immediately, and if there are multiple premises, the number of subgoals increases, but they are expected to be easier to solve than the consequent.

Some example lemmas that are suitable:

```Isabelle
lemma [auto]: "x N ⟹ ¬ S(x) = 0"
lemma natS [auto]: "a N ⟹ S a N"
lemma conjI [auto]: "p ⟹ q ⟹ p ∧ q"
lemma true [auto]: "True"
lemma true_bool [auto]: "True B"
lemma neq_bool [auto]: "a N ⟹ b N ⟹ (a ≠ b) B"
lemma if_trueI [auto]: "c ⟹ if c then True else False"
```

As can already be seen in this set of lemmas, the solver uses theorems with the $tag("auto")$ tag.

The solver works in the following way.

1. Fetch the theorems with the $tag("auto")$ tag using the function `Named_Theorems.get`.
2. Perform one iteration of the solver: Try to solve the current subgoal with the assumptions in context, else try to solve it with any other assumptions carried around in the simplifier context, or else try to apply any of the theorems tagged with $tag("auto")$. The iteration succeeds if and only if the goal state changed.
3. Recursively call another iteration on all new subgoals resulting from step 2, but succeed overall even if the recursive call fails. That is, the solver succeeds if at least one iteration succeeds.

The solver is extremely simple by design. It is easy to get stuck in a loop for the simplifier, which is why its subgoal solver should be simple, predictable, and most importantly, terminating. The solver tactic could be even more concise by using the `REPEAT_ALL_NEW` tactic combinator, which implements precisely the recursive structure of `solver_tac`. However, `REPEAT_ALL_NEW` is not bounded, which resulted in unpredictably occurring infinite loops of the simplifier when using it in the solver. Thus, it was replaced by this explicit recursion with a bound on the number of iterations.

The iteration bound is controlled by a global attribute in Isabelle and can be modified if necessary. The default value is 6, which has proved sufficient for all automated proofs in the GA formalization, while still maintaining acceptable performance. The `auto` solver can also be invoked directly. However, it is less powerful than the simplifier on its own, as it does not apply the $tag("simp")$ rewrite rules and does not rewrite subexpressions. When invoking `auto` directly, an optional argument can be supplied to override the iteration bound for that invocation only.

```SML
val gd_auto_depth_limit =
  Attrib.setup_config_int @{binding gd_auto_depth_limit} (K 6)

fun TRY' tac i = TRY (tac i)

structure GDAuto =
struct
  fun uncond_rules ctxt = Named_Theorems.get ctxt @{named_theorems auto}

  fun solver_tac _    0 = K no_tac
    | solver_tac ctxt k =
      let
        val tac = assume_tac ctxt ORELSE'
                  resolve_tac ctxt (Simplifier.prems_of ctxt) ORELSE'
                  resolve_tac ctxt (uncond_rules ctxt)

        val one_iter = CHANGED o tac
        val recurse = solver_tac ctxt (k-1)
      in
        one_iter THEN_ALL_NEW TRY' recurse
    end

  fun gd_auto_tac ctxt i =
    let
      val fuel = Config.get ctxt gd_auto_depth_limit
    in
      CHANGED (REPEAT (CHANGED (solver_tac ctxt fuel i)))
    end
end

val parse_nat =
  Scan.optional (Scan.lift Parse.nat >> SOME) NONE

val _ =
  Theory.setup (
    Method.setup @{binding auto}
      (parse_nat >> (fn opt_n => fn ctxt =>
        let
          val ctxt' = (case opt_n of NONE => ctxt | SOME n => Config.put gd_auto_depth_limit n ctxt)
        in
          SIMPLE_METHOD' (GDAuto.gd_auto_tac ctxt')
        end))
      "Simple proof automation for GA"
  )
```

There is not much to gain in trying to prune the set of rewrites at each point for the solver, since it only applies unconditional rewrites that are always the 'right choice', i.e. it doesn't perform a proof search.

The power of the solver comes not from its sophistication, but from a wealth of useful theorems that are added to its set of facts. With this simple solver (and a rich set of theorems tagged $tag("auto")$ and $tag("simp")$ respectively), the simplifier becomes capable of solving many kinds of subgoals entirely. For example, the termination proof of the multiplication function used to exactly mirror the one for the addition function from @term-proofs. With the new solver, almost everything can be solved by the simplifier. In particular, no manual reasoning to solve any _habeas quid_ premises is required.

```Isabelle
lemma mult_terminates [auto]:
  shows ‹x N ⟹ y N ⟹ mult x y N›
proof (rule ind[where a=y])
  show "y N ⟹ y N" by simp
  show "x N ⟹ mult x 0 N"
    by (unfold_def mult_def, simp)
  fix a
  show "a N ⟹ x N ⟹ mult x a N ⟹ mult x (S a) N"
    by (unfold_def mult_def, rule condT, simp+)
qed
```

The lemma is itself immediately tagged $tag("auto")$, such that the simplifier becomes even more powerful in subsequent proofs.

== Conditional Rewrites
The `auto` solver exclusively applies assumptions and unconditional rewrites. However, it would be desirable to have a means to declare certain lemmas as conditional rewrites. This can mean multiple things, for example could there be a theorem that should only be applied by an automatic solver if some of its premises can be automatically solved, or a theorem should be applied entirely for proof search, i.e. it is generally uncertain whether applying it is productive towards solving the subgoal.

- #text[
  An example for the former is the following lemma:

  ```Isabelle
  lemma "¬c ⟹ b N ⟹ d N ⟹ b = d ⟹ (if c then a else b) = d"
  ```

  If the current goal is of the shape of the consequent and the first three premises can be solved, the goal should be reduced to the fourth premise, $b = d$. Solving only the first premise is not sufficient, since $b$ and $d$ could be of type `o`, in which case $b nat$ and $d nat$ would not be solvable and the following lemma should have been applied instead:

  ```Isabelle
  lemma "¬c ⟹ b B ⟹ d B ⟹ b = d ⟹ (if c then a else b) = d"
  ```
]

- #text[
  A simple example for the latter kind would be the `eqSym` axiom. A goal might be solvable after applying it, but it generally does not simplify the goal:

  ```Isabelle
  eqSym: "a = b ⟹ b = a"
  ```
]

=== Using `simp` for conditional rewrites
<simp-for-cond>
The first approach towards conditional rewrites is to use the simplifier. Since it only applies a rewrite if it can solve all premises, it is a natural choice for conditional rewriting. It is also highly efficient, much more so than any custom solution anyone could hope to implement single handedly.

This approach works very well for lemmas like the following:

```Isabelle
lemma [simp]: "c ⟹ (if c then True else b) = True"
lemma [simp]: "¬c ⟹ (if c then a else True) = True"
lemma suc_pred_inv [simp]: "x N ⟹ ¬ x = 0 ⟹ S P x = x"
```

The amount of complexity that can be moved into solving a premise is arbitrary. For example does the simplifier try to rewrite $pred(x) <= pred(y)$ to $1$ if the premises $x nat$, $y nat$, and $x <= y = 1$ can be solved by the `auto` solver (and recursive simplification on the subgoals) when trying to apply the following lemma. However, $x <= y = 1$ might be just as difficult to solve as $pred(x) <= pred(y) = 1$.

```Isabelle
lemma leq_monotone_pred [simp]:
  assumes x_nat: "x N"
  assumes y_nat: "y N"
  assumes H: "x ≤ y = 1"
  shows "P x ≤ P y = 1"
```

There are some key limitations to note for using the simplifier for conditional rewrites:

1. Adding too many rules like `leq_monotone_pred` (with low probability of the solver succeeding in solving its premises) to the simpset makes the performance of the simplifier deteriorate quickly, as it essentially ends up performing a proof search.
2. If the premise and consequent can have the same instantiation, the simplifier *will* run into an infinite loop. For instance, tagging the `eqSym` axiom with $tag("simp")$ makes it enter an infinite loop on every invocation immediately.
3. The simplifier always tries to solve all premises and does not support reducing the goal to one or more premises (to be solved manually or by another tactic).
4. The simplifier operates on equalities only. While this is largely solved by the `auto` solver, it can only do unconditional applications.

Point (1) suggests moving low-probability-of-success rewrites to a different tool, but points (2), (3), and (4) ask for a different approach altogether.

=== Extending the `auto` Solver with Conditional Rewrites
<cond>
Problem (4) asks for an extension of the `auto` solver to also handle conditional rewrites, which also solves problem (3). Thus, the next approach was to add another tag $tag("cond")$ for lemmas intended to be used as conditional rewrites and let the `auto` solver use such a tagged theorem for rewriting if it can solve its first premise. Since any number of premises can be 'encoded' into the first premise by simply conjoining them ($and$), conditioning on solving the first premise is sufficient.

Some lemmas that can be handled using this approach and not by the simplifier:

```Isabelle
lemma [cond]: "a ⟹ a B"
lemma [cond]: "¬a ⟹ a B"
lemma [cond]: "((c B) ∧ (a N) ∧ (b N)) ⟹ if c then a else b N"
lemma [cond]: "((c B) ∧ (a B) ∧ (b B)) ⟹ if c then a else b B"
```

Especially the booleanness conditions $a bool$ are vital to solve effectively in the subgoal solver of the simplifier, since they are common _habeas quid_ premises in _GA_. The first two lemmas effectively do a proof search and try to solve for both the positive and negative case.

The last two lemmas are equivalent to the axioms `condT` and `condTB`, just with the three premises conjoined into one, such that the `auto` solver only applies them if all three are solved. These lemmas show the limitations of using exclusively the simplifier for automation, since this lemma cannot be expressed as an equality. One would expect that the following lemmas could be used by the simplifier:

```Isabelle
lemma [simp]: "c B ⟹ a N ⟹ b N ⟹ if c then a else b N = True"
lemma [simp]: "c B ⟹ a B ⟹ b B ⟹ if c then a else b B = True"
```

However, due to the extraordinarily syntactic nature of equality in _GA_, these propositions are not provable. `True` is defined as the canonical truth $0 = 0$ in _GA_ and $"True" = a$ cannot be derived for any $a$, as there is no axiom that allows deriving equality of equalities (in particular, no reflexivity axiom).

With these lemmas presented so far, the approach is the following. Previously, the `auto` solver was designed to apply a theorem if it is the single canonical way to solve a goal of a certain shape. The conditional extension now added the capability of trying multiple different solution strategies to definitely solve a goal. For examle, if premise $c$ can be solved, the goal $c bool$ is solved completely and no new subgoals are generated. There is however another category of lemmas that can be integrated with the conditional extension to the `auto` solver. Namely, trying different solution strategies to reduce the current goal to a new subgoal that is likely easier to solve. For example the following lemmas implement this strategy for reducing $cond(c,a,b)$ constructs:

```Isabelle
lemma [cond]: "(¬c ∧ (b N) ∧ (d N)) ⟹ b = d ⟹ (if c then a else b) = d"
lemma [cond]: "(c ∧ (a N) ∧ (d N)) ⟹ a = d ⟹ (if c then a else b) = d"
```

With this extension, the simplifier gets an even more competent subgoal solver, providing another boost to proof automation. Problems (3) and (4) of the initial approach of using only the simplifier are now solved and the two approaches coexist.

The additions in the `auto` implementation are straightforward. The required additions are highlighted:

#codly(highlights: (
  (line: 10, start: 3, fill: green),
  (line: 15, start: 9, fill: green),
  (line: 16, start: 11, fill: green),
  (line: 17, start: 11, fill: green),
  (line: 18, start: 9, fill: green),
  (line: 19, start: 11, fill: green),
  (line: 20, start: 13, fill: green),
  (line: 23, start: 56, fill: green),
  (line: 24, start: 19, fill: green),
))
```SML
val gd_auto_depth_limit =
  Attrib.setup_config_int @{binding gd_auto_depth_limit} (K 6)

fun TRY' tac i = TRY (tac i)

structure GDAuto =
struct

  fun uncond_rules ctxt = Named_Theorems.get ctxt @{named_theorems auto}
  fun cond_rules   ctxt = Named_Theorems.get ctxt @{named_theorems cond}

  fun solver_tac _    0 = K no_tac
    | solver_tac ctxt k =
      let
        fun apply_and_solve_subgoal i th =
          match_tac ctxt [th] i
          THEN SOLVED' (solver_tac ctxt (k-1)) i
        fun cond_tacs i =
          FIRST (map (apply_and_solve_subgoal i)
            (cond_rules ctxt))
        val tac = assume_tac ctxt ORELSE'
                  resolve_tac ctxt (Simplifier.prems_of ctxt) ORELSE'
                  resolve_tac ctxt (uncond_rules ctxt) ORELSE'
                  cond_tacs
        val one_iter = CHANGED o tac
        val recurse = solver_tac ctxt (k-1)
      in
        REPEAT_ALL_NEW one_iter
    end

  fun gd_auto_tac ctxt i =
    let
      val fuel = Config.get ctxt gd_auto_depth_limit
    in
      CHANGED (REPEAT (CHANGED (solver_tac ctxt fuel i)))
    end
end

val parse_nat =
  Scan.optional (Scan.lift Parse.nat >> SOME) NONE

val _ =
  Theory.setup (
    Method.setup @{binding auto}
      (parse_nat >> (fn opt_n => fn ctxt =>
        let
          val ctxt' = (case opt_n of NONE => ctxt | SOME n => Config.put gd_auto_depth_limit n ctxt)
        in
          SIMPLE_METHOD' (GDAuto.gd_auto_tac ctxt')
        end))
      "Simple proof automation for GD logic"
  )
```

There is one massive problem with this `cond` extension however, namely that problem (1) of the simplifier approach is made even worse here. The `auto` solver is the subgoal solver of the simplifier and it now performs quite a bit of proof search, and a completely unoptimized one at that, which makes the performance of the simplifier suffer.

=== Circumventing Weak Equality
The automation boost the `cond` extension from the previous @cond provides is satisfactory, but it slowed down the simplifier significantly. Although computationally the same problem, moving the rudimentary proof search capabilities of the `cond` extension from the `auto` solver into the simplifier itself should be much faster, simply due to its (presumably) more efficient implementation.

Although an equality like the following (which the simplifier could use as a rewrite rule) does not hold in _GA_:

```Isabelle
lemma "¬c ⟹ b N ⟹ d N ⟹ ((if c then a else b) = d) = (b = d)"
```

The following proposition is provable:
```Isabelle
lemma "¬c ⟹ b N ⟹ d N ⟹ (if c then a else b) = d ⟷ b = d"
```

Adding a conversion axiom from $<->$ to $equiv$ makes such lemmas usable as rewrites for the simplifier.

#definition-box("Iff Reflection Axiom")[
  #iff-reflection-axiom
]

If-and-only-if ($<->$) is effectively an equality for propositions of type `o`, since object equalities (=) are not derivable for them (only for expressions of type `num`). It is unclear whether it is admissible. However, the following theorem shows that, while for admissibility the theorem $a <-> b ==> ctxt(b) ==> ctxt(a)$ would be required, the following inference rule that very closely resembles the axiom itself is readily provable in _GA_.

#theorem("Iff Trueprop Reflection")[
  #iff-refl-prop
]

#proof[
  Using the `equal_intr_rule` _Pure_ axiom, derive both $a ==> b$ and $b ==> a$.
  ```Isabelle
  lemma "a ⟷ b ⟹ (Trueprop a) ≡ (Trueprop b)"
  apply (rule Pure.equal_intr_rule)
  apply (unfold iff_def)
  apply (rule implE, rule conjE1, assumption+)
  apply (rule implE, rule conjE2, assumption+)
  done
  ```
]

The same proof does not work when trying to prove `iff_reflection`, since the _Pure_ `equal_intr_rule` only works for meta equalities ($equiv$) where both sides are of type `prop`, whereas in `iff_reflection`, the two sides are of type `o`.

The proof of the theorem shows that the `iff_reflection` axiom is essentially an object-level version of the meta level `equal_intr_rule`, which allows deriving equality $equiv$ when $a ==> b$ and $b ==> a$ can be derived. While the simplifier could in principle work with lemmas of the shape $"Trueprop" a equiv "Trueprop" b$, the left-hand side never matches any subterm in a _GA_ expression, as it is of type `prop`, while _GA_ terms are of type `o` or `num`. The admissibility of the axiom might be provable meta-logically by induction over the inference rules of _GA_, but _Pure_ is not sufficiently strong as a meta-logic to do so, as it does not have an (meta-level) induction scheme.

The new axiom allows restating most of the lemmas previously tagged with $tag("cond")$, such that the simplifier can rewrite them. An example is the following lemma:

```Isabelle
lemma [cond]: "a < b = 1 ⟹ a N ⟹ b N ⟹ ¬ a = b"
```
Which was subsequently restated and reproven as:
```Isabelle
lemma [simp]: "a < b = 1 ⟹ a N ⟹ b N ⟹ ¬ a = b ⟷ True"
```
In fact, this is more powerful, since even subexpressions can be rewritten using the latter.

While all lemmas intended for conditional rewriting can be reformulated as bicionditional, not all such reformulated propositions can actually be proven. The reason is the _habeas quid_ premise of the derivable implication introduction rule in _GA_, which requires proving the antecedent of the implication boolean ($bool$). This is not possible for example in the following lemma:
```Isabelle
lemma [cond]: "((c B) ∧ (a N) ∧ (b N)) ⟹ if c then a else b N"
```
While it can be restated as:
```Isabelle
lemma [simp]: "((c B) ∧ (a N) ∧ (b N)) ⟹ if c then a else b N ⟷ True"
```
Proving this proposition requires showing that $(cond(c,a,b) nat) bool$, which is equivalent to solving the halting problem in _GA_, as it requires proving that the proposition $a nat$ is decidable in general. Thus, rewrites of this shape remain in the domain of the `cond` extension of the `auto` solver.

The configuration of the simplifier needs to be extended in order for it to correctly apply biconditional theorems. The minimal additional logic is hightlighted in green:

#codly(highlights: (
  (line: 4, start: 3, fill: green),
  (line: 9, start: 5, fill: green),
))
```SML
structure GD_Simp =
struct
  fun convert_eq_to_meta_eq th: thm = th RS @{thm eq_reflection}
  fun convert_iff_to_meta_eq th: thm = th RS @{thm iff_reflection}

  fun match_object_rule th trm =
    case trm of
      Const (@{const_name GD.eq},  _) $ _ $ _  => [convert_eq_to_meta_eq th]
    | Const (@{const_name GD.iff},  _) $ _ $ _ => [convert_iff_to_meta_eq th]
    | _ => []
...
```

=== Proof Search
The initial approach of using the simplifier to handle conditional rewrites maybe unsurprisingly ended up being the most effective solution, although it did take an extension to make better use of it. The reason is its sophistication and efficient implementation, which makes it hard to beat even though it is not designed to be used for even rudimentary proof search. An approach that might provide additional value over the setup constructed in this section is a true proof search (implemented on top of the simplifier, and not as its subgoal solver). However, since a naive implementation is exponential in the number of theorems in the rewrite set, this requires a sophisticated datastructure to search for applicable rules in order to be tractable at the very least. This might be a valuable addition to the tooling of _GA_, but has not been implemented yet for two reasons.
- An efficient implementation is a significant time investment and seemed out of the scope for this thesis.
- The automation with the existing setup was surprisingly effective and a real proof search for the sake of better proof automation never seemed exceptionally desirable.

== Manual Substitution
Finally, if the simplifier is not powerful enough to solve all premises of a theorem that would actually be the right one to apply, a simple substitution command that allows rewriting (including subexpressions) with a specific theorem and solving some of its premises manually is very helpful.

For example, consider the following goal state reached by an invocation of the simplifier. 

1. $x nat ==> x' nat ==> (cond(suc(x') = 0, 0, cond("cpx" x' = 0, suc("cpy" x'), pred("cpx" x')))) nat$

Another invocation of `simp` fails.

```Isabelle
apply (simp)
```

The simplifier is not able to take the second branch of the top-level conditional, since to do this rewrite, it would have to show that the second branch terminates, i.e. show that it is $nat$, which it is unable to do.

Now, a command like the following would come in very handy:

```Isabelle
apply (subst rule: condI2)
```

This performs the rewrite and leaves the unsolved premises as new subgoals, resulting in the goal state:

1. $x nat ==> x' nat ==> (cond("cpx" x' = 0, suc("cpy" x'), pred("cpx" x'))) nat$
2. $x nat ==> x' nat ==> (cond("cpx" x' = 0, suc("cpy" x'), pred("cpx" x'))) nat$

Here, the same goal appears twice, since the premise of the `condI2` rule, to show the second branch terminates, precisely coincides with the remaining goal after substituting the second branch for the entire conditional.

Without the `subst` command, the `condI2` theorem couldn't have been applied directly, since the substituted conditional is a subexpression; it would have had to be preceded by an equality substitution and an application of equality symmetry first (which is more or less what the `subst` command does). Thus, the `subst` command is a convenient way of manually advancing the proof when the simplifier gets stuck.

In fact, more occurences of `eqSubst` applications can be replaced by a more convenient method. Consider the following goal state.

1. $x nat ==> x' nat ==> not (pred(x') = pred(suc(x))) ==> not (pred(x') = x)$

So far, this was solved the following way:

```Isabelle
apply (rule eqSubst[where a="P S x" and b="x"])
apply (simp)
```

Where the simplifier solves the first resulting subgoal after the equality substitution $pred(suc(x)) = x$ automatically and then the second subgoal by assumption.

The `eqSubst` axiom itself should be hidden and the rewrite should be done automatically with a simple:

```Isabelle
apply (subst "P S x = x")
```

This is not a huge difference, but it makes the proof cleaner.

The `subst` command thus has two different modes of operating, one accepting a theorem name (which is expected to have a top-level equality) and using it to rewrite a match for the left-hand side to the right-hand side, concluding the first subgoal with the theorem itself, and the other accepting an equality itself, which it uses to rewrite, and then tries to solve using the simplifier.

This is implemented in the following SML code, which works as follows:

1. Parses either a theorem name or a term, whichever succeeds.
2. If the argument is a theorem name, it fetches the theorem and extracts the left-hand side and right-hand side of its top-level equality (assuming it is of the expected shape), instantiates the `eqSubst` theorem with those extracted terms, and then finally applies it. Then, it applies the `eqSym` axiom to flip the equality from the first subgoal, which can then be resolved by the passed theorem itself.
3. If the argument is a term, the code extracts the left-hand side and right-hand side of its top-level equality (assuming it is of the expected shape), instantiates the `eqSubst` theorem with those extracted terms, and then finally applies it. Then, it tries to solve the resulting first subgoal (the equality itself) by applying the simplifier.

```SML
datatype input = AsThm of thm | AsTrm of term

structure GD_Subst =
struct
  fun strip_asms t =
    case t of
      @{term "(==>)"} $ _ $ t' => strip_asms t'
    | _ => t

  fun get_lhs_rhs_of_eq t =
      case t of
        @{term "(Trueprop)"} $ t'                  => get_lhs_rhs_of_eq t'
      | Const (@{const_name GD.eq}, _) $ lhs $ rhs => (SOME lhs, SOME rhs)
      | _                                          => (NONE, NONE)

  fun get_eq (AsTrm t)   = let val (l, r) = get_lhs_rhs_of_eq t in (r, l) end
    | get_eq (AsThm thm) = get_lhs_rhs_of_eq (strip_asms (Thm.prop_of thm))

  fun eq_subst_tac input ctxt =
    case (get_eq input) of
      (SOME pat, SOME rhs) =>
        let
          val l = (Thm.cterm_of ctxt pat)
          val r = (Thm.cterm_of ctxt rhs)
          val eqSub = Proof_Context.get_thm ctxt "eqSubst"
          val eqSub' =
            Drule.infer_instantiate' ctxt
            [SOME r, SOME l]
            eqSub
        in
          resolve_tac ctxt [eqSub']
        end
      | (_,_) => K no_tac

  fun gd_subst_tac (AsThm thm) ctxt =
    let val eqSym = Proof_Context.get_thm ctxt "eqSym" in
      (eq_subst_tac (AsThm thm) ctxt) THEN'
      resolve_tac ctxt [eqSym] THEN'
      resolve_tac ctxt [thm]
    end
  | gd_subst_tac (AsTrm trm) ctxt =
    (eq_subst_tac (AsTrm trm) ctxt) THEN'
    (fn i => TRY (SOLVED' (Simplifier.asm_full_simp_tac ctxt) i))

end

val parse_subst_args : input context_parser =
  (Scan.lift (Args.$$$ "rule" |-- Args.colon) |-- Attrib.thm >> AsThm)
  || (Args.term >> AsTrm)

val _ =
Theory.setup
    (Method.setup @{binding subst}
    (parse_subst_args >>
      (fn inp => fn ctxt => SIMPLE_METHOD' (GD_Subst.gd_subst_tac inp ctxt)))
    "Substitute using the given theorem name or term."
)
```

== Case Distinction
What is missing so far is a good way to do case distinction over natural numbers and truth values. The foundation for these case distinctions is given by the following two lemmas.

#theorem("Cases Bool")[
  #cases-bool
]

#proof[
  By the 'case distinction' axiom `disjE1` using the fact that $q or not q$ by $q bool$.
  ```Isabelle
  lemma cases_bool:
    assumes q_bool: "q B"
    assumes H: "q ⟹ p"
    assumes H1: "¬q ⟹ p"
    shows "p"
  apply (rule disjE1[where P="q" and Q="¬q"])
  apply (fold bJudg_def)
  apply (rule q_bool)
  apply (rule H)
  apply (assumption)
  apply (rule H1)
  apply (assumption)
  done
  ```
]

#theorem("Cases Nat")[
  #cases-nat
]

#proof[
  By the 'case distinction' axiom `disjE1` using the fact that $x = 0 or not (x = 0)$ and using the helper lemma `num_nonzero`, stating that $a nat ==> not (a = 0) ==> exists x. #h(0.5em) a = suc(x)$
  ```Isabelle
  lemma cases_nat: "x N ⟹ (x = 0 ⟹ Q 0) ⟹ (⋀y. y N ⟹ x = S(y) ⟹ Q S(y)) ⟹ Q x"
  apply (rule disjE1[where P="x = 0" and Q="¬ x = 0"])
  apply (fold bJudg_def, simp)
  apply (subst "0 = x", assumption)
  apply (rule existsE[where Q="λc. x = S(c)"])
  apply (rule num_nonzero)
  proof -
    fix a
    show "(⋀y. y N ⟹ x = S y ⟹ Q (S y)) ⟹ a N ⟹ x = S a ⟹ Q x"
     by (subst "S a = x", assumption)
  qed
  ```
]

Using these theorems, the job of the `cases` method is very simple -- parse the argument and decide which theorem to apply:

```SML
datatype input = BoolCaseTac of term | NatCaseTac of term

structure GDCases =
struct

fun try_inst_thm ctxt t th =
  let val ct = Thm.cterm_of ctxt t in
    try (fn th => Drule.infer_instantiate' ctxt [SOME ct] th) th
  end

fun gd_bool_cases_tac ctxt x =
  case (try_inst_thm ctxt x @{thm cases_bool}) of
    SOME th => resolve_tac ctxt [th]
  | NONE    => K no_tac

fun gd_nat_cases_tac ctxt x =
  case (try_inst_thm ctxt x @{thm cases_nat}) of
    SOME th => resolve_tac ctxt [th]
  | NONE    => K no_tac

fun gd_cases_tac ctxt input =
  case input of
    BoolCaseTac t   => SIMPLE_METHOD' (gd_bool_cases_tac ctxt t)
  | NatCaseTac t   => SIMPLE_METHOD' (gd_nat_cases_tac ctxt t)

val parse_cases_args : input context_parser =
  (Scan.lift (Args.$$$ "bool" |-- Args.colon) |-- Args.term >> BoolCaseTac)
  || (Args.term >> NatCaseTac)

val _ =
  Theory.setup
    (Method.setup @{binding cases}
      (parse_cases_args >> (fn inp => fn ctxt => gd_cases_tac ctxt inp))
      "case analysis")

end
```

== Induction Method
Although there is an induction axiom, this is another opportunity to make _GA_ consistent with the sorts of commands/methods a user would expect of a proof assistant and provide a method that wraps the axiom application.

Instead of applying the axiom:
```Isabelle
apply (rule ind[where a="x"])
```

The `induct` method is applied:
```Isabelle
apply (induct x)
```

And instead of the strong induction lemma:
```Isabelle
apply (rule strong_induction[where a="x"])
```

A flag can be passed to the `induct` method:
```Isabelle
apply (induct strong x)
```

For much of this thesis, Isabelle proofs were presented in apply-style scripts. However, Isabelle also provides a structured proof language called _Isar_, which aims for emulating natural language proofs and overall better legibility compared to apply-style scripts. One nice feature of _Isar_ are named cases; The premises of a theorem can be named and when applying it, the subgoals (and their respective assumptions) are bound to a case name that can be invoked with the following general syntax:

```Isabelle
proof (method_name)
  case (case_1_name case_1_arg_1 ...)
    show ?case
    ...
next
  case (case_2_name case_2_arg_1 ...)
    show ?case
    ...
...
qed
```

For example, the goal is to be able to provide the following syntax for applying induction:

```Isabelle
proof (induct y)
  case Base
    show case?
    ...
next
  case (Step xa)
   ...
qed
```

Precisely this functionality is provided by the following SML implementation of the `induct` method:

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
      val th  = if strong then strong_induct_thm else induct_thm
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

== A Case Study: Proving Strict Monotonicity of `cpy`
The following case study reviews the tooling and automation introduced in this section by presenting a proof of strict monotonicity for the `cpy` function, which extracts the second component of a _Cantor pair_ and is central in @inductive.

The `cpy` function itself is not important here, but the proof is a great example of how the few methods introduced in this section make up the majority of commands used in a proof and are a huge step up compared to the axiom level reasoning required before this chapter.

```Isabelle
lemma cpy_strict_mono [simp]: "x N ⟹ cpy (S x) < (S x) = 1"
proof (induct strong x)
  case Base
    from Base show ?case
      by (unfold_def cpy_def, simp)
next
  case (Step xa)
    fix y
    assume hyp: "⋀y. y N ⟹ y ≤ xa = 1 ⟹ cpy (S y) < (S y) = 1"
    from Step show ?case
      apply (unfold_def cpy_def, simp)
      apply (cases bool: "cpx (S xa) = 0")
      apply (simp add: cpx_suc)+
      apply (cases bool: "cpx xa = 0")
      apply (simp add: cpx_suc cpy_suc)+
      apply (subst "S P xa = xa", simp)
      apply (rule cpx_nz_arg_nz, simp)
      apply (rule le_monotone_suc)+
      apply (rule hyp, simp)
      done
qed
```
