// =====================================================
// The tooling chapter. Tackles automation to make GD
// a usable proof assistant.
// =====================================================

#import "../style.typ": definition-box
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

```Isabelle
complicated_expression ≡ simple_expression
```

That is, the _Pure_ simplifier works on meta-level equations. When applied, the simplifier tries to match the left-hand side of any rewrite equation in any subexpression and rewrites it to the right-hand side of the equation.

The simplifier uses theorems tagged with $\["simp"\]$ as its rewrite rules. Its exact inner workings are not of interest here, but it is highly sophisticated and sublinear in the number of rewrite rules.

The first problem with using the simplifier in _GA_ is that the axioms allow deriving object-level equality (=), but not meta-level equality ($equiv$). Either, _GA_ needs its own simplifier, or it needs to seek 'compatibility' of object equality with meta equality.

The simple solution is to add an axiom to convert object equality to meta equality:

#definition-box("Equality Reflection")[
  #eq-reflection-axiom
]

This proposition is not provable from either the _Pure_ axioms or the _GA_ axioms, which is why it needs to be axiomatized. Using it for rewrites however is completely safe, as any such rewrite can be achieved using the existing `eqSubst` axiom.

If a rewrite theorem (that is, a theorem tagged with [simp]) has premises, the simplifier only rewrites if it can discharge all its premises.

The following SML structure configures the simplifier for _GA_. It implements three functionalities:

1. Converts object equality theorems to meta equality theorems on the fly.
2. Configures a solver tactic.
3. Sets a subgoaler.

```SML
structure GD_Simp =
struct
  fun reflect_eq th: thm = th RS @{thm eq_reflection};

  fun match_object_rule th trm =
    case trm of
      Const (@{const_name GD.eq},  _) $ _ $ _ =>
        (case try reflect_eq th of SOME th' => [th'] | NONE => [])
    | _ => []

  fun mksimps _ th =
    case Thm.concl_of th of
       Const (@{const_name "Pure.eq"}, _) $ _ $ _ => [th]
     | Const (@{const_name "GD.Trueprop"}, _) $ x => match_object_rule th x
     | _ => []

  fun step_tac ctxt i =
    let
      val close = reflexive_thm :: Simplifier.prems_of ctxt
      val tac =
        assume_tac ctxt
        ORELSE' resolve_tac ctxt close
        ORELSE' GDAuto.gd_auto_tac ctxt
    in
      REPEAT_DETERM (CHANGED (tac i))
    end

  val gd_solver =
    Raw_Simplifier.mk_solver "GD_solver" step_tac
end;

let
  fun set_solver ctxt =
    Raw_Simplifier.setSolver (ctxt, GD_Simp.gd_solver)
  fun set_ssolver ctxt =
    Raw_Simplifier.setSSolver (ctxt, GD_Simp.gd_solver)
  fun configure ctxt =
    ctxt
    |> Simplifier.set_mksimps GD_Simp.mksimps
    |> Simplifier.set_subgoaler asm_full_simp_tac
    |> set_solver
    |> set_ssolver
in
  Theory.setup (Simplifier.map_theory_simpset configure)
end;
```

// TODO: proof of leq_refl. Making use of induction,
// natural number case distinction, rewrites with eqSubst
// 1. unfold_def tac
// 2. compatibility with simp
// 3. auto as subgoaler for simp
// 4. rewrite engine (subst for substEq and)
// 5. iff for simp
// 6. cond. exponential.
// 7. cases for bool/num
// 8. induct for num (and strong induct)

