(*  Title:      gd2/gd_simp.ML

Simplifier setup for GD2.  A fact is turned into rewrite rules as follows:

  a \<equiv> b     stays as it is
  a = b     a \<equiv> b          (eq_reflection)
  \<not> p       p \<equiv> 0          (falseE, then eq_reflection)
  p         p \<equiv> 1          (trueE, then eq_reflection)

so any proved formula can be rewritten to its truth value, and a proved
equation between terms rewrites the left side to the right.  Premises of
conditional rules are discharged by the auto solver (gd_auto.ML).  Trivial
rules (lhs = rhs, e.g. from the fact 1) are dropped.
*)

structure GD_Simp =
struct

fun trivial th =
  (case try Logic.dest_equals (Thm.concl_of th) of
    SOME (l, r) => l aconv r
  | NONE => false);

fun mk_eqs _ th =
  let
    val rules =
      (case Thm.concl_of th of
        Const (@{const_name Pure.eq}, _) $ _ $ _ => [th]
      | Const (@{const_name GD_Core.Trueprop}, _) $ p =>
          (case p of
            Const (@{const_name GD_Core.eq}, _) $ _ $ _ =>
              [th RS @{thm eq_reflection}]
          | Const (@{const_name GD_Core.not}, _) $ _ =>
              [(th RS @{thm falseE}) RS @{thm eq_reflection}]
          | _ => [(th RS @{thm trueE}) RS @{thm eq_reflection}])
      | _ => []);
  in filter_out trivial rules end
  handle THM _ => [];

end;

val _ =
  let
    val solver = Raw_Simplifier.mk_solver "GD_solver" GDAuto.gd_auto_tac;
  in
    Theory.setup (Simplifier.map_theory_simpset (fn ctxt =>
      ctxt
      |> Simplifier.set_mksimps GD_Simp.mk_eqs
      |> Raw_Simplifier.set_unsafe_solver solver
      |> Raw_Simplifier.set_safe_solver solver))
  end;

val _ =
  Theory.setup
    (Method.setup @{binding gd_simp}
      (Scan.optional (Scan.lift Parse.nat >> SOME) NONE >> (fn opt_n => fn ctxt =>
        let
          val ctxt' =
            (case opt_n of
              NONE => ctxt
            | SOME n => Config.put gd_auto_depth_limit n ctxt);
        in SIMPLE_METHOD' (fn i => CHANGED (asm_simp_tac ctxt' i)) end))
      "simp with the GD solver; optional solver depth");
