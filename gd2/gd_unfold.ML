(*  Title:      gd2/gd_unfold.ML

unfold_def: unfold recursive definitions exactly once.

Definitions from gd_def are meta-equalities  f x \<equiv> body  whose body mentions f
again, so "unfolding f_def" or "simp add: f_def" would not terminate.
unfold_def f_def rewrites only the outermost occurrences of f in the goal and
does not look inside what it produced.
*)

val _ =
  Theory.setup
    (Method.setup @{binding unfold_def}
      (Attrib.thms >> (fn ths => fn ctxt =>
        SIMPLE_METHOD' (fn i =>
          CHANGED (CONVERSION (Conv.top_sweep_rewrs_conv ths ctxt) i))))
      "unfold (recursive) definitions once, at their outermost occurrences");
