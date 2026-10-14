(*  Title:      pure/gd_hammer.ML
    Author:     Omar Muhammad

Mode A of the GD hammer: a relevance oracle.

Translates a GD goal and a pool of GD facts into untyped first-order logic
(TPTP FOF), runs an external prover, and reports which facts it used.  The
proof is NOT imported: the answer is a list of lemma names to try, and the
Isabelle kernel remains the only thing that certifies anything.  A lossy
translation therefore costs at most a bad suggestion.

The translation is classical, so it is faithful exactly on the decided
fragment (see GD_Classical.thy): "~" is GD's negation, which coincides with
classical negation only when the formula is B.  Two consequences:

  * "p B" translates to $true.  Decidedness is what the classical side
    assumes, so B-hypotheses carry no information there -- which means
    B-plumbing lemmas will never appear in a suggestion even when the GD
    replay needs them.  auto / gd_simp usually supply those.

  * Equality is grounded: "a = b" becomes  gnat(a) & a = b,  so the prover
    gets native equality reasoning while groundedness stays tracked.

Anything the translation does not recognise is abstracted to a fresh opaque
constant, memoised so that identical subterms stay identical.  That keeps the
translation total.
*)

signature GD_HAMMER =
sig
  val tptp_of_prop: term -> string * (term * string) list
  val useful: term -> bool
  val facts_of: Proof.context -> (string * thm) list
  val fof: string -> string -> term -> string
  val used_labels: string -> string list
  val run: Proof.context -> int -> term -> string list option
end;

structure GD_Hammer: GD_HAMMER =
struct

(* ------------------------------------------------------------------ *)
(* names                                                               *)
(* ------------------------------------------------------------------ *)

fun sanitize s =
  let
    val s' =
      String.translate
        (fn c => if Char.isAlphaNum c orelse c = #"_" then String.str c else "_") s;
  in if s' = "" then "x" else s' end;

fun fn_name n = "g_" ^ String.map Char.toLower (sanitize (Long_Name.base_name n));
fun free_name n = "k_" ^ String.map Char.toLower (sanitize n);
fun var_name (n, i) = "V" ^ sanitize n ^ (if i = 0 then "" else string_of_int i);

fun app f [] = f
  | app f args = f ^ "(" ^ commas args ^ ")";

(* ------------------------------------------------------------------ *)
(* translation                                                         *)
(* ------------------------------------------------------------------ *)

(*bs holds the enclosing binders, innermost first, as (tptp name, type).*)
(*One table per problem, not per formula.  Each fact used to be translated
  in its own call with the counter restarting, so a fact's abs0 and the
  goal's abs0 were different terms sharing a name -- and the prover would
  "prove" the goal by unifying them.  run resets this once per problem.*)
val absmap = Unsynchronized.ref ([]: (term * string) list);

fun reset_abs () = absmap := [];

fun tptp_of_prop t0 =
  let
    val vars = Unsynchronized.ref ([]: string list);
    fun reg_var v = (if member (op =) (! vars) v then () else vars := v :: ! vars; v);
    fun abstract t =
      (case AList.lookup (op aconv) (! absmap) t of
        SOME s => s
      | NONE =>
          let val s = "abs" ^ string_of_int (length (! absmap))
          in absmap := (t, s) :: ! absmap; s end);

    fun typ_of bs t = fastype_of1 (map snd bs, t);

    fun tm bs t =
      (case Term.strip_comb t of
        (Bound i, []) => fst (nth bs i)
      | (Free (x, _), []) => free_name x
      | (Var (xi, _), []) => reg_var (var_name xi)
      | (Const (@{const_name GD.zero}, _), []) => "zero"
      | (Const (@{const_name GD.suc}, _), [a]) => app "suc" [tm bs a]
      | (Const (@{const_name GD.pred}, _), [a]) => app "pred" [tm bs a]
      | (Const (n, _), args) =>
          if forall (fn a => typ_of bs a = @{typ num}) args
          then app (fn_name n) (map (tm bs) args)
          else abstract t
      | _ => abstract t)

    (*"p B" is not $true: GD is paracomplete, so a B-goal is a real goal.
      Two cases are exact, both directions being GD theorems:
        (a = b) B  <->  a N & b N        (eqTI / eqE, primitive)
        (~p) B     <->  p B              (not_bool / dNegE + disjI1,2)
      Everything else becomes an opaque atom -- unprovable rather than
      trivially true, so the oracle reports nothing instead of lying.*)
    and bcheck bs p =
      (case Term.strip_comb p of
        (Const (@{const_name GD.eq}, _), [a, b]) =>
          "(gnat(" ^ tm bs a ^ ") & gnat(" ^ tm bs b ^ "))"
      | (Const (@{const_name GD.not}, _), [q]) => bcheck bs q
      | _ => abstract (Const (@{const_name GD.bJudg}, @{typ "o => o"}) $ p))

    and eqf bs a b =
      let val (x, y) = (tm bs a, tm bs b)
      in "(gnat(" ^ x ^ ") & " ^ x ^ " = " ^ y ^ ")" end

    and quant bs q conn T b =
      let
        val v = "X" ^ string_of_int (length bs);
        val bs' = (v, T) :: bs;
      in "(" ^ q ^ " [" ^ v ^ "] : (gnat(" ^ v ^ ") " ^ conn ^ " " ^ fm bs' b ^ "))" end

    and fm bs t =
      (case Term.strip_comb t of
        (Const (@{const_name GD.not}, _), [p]) => "(~ " ^ fm bs p ^ ")"
      (*p B unfolds definitionally to p or ~p, so catch that spelling here
        too: classically it is a tautology, in GD it is a real goal.*)
      | (Const (@{const_name GD.disj}, _), [p, q]) =>
          (case Term.strip_comb q of
            (Const (@{const_name GD.not}, _), [q']) =>
              if p aconv q' then bcheck bs p
              else "(" ^ fm bs p ^ " | " ^ fm bs q ^ ")"
          | _ => "(" ^ fm bs p ^ " | " ^ fm bs q ^ ")")
      | (Const (@{const_name GD.conj}, _), [p, q]) =>
          "(" ^ fm bs p ^ " & " ^ fm bs q ^ ")"
      | (Const (@{const_name GD.impl}, _), [p, q]) =>
          "(" ^ fm bs p ^ " => " ^ fm bs q ^ ")"
      | (Const (@{const_name GD.iff}, _), [p, q]) =>
          "(" ^ fm bs p ^ " <=> " ^ fm bs q ^ ")"
      | (Const (@{const_name GD.eq}, _), [a, b]) => eqf bs a b
      | (Const (@{const_name GD.neq}, _), [a, b]) => "(~ " ^ eqf bs a b ^ ")"
      | (Const (@{const_name GD.isNat}, _), [a]) => app "gnat" [tm bs a]
      | (Const (@{const_name GD.bJudg}, _), [p]) => bcheck bs p
      | (Const (@{const_name GD.True}, _), []) => "$true"
      | (Const (@{const_name GD.False}, _), []) => "$false"
      | (Const (@{const_name GD.forall}, _), [Abs (_, T, b)]) => quant bs "!" "=>" T b
      | (Const (@{const_name GD.exists}, _), [Abs (_, T, b)]) => quant bs "?" "&" T b
      | (Const (@{const_name GD.cond}, _), [c, p, q]) =>
          if typ_of bs p = @{typ o}
          then "((" ^ fm bs c ^ " & " ^ fm bs p ^ ") | ((~ " ^ fm bs c ^ ") & " ^
                 fm bs q ^ "))"
          else abstract t
      | (Const (n, _), args) =>
          if forall (fn a => typ_of bs a = @{typ num}) args
          then app (fn_name n) (map (tm bs) args)
          else abstract t
      | _ => abstract t)

    (*Pure structure.  A meta-quantified num variable ranges over all terms,
      grounded or not, so it is NOT relativised -- unlike an object-level
      forall, which quantifies only over naturals.*)
    and prop bs t =
      (case t of
        Const ("Pure.imp", _) $ a $ b =>
          "(" ^ prop bs a ^ " => " ^ prop bs b ^ ")"
      | Const ("Pure.all", _) $ Abs (_, T, b) =>
          let
            val v = "X" ^ string_of_int (length bs);
            val bs' = (v, T) :: bs;
          in "(! [" ^ v ^ "] : " ^ prop bs' b ^ ")" end
      | Const (@{const_name GD.Trueprop}, _) $ p => fm bs p
      | _ => abstract t);

    val s = prop [] t0;
    val s' =
      if null (! vars) then s
      else "(! [" ^ commas (rev (! vars)) ^ "] : " ^ s ^ ")";
  in (s', rev (! absmap)) end;

(* ------------------------------------------------------------------ *)
(* fact selection                                                      *)
(* ------------------------------------------------------------------ *)

(*A schematic variable whose type mentions o is a schema over formulas: type
  o itself (disjI1's ?P) or a predicate, num => o (eqSubst's ?Q).  FOF is
  first order and cannot quantify over either, and the prover has the
  propositional schemas natively anyway.  Note this tests the TYPE of the
  variable, not what the fact says about naturals: mult_terminates has only
  ?a, ?b :: num and is kept.
  Facts whose translation carries no content are dropped too -- that is every
  B-closure lemma, since "p B" is $true on the classical side.*)
fun mentions_o T = exists_subtype (fn T' => T' = @{typ o}) T orelse T = @{typ o};

fun has_prop_var t =
  Term.exists_subterm (fn Var (_, T) => mentions_o T | _ => false) t;

(*Does the translation say anything a first-order prover can use?  Note the
  implication and equivalence arrows must go before looking for "=", or every
  implication would count as containing an equality.*)
fun trivial s =
  let
    val s' = space_implode " " (space_explode "<=>" s);
    val s'' = space_implode " " (space_explode "=>" s');
  in
    not (String.isSubstring "gnat" s'' orelse String.isSubstring "=" s'' orelse
         String.isSubstring "g_" s'')
  end;

fun useful t = not (has_prop_var t) andalso not (trivial (fst (tptp_of_prop t)));

fun facts_of ctxt =
  let
    fun named ts = Named_Theorems.get ctxt ts;
    val pool =
      named @{named_theorems auto} @ named @{named_theorems cond} @
      Assumption.all_prems_of ctxt;
    fun entry th =
      let val n = Thm_Name.print (Thm.get_name_hint th)
      in if n = "" orelse String.isSubstring "unknown" n then NONE
         else SOME (n, th) end;
  in
    pool
    |> filter (fn th => useful (Thm.prop_of th))
    |> map_filter entry
    |> distinct (fn ((_, a), (_, b)) => Thm.eq_thm_prop (a, b))
  end;

(* ------------------------------------------------------------------ *)
(* running the prover                                                  *)
(* ------------------------------------------------------------------ *)

fun fof name role t = "fof(" ^ name ^ ", " ^ role ^ ", " ^ fst (tptp_of_prop t) ^ ").";

(*E lists the axioms it used as  fof(NAME, axiom, ...)  lines inside the
  CNFRefutation block.  Those NAMEs are our f<i> labels.*)
fun used_labels out =
  let
    fun label l =
      if String.isPrefix "fof(" l then
        (case space_explode "," (String.extract (l, 4, NONE)) of
          nm :: role :: _ =>
            if String.isPrefix " axiom" role then SOME nm else NONE
        | _ => NONE)
      else NONE;
  in map_filter label (split_lines out) end;

fun run ctxt secs goal =
  let
    val _ = reset_abs ();
    val labelled =
      map_index (fn (i, (n, th)) => ("f" ^ string_of_int i, n, th)) (facts_of ctxt);
    val problem =
      cat_lines
        (map (fn (l, _, th) => fof l "axiom" (Thm.prop_of th)) labelled @
          [fof "gd_goal" "conjecture" goal]);
    (*E's --cpu-limit relies on RLIMIT_CPU, which Cygwin refuses to set, so
      the prover would otherwise run forever on an unprovable goal.  The
      external timeout is the one that actually bites.*)
    val cmd =
      "timeout " ^ string_of_int secs ^ " " ^
        Bash.string (getenv "E_HOME" ^ "/eprover") ^
        " --auto --tptp3-format -s --proof-object --cpu-limit=" ^
        string_of_int secs ^ " ";
    (*E writes an RLIMIT_CPU warning to stderr on Cygwin for every call; it is
      harmless and would otherwise be printed at the user.*)
    val quiet = " 2>/dev/null";
    val out =
      Isabelle_System.with_tmp_file "gd_hammer" "p" (fn path =>
        (File.write path problem;
         fst (Isabelle_System.bash_output (cmd ^ File.bash_path path ^ quiet))));
    fun name_of l =
      (case find_first (fn (l', _, _) => l' = l) labelled of
        SOME (_, n, _) => SOME n
      | NONE => NONE);
  in
    if String.isSubstring "SZS status Theorem" out
    then SOME (distinct (op =) (map_filter name_of (used_labels out)))
    else NONE
  end;

(* ------------------------------------------------------------------ *)
(* the command                                                         *)
(* ------------------------------------------------------------------ *)

fun hammer_cmd secs st =
  let
    val ctxt = Toplevel.context_of st;
    val goal_thm = #goal (Proof.goal (Toplevel.proof_of st));
  in
    (case Thm.prems_of goal_thm of
      [] => writeln "gd_hammer: no subgoals"
    | sg :: _ =>
        (case run ctxt secs sg of
          NONE => writeln ("gd_hammer: no proof found (" ^ string_of_int secs ^ "s)")
        | SOME [] => writeln "gd_hammer: proved with no facts -- try  by auto"
        | SOME ns =>
            writeln ("gd_hammer: try  using " ^ space_implode " " ns ^ "  or  by (auto simp: " ^
              space_implode " " ns ^ ")")))
  end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>gd_hammer\<close>
    "suggest facts for the current goal via an external prover"
    (Scan.optional Parse.nat 10 >> (fn secs => Toplevel.keep_proof (hammer_cmd secs)));

end;
