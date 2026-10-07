(*
Recursive definitions for GD_Core.  See the section "Recursive definitions"
of GD_Core.thy.

  gd_def f :: "tm => tm => tm" and g :: "tm => tm"
    where "f x y == body_f" and "g z == body_g"
      defines f and g as the components of one fixed point (fix, from
      GD_Core) and proves their unfolding equations, named <c>_def unless
      named explicitly.  The underlying Pure definitions are <c>_raw_def.
      Adds no axioms.

  gd_fuel f
      defines the fuel versions <c>_fuel of every constant of f's block, with
      unfolding equations <c>_fuel_def.  An ordinary gd_def block.

  gd_approx f
      adds, for every constant of f's block, the least-fixed-point axiom
      <c>_approx (defining the fuel versions first if needed).  Only for
      finitary blocks (A5).  This is the one command here that adds axioms:
      it is opt-in so that thm_deps shows exactly which results rely on it.

  print_gd_defs
      lists the registry.

Conditions (see GD_Core.thy).  A1-A4 are what it takes to build the fixed
point; they are checked here only to explain a rejection, since Pure checks
the resulting definitions anyway.  A5 is soundness-critical.

  A1  every defined constant is declared in the block, with type
      tm => ... => tm;
  A2  the left-hand side is the constant fully applied to pairwise distinct
      variables;
  A3  every variable of the body occurs on the left;
  A4  exactly one equation per constant, and every constant declared in the
      block has one;
  A5  (for gd_approx only) every block body is finitary: built from
      variables, the primitives 0 \<bottom> S P = \<not> \<or> if, the definitions N and B,
      constants of the block (fully applied), and constants of earlier
      finitary blocks.  No \<Lambda>, \<cdot>, \<forall>, other Pure definitions, or Pure-level
      abstraction.

A5 used to be "no block constant under a binder".  That was unsound: under
call-by-name a recursive call can be passed unevaluated to a helper
definition that wraps it in a \<Lambda>, and another helper can force that \<Lambda> under \<forall>
at unboundedly many depths (see the audit in GD_Def_Test.thy).  In the
finitary fragment evaluation derivations are finite, which is what approx
needs (O5 in GD_Core.thy).
*)

signature GD_DEF =
sig
  type entry = {def_thm: thm, block: string list, finitary: bool,
    fuel_thm: thm option, approx_thm: thm option, grounding: thm list}
  val get: Context.generic -> entry Symtab.table
  val lookup: Context.generic -> string -> entry option
  val define_block: ((binding * typ) * mixfix) list -> term list ->
    (term list * term) list -> theory -> (term list * thm list) * theory
  val pretty: Proof.context -> Pretty.T
end;

structure GD_Def: GD_DEF =
struct

(** registry **)

(*def_thm: the unfolding equation; block: all constants defined by the same
  gd_def; finitary: whether the block satisfies A5 (recorded at definition
  time, used by later blocks and by gd_approx)*)
type entry = {def_thm: thm, block: string list, finitary: bool,
  fuel_thm: thm option, approx_thm: thm option, grounding: thm list};

fun base c = Long_Name.base_name c;

fun merge_opt (SOME x, _) = SOME x
  | merge_opt (NONE, y) = y;

(*A constant is defined once, in one theory, so two entries for it can only
  differ in what was added on separate branches afterwards.*)
fun merge_entry (e1: entry, e2: entry) : entry =
  {def_thm = #def_thm e1, block = #block e1, finitary = #finitary e1,
   fuel_thm = merge_opt (#fuel_thm e1, #fuel_thm e2),
   approx_thm = merge_opt (#approx_thm e1, #approx_thm e2),
   grounding = Library.merge Thm.eq_thm_prop (#grounding e1, #grounding e2)};

structure Data = Generic_Data
(
  type T = entry Symtab.table;
  val empty = Symtab.empty;
  fun merge data = Symtab.join (K merge_entry) data;
);

val get = Data.get;
fun lookup context name = Symtab.lookup (get context) name;

fun register c e = Data.map (Symtab.update (c, e));

fun map_entry c f = Data.map (Symtab.map_entry c f);

fun add_grounding cname th =
  Data.map (fn tab =>
    (case Symtab.lookup tab cname of
      NONE =>
        error ("grounded_by: " ^ quote cname ^ " was not introduced by gd_def")
    | SOME {def_thm, block, finitary, fuel_thm, approx_thm, grounding} =>
        Symtab.update (cname,
          {def_thm = def_thm, block = block, finitary = finitary,
           fuel_thm = fuel_thm, approx_thm = approx_thm,
           grounding = Library.insert Thm.eq_thm_prop th grounding}) tab));


(** object-logic vocabulary **)

val tmT = @{typ tm};

val zero = Const (@{const_name GD_Core.zero}, tmT);
val bot = Const (@{const_name GD_Core.bot}, tmT);
fun pred t = Const (@{const_name GD_Core.pred}, tmT --> tmT) $ t;
fun eq a b = Const (@{const_name GD_Core.eq}, tmT --> tmT --> tmT) $ a $ b;
fun cond c a b =
  Const (@{const_name GD_Core.cond}, tmT --> tmT --> tmT --> tmT) $ c $ a $ b;
fun is_nat t = Const (@{const_name GD_Core.isNat}, tmT --> tmT) $ t;
fun tprop t = Const (@{const_name GD_Core.Trueprop}, tmT --> propT) $ t;
fun app a b = Const (@{const_name GD_Core.app}, tmT --> tmT --> tmT) $ a $ b;
fun lam t = Const (@{const_name GD_Core.lam}, (tmT --> tmT) --> tmT) $ t;
fun fix t = Const (@{const_name GD_Core.fix}, (tmT --> tmT) --> tmT) $ t;

(*tm => ... => tm, including tm itself*)
fun is_tm_fun T =
  forall (fn U => U = tmT) (binder_types T) andalso body_type T = tmT;


(** the fixed-point construction **)

(*selector of an m-tuple:  \<Lambda>y1 ... ym. yi*)
fun proj m i =
  let
    fun go j =
      if j > m then Bound (m - i)
      else lam (Abs ("y" ^ string_of_int j, tmT, go (j + 1)));
  in go 1 end;

(*component i of the tuple G as a Pure function of arity n:
  \<lambda>z1 ... zn. G \<cdot> \<pi>i \<cdot> z1 \<cdot> ... \<cdot> zn*)
fun component m G (i, n) =
  let
    val body = fold (fn k => fn acc => app acc (Bound (n - k))) (1 upto n) (app G (proj m i));
  in funpow n (fn t => Abs ("z", tmT, t)) body end;

(*Head of an application chain  h \<cdot> a1 \<cdot> ... \<cdot> an.*)
fun at_head cv ct =
  (case Thm.term_of ct of
    Const (@{const_name GD_Core.app}, _) $ _ $ _ => Conv.fun_conv (Conv.arg_conv (at_head cv)) ct
  | _ => cv ct);

(*One beta step at the head redex of an application chain.*)
fun beta_step ct =
  (case Thm.term_of ct of
    Const (@{const_name GD_Core.app}, _) $ (Const (@{const_name GD_Core.lam}, _) $ _) $ _ =>
      Conv.rewr_conv @{thm beta} ct
  | Const (@{const_name GD_Core.app}, _) $ _ $ _ => Conv.fun_conv (Conv.arg_conv beta_step) ct
  | _ => raise CTERM ("gd_def: no head redex", [ct]));

(*Define the constants of a block and prove their unfolding equations.
  consts: declarations; frees: the Frees standing for them in eqs; eqs: for
  each constant (same order) its argument Frees and its body.  Assumes A1-A4.*)
fun define_block consts frees eqs thy =
  let
    val m = length consts;
    val arities = map (length o binder_types o #2 o #1) consts;
    val idx = 1 upto m;
    fun components G = map2 (fn d => fn i => (d, component m G (i, nth arities (i - 1)))) frees idx;

    val used =
      fold (fn (args, rhs) => fold Term.add_free_names (rhs :: args)) eqs
        (map (#1 o dest_Free) frees);
    val g = Free (singleton (Name.variant_list used) "g", tmT);
    (*Ci g = \<Lambda>x1 ... xn. body_i[fj := component j of g]*)
    val entries =
      map (fn (args, rhs) =>
          fold_rev (fn x => fn t => lam (Term.lambda x t)) args
            (Envir.beta_norm (Term.subst_free (components g) rhs)))
        eqs;
    val F = Term.lambda g (lam (Abs ("s", tmT, fold (fn c => fn acc => app acc c) entries (Bound 0))));
    val G = fix F;

    val (cs, thy1) = fold_map Sign.declare_const_global consts thy;
    val (raw_defs, thy2) =
      fold_map (fn ((((b, _), _), c), (_, comp)) =>
          Global_Theory.add_def (Binding.suffix_name "_raw_def" b, Logic.mk_equals (c, comp)))
        (consts ~~ cs ~~ components G) thy1;

    val ctxt = Proof_Context.init_global thy2;
    val cert = Thm.cterm_of ctxt;
    fun unfold_conv n =
      Conv.every_conv
        (at_head (Conv.rewr_conv @{thm fix_unfold}) :: replicate (1 + m + n) beta_step);
    fun internal c msg =
      error ("gd_def: could not prove the unfolding equation of " ^
        quote (base (dest_Const_name c)) ^ " (internal error)\n" ^ msg);
    (*th: a == b  gives  a == b' with b' the beta-eta normal form of b*)
    fun norm_rhs th =
      let val th' = Thm.transitive th (Thm.beta_conversion true (Thm.rhs_of th))
      in Thm.transitive th' (Thm.eta_conversion (Thm.rhs_of th')) end;
    (*Both sides are reduced to the same term, body_i with every block
      constant replaced by its component of fix F, by primitive inferences
      only (no simplifier):
        left:   c x1 .. xn == fix F \<cdot> \<pi>i \<cdot> x1 .. xn    (raw_def, Pure beta)
                           == body_i[cj := component j]   (fix_unfold, 1 + m + n beta)
        right:  body_i == body_i[cj := component j]       (raw_defs under a context)*)
    fun prove ((args, rhs), ((c, n), raw_def)) =
      let
        val body = Envir.beta_norm (Term.subst_free (frees ~~ cs) rhs);
        val goal = Logic.mk_equals (list_comb (c, args), body);
        val app_def =
          norm_rhs (fold (fn x => fn th => Thm.combination th (Thm.reflexive (cert x))) args raw_def);
        val left = Thm.transitive app_def (unfold_conv n (Thm.rhs_of app_def));
        val ctx = fold_rev Term.lambda cs body;
        val inst = fold (fn d => fn th => Thm.combination th d) raw_defs (Thm.reflexive (cert ctx));
        val right =
          Thm.transitive (Thm.symmetric (Thm.beta_conversion true (Thm.lhs_of inst))) inst;
        val eqn = Thm.transitive (norm_rhs left) (Thm.symmetric (norm_rhs right));
      in
        Goal.prove ctxt (map (#1 o dest_Free) args) [] goal (fn {context = ctxt', ...} =>
          resolve_tac ctxt' [eqn] 1)
      end
      handle
        ERROR msg => internal c msg
      | THM (msg, _, _) => internal c msg
      | CTERM (msg, _) => internal c msg
      | TERM (msg, _) => internal c msg;
  in ((cs, map prove (eqs ~~ (cs ~~ arities ~~ raw_defs))), thy2) end;


(** reading an equation back **)

(*Replace outer Pure quantifiers by schematic variables.*)
fun strip_all t =
  let
    val i = Term.maxidx_of_term t + 1;
    fun go (Const (@{const_name Pure.all}, _) $ Abs (x, T, b)) =
          go (Term.subst_bound (Var ((x, i), T), b))
      | go u = u;
  in go t end;

(*c x1 ... xn == rhs, with nothing else around it*)
fun dest_def th =
  (case try Logic.dest_equals (strip_all (Thm.prop_of th)) of
    SOME (lhs, rhs) =>
      (case strip_comb lhs of
        (Const (c, T), args) => SOME (c, T, lhs, args, rhs)
      | _ => NONE)
  | NONE => NONE);


(** A5: finitary bodies **)

(*Primitives whose evaluation clauses are finitary (no omega-quantifier, no
  function values), and the two type-check definitions built from them.*)
val finitary_prims =
  [@{const_name GD_Core.zero}, @{const_name GD_Core.bot}, @{const_name GD_Core.suc},
   @{const_name GD_Core.pred}, @{const_name GD_Core.eq}, @{const_name GD_Core.not},
   @{const_name GD_Core.disj}, @{const_name GD_Core.cond},
   @{const_name GD_Core.isNat}, @{const_name GD_Core.isBool}];

fun finitary_const context c =
  member (op =) finitary_prims c orelse
  (case lookup context c of
    SOME e => #finitary e
  | NONE => false);

(*true iff t is a finitary body for the given block ((name, type) list)*)
fun a5_ok context block t =
  let
    fun arity c = length (binder_types (the (AList.lookup (op =) block c)));
    fun ok u =
      let val (h, ts) = strip_comb u in
        (case h of
          Const (c, _) =>
            (if AList.defined (op =) block c then length ts = arity c
             else finitary_const context c)
            andalso forall ok ts
        | Var _ => null ts
        | Free _ => null ts
        | _ => false)
      end;
  in ok (Envir.beta_norm t) end;


(** fuel versions and approximation axioms **)

fun fuel_name c = base c ^ "_fuel";

(*schematic variables to fixed ones*)
val freeze =
  Term.map_aterms
    (fn Var ((x, i), T) =>
          Free (if i = 0 then x else x ^ "_" ^ string_of_int i, T)
      | a => a);

(*fresh names for the fuel argument and the approx conclusion*)
fun block_parts block defs =
  let
    val var_names = fold (fn (_, _, args, rhs) =>
      fold Term.add_free_names (rhs :: args)) defs [];
    val _ =
      (case inter (op =) var_names (map (fuel_name o #1) block) of
        [] => ()
      | clash => error ("gd_fuel: variable name clashes with generated constant: " ^
          commas_quote clash));
    val fresh = Name.variant_list (var_names @ map (fuel_name o #1) block) ["k", "R"];
    val k = Free (nth fresh 0, tmT);
    val R = Free (nth fresh 1, propT);
  in (k, R) end;

(*f_fuel k x1 ... xn == if k = 0 then \<bottom> else body[g := g_fuel (P k)], as
  arguments and body for define_block*)
fun fuel_eq block fuel_free k (_, _, args, rhs) =
  let
    val fuelize =
      Term.map_aterms
        (fn Const (d, T) =>
              if AList.defined (op =) block d then fuel_free d $ pred k
              else Const (d, T)
          | a => a);
  in (k :: args, cond (eq k zero) bot (fuelize (Envir.beta_norm rhs))) end;

fun approx_spec fuel_const k R (c, T, args, _) =
  let
    val fa = list_comb (Const (c, T), args);
    val ffa = list_comb (fuel_const c, k :: args);
  in
    ((Binding.name (base c ^ "_approx"), []),
     Logic.list_implies
       ([tprop (is_nat fa),
         Logic.all k (Logic.list_implies ([tprop (is_nat k), tprop (eq ffa fa)], R))],
        R))
  end;


(** looking up blocks **)

fun entry_of context c =
  (case lookup context c of
    SOME e => e
  | NONE => error (quote (base c) ^ " was not introduced by gd_def"));

fun read_block_names thy raw_names =
  let
    val ctxt = Proof_Context.init_global thy;
    val context = Context.Theory thy;
    val cs =
      map (dest_Const_name o Proof_Context.read_const {proper = true, strict = false} ctxt)
        raw_names;
  in distinct (op =) (map (#block o entry_of context) cs) end;

(*(name, type) list and frozen (name, type, args, rhs) list of a block*)
fun block_defs context block_names =
  let
    val defs =
      map (fn c =>
          (case dest_def (#def_thm (entry_of context c)) of
            SOME (c', T, _, args, rhs) => (c', T, map freeze args, freeze rhs)
          | NONE => error ("gd_fuel: malformed definition of " ^ quote (base c))))
        block_names;
  in (map (fn (c, T, _, _) => (c, T)) defs, defs) end;


(** gd_fuel **)

(*Define the fuel constants of a block; a no-op if they exist already.*)
fun fuel_block block_names thy =
  let
    val context = Context.Theory thy;
  in
    if forall (is_some o #fuel_thm o entry_of context) block_names then thy
    else
      let
        val (block, defs) = block_defs context block_names;
        val (k, _) = block_parts block defs;
        val fuel_frees = map (fn (c, T) => (c, Free (fuel_name c, tmT --> T))) block;
        fun fuel_free c = the (AList.lookup (op =) fuel_frees c);
        val consts =
          map (fn (c, T) => ((Binding.name (fuel_name c), tmT --> T), NoSyn)) block;
        val eqs = map (fuel_eq block fuel_free k) defs;
        val ((fuel_cs, eq_thms), thy1) = define_block consts (map #2 fuel_frees) eqs thy;
        val (fuel_thms, thy2) =
          fold_map (fn ((c, _), th) =>
              Global_Theory.store_thm (Binding.name (fuel_name c ^ "_def"), th))
            (block ~~ eq_thms) thy1;
        val fuel_consts = map dest_Const_name fuel_cs;
        (*the fuel constants form a finitary block of their own iff the
          original block is finitary*)
        val finitary = #finitary (entry_of context (hd block_names));
        fun set_fuel th {def_thm, block, finitary, fuel_thm = _, approx_thm, grounding} =
          {def_thm = def_thm, block = block, finitary = finitary,
           fuel_thm = SOME th, approx_thm = approx_thm, grounding = grounding};
      in
        thy2
        |> fold2 (fn c => fn th => Context.theory_map (map_entry c (set_fuel th)))
            block_names fuel_thms
        |> fold2 (fn fc => fn th => Context.theory_map (register fc
            {def_thm = th, block = fuel_consts, finitary = finitary,
             fuel_thm = NONE, approx_thm = NONE, grounding = []}))
            fuel_consts fuel_thms
      end
  end;

fun gd_fuel_cmd raw_names thy = fold fuel_block (read_block_names thy raw_names) thy;


(** gd_approx **)

fun approx_block block_names thy =
  let
    val context = Context.Theory thy;
    val entries = map (entry_of context) block_names;
    val _ =
      if exists (is_some o #approx_thm) entries then
        error ("gd_approx: " ^ commas_quote (map base block_names) ^
          " already has approx axioms")
      else ();
    val _ =
      if forall #finitary entries then ()
      else
        error ("gd_approx: the block " ^ commas_quote (map base block_names) ^
          " is not finitary (condition A5).\n\
          \Finitary bodies use only variables, 0 \<bottom> S P = \<not> \<or> if, N, B, constants of \
          \the block\nand of earlier finitary blocks.  Approx for anything else can be \
          \inconsistent.");

    val thy1 = fuel_block block_names thy;
    val context1 = Context.Theory thy1;
    val (block, defs) = block_defs context1 block_names;
    val (k, R) = block_parts block defs;
    fun fuel_const c =
      (case dest_def (the (#fuel_thm (entry_of context1 c))) of
        SOME (fc, fT, _, _, _) => Const (fc, fT)
      | NONE => error ("gd_approx: malformed fuel equation of " ^ quote (base c)));
    val specs = map (approx_spec fuel_const k R) defs;
    val ((_, approx_thms), thy2) = Specification.axiomatization [] [] [] specs thy1;
    fun set_approx th {def_thm, block, finitary, fuel_thm, approx_thm = _, grounding} =
      {def_thm = def_thm, block = block, finitary = finitary,
       fuel_thm = fuel_thm, approx_thm = SOME th, grounding = grounding};
  in
    fold2 (fn c => fn th => Context.theory_map (map_entry c (set_approx th)))
      block_names approx_thms thy2
  end;

fun gd_approx_cmd raw_names thy = fold approx_block (read_block_names thy raw_names) thy;


(** gd_def **)

fun gd_def_cmd raw_decls raw_specs thy =
  let
    val context = Context.Theory thy;
    val ctxt = Proof_Context.init_global thy;
    val ((params, specs), _) =
      Specification.read_multi_specs raw_decls (map (fn s => (s, [], [])) raw_specs) ctxt;
    val frees = map (fn ((b, T), _) => Free (Binding.name_of b, T)) params;
    fun const_index x = find_index (fn Free (y, _) => x = y | _ => false) frees;

    (*A1*)
    val _ =
      (case filter_out (is_tm_fun o #2 o #1) params of
        [] => ()
      | bad => error ("gd_def: type must be tm \<Rightarrow> ... \<Rightarrow> tm: " ^
          commas_quote (map (Binding.name_of o #1 o #1) bad)));

    fun check ((b, atts), t) =
      let
        fun err msg =
          error ((if Binding.is_empty b then "An equation" else Binding.print b) ^ msg);
        val vs = Term.strip_all_vars t;
        val xs =
          map2 (fn x => fn (_, T) => Free (x, T))
            (Name.variant_list (Term.add_free_names t []) (map #1 vs)) vs;
        val prop = Term.subst_bounds (rev xs, Term.strip_all_body t);
        val (lhs, rhs) =
          (case try Logic.dest_equals prop of
            SOME eqn => eqn
          | NONE => err " is not of the form  c x1 ... xn \<equiv> body");
        val (head, args) = strip_comb lhs;
        (*A1*)
        val i =
          (case head of
            Free (x, _) => const_index x
          | _ => ~1);
        val _ =
          if i >= 0 then ()
          else err ": the left-hand side must be a constant declared in this gd_def";
        val name = quote (Binding.name_of (#1 (#1 (nth params i))));
        (*A2*)
        val _ =
          if length args = length (binder_types (#2 (#1 (nth params i)))) then ()
          else error (name ^ " must be applied to all of its arguments on the left");
        val _ =
          if forall (member (op aconv) xs) args andalso not (has_duplicates (op aconv) args)
          then ()
          else error (name ^ ": the arguments on the left must be pairwise distinct \
            \variables");
        (*A3*)
        val _ =
          (case subtract (op aconv) (args @ frees) (map Free (Term.add_frees rhs [])) of
            [] => ()
          | extra =>
              error (name ^ " has " ^ commas (map (#1 o dest_Free) extra) ^
                " in the body but not on the left"));
      in (i, (b, atts), args, rhs) end;

    val checked = map check specs;

    (*A4*)
    val _ =
      (case duplicates (op =) (map #1 checked) of
        [] => ()
      | dups =>
          error ("more than one defining equation for: " ^
            commas_quote (map (fn i => Binding.name_of (#1 (#1 (nth params i)))) dups) ^
            "\nUse a single equation with if/then/else."));
    val _ =
      (case filter_out (fn i => exists (fn (j, _, _, _) => i = j) checked)
          (0 upto length params - 1) of
        [] => ()
      | missing =>
          error ("declared with no defining equation: " ^
            commas_quote (map (fn i => Binding.name_of (#1 (#1 (nth params i)))) missing)));
    val ordered =
      map (fn i => the (find_first (fn (j, _, _, _) => i = j) checked))
        (0 upto length params - 1);

    val ((cs, eq_thms), thy1) =
      define_block params frees (map (fn (_, _, args, rhs) => (args, rhs)) ordered) thy;

    (*store the equations: <c>_def unless named*)
    val (def_thms, thy2) =
      fold_map (fn (((_, (b, atts), _, _), c), th) => fn thy =>
          let
            val b' = if Binding.is_empty b then Binding.name (base (dest_Const_name c) ^ "_def") else b;
            val ((_, ths), thy') =
              Global_Theory.note_thms ""
                ((b', []), [([th], map (Attrib.attribute_global thy) atts)]) thy;
          in (the_single ths, thy') end)
        (ordered ~~ cs ~~ eq_thms) thy1;

    (*A5 is only checked by gd_approx, but recorded here: later blocks that
      call these constants need to know whether they are finitary*)
    val block = map dest_Const cs;
    val finitary =
      forall (fn (_, _, _, rhs) => a5_ok context block (Term.subst_free (frees ~~ cs) rhs))
        ordered;
    val defined = map #1 block;
  in
    fold2 (fn c => fn def_thm => Context.theory_map (register c
        {def_thm = def_thm, block = defined, finitary = finitary,
         fuel_thm = NONE, approx_thm = NONE, grounding = []}))
      defined def_thms thy2
  end;


(** outer syntax **)

val spec_list = Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Parse.prop);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>gd_def\<close>
    "GD recursive definition (a fixed point; unfolding equations are proved)"
    (Parse.vars -- (Parse.where_ |-- Parse.!!! spec_list)
      >> (fn (decls, specs) => Toplevel.theory (gd_def_cmd decls specs)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>gd_fuel\<close>
    "fuel versions of gd_def blocks (ordinary definitions)"
    (Scan.repeat1 Parse.const >> (fn names => Toplevel.theory (gd_fuel_cmd names)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>gd_approx\<close>
    "least-fixed-point (approximation) axioms for finitary gd_def blocks"
    (Scan.repeat1 Parse.const >> (fn names => Toplevel.theory (gd_approx_cmd names)));


(** [grounded_by] and print_gd_defs **)

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>grounded_by\<close>
      (Args.const {proper = true, strict = false} >> (fn cname =>
        Thm.declaration_attribute (fn th => add_grounding cname th)))
      "attach a grounding lemma to a gd_def constant");

fun pretty_entry ctxt (name, {def_thm, block, finitary, fuel_thm, approx_thm, grounding}) =
  let
    fun opt_thm label NONE = Pretty.str (label ^ ": (none)")
      | opt_thm label (SOME th) =
          Pretty.block [Pretty.str (label ^ ": "), Thm.pretty_thm ctxt th];
  in
    Pretty.chunks
      [Pretty.block [Pretty.str (base name), Pretty.str ":"],
       Pretty.indent 4 (Thm.pretty_thm ctxt def_thm),
       Pretty.indent 4 (Pretty.str ("block: " ^ commas (map base block) ^
         (if finitary then " (finitary)" else " (not finitary)"))),
       Pretty.indent 4 (opt_thm "fuel" fuel_thm),
       Pretty.indent 4 (opt_thm "approx" approx_thm),
       Pretty.indent 4
         (case grounding of
           [] => Pretty.str "grounded_by: (none)"
         | ths =>
             Pretty.block
               (Pretty.str "grounded_by: " :: Pretty.commas (map (Thm.pretty_thm ctxt) ths)))]
  end;

fun pretty ctxt =
  Pretty.big_list "gd_def definitions:"
    (map (pretty_entry ctxt) (Symtab.dest (get (Context.Proof ctxt))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_gd_defs\<close>
    "print gd_def definitions, fuel versions, approximation axioms and grounding lemmas"
    (Scan.succeed (Toplevel.keep (Pretty.writeln o pretty o Toplevel.context_of)));

end;
