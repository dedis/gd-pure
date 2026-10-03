(*
Recursive definitions for GD_Core.  Implements the axiom schemes of the
section "Recursive definitions" of GD_Core.thy.

  gd_decl f :: "tm => tm"
      declares f with no axioms, so that earlier gd_def blocks may call it
      (forward reference); a later gd_def defines it.

  gd_def f :: "tm => tm => tm" and g :: "tm => tm"
    where "f x y == body_f" and "g z == body_g"
      adds one unfolding axiom per constant, named <c>_def unless named
      explicitly.  Nothing else.

  gd_fuel f
      adds the fuel versions <c>_fuel of every constant of f's block, with
      their unfolding axioms <c>_fuel_def.  These are ordinary recursive
      definitions (A1-A4 hold by construction) and add no new kind of
      commitment.

  gd_approx f
      adds, for every constant of f's block, the least-fixed-point axiom
      <c>_approx (generating the fuel versions first if needed).  Only for
      finitary blocks (A5).  This is the one command here that asserts more
      than a definition: it is opt-in so that thm_deps shows exactly which
      results rely on it.

  print_gd_defs
      lists the registry.

This file is part of the trusted base: it adds axioms, and every check below
is soundness-critical.  Conditions (see GD_Core.thy):

  A1  every defined constant is declared in the block, or declared by gd_decl
      and not yet defined; its type is tm => ... => tm;
  A2  the left-hand side is the constant fully applied to pairwise distinct
      variables;
  A3  every variable of the body occurs on the left;
  A4  exactly one equation per constant, and every constant declared in the
      block has one;
  A5  (for gd_approx only) every block body is finitary: built from
      variables, the primitives 0 \<bottom> S P = \<not> \<or> if, the definitions N and B,
      constants of the block (fully applied), and constants of earlier
      finitary blocks.  No \<Lambda>, \<cdot>, \<forall>, other Pure definitions, constants
      declared by gd_decl but not yet defined, or Pure-level abstraction.
  A6  a constant has one definition in every theory: two theories that
      define the same constant differently (possible after a common gd_decl)
      cannot be merged.

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
  val pending: Context.generic -> string list
  val pretty: Proof.context -> Pretty.T
end;

structure GD_Def: GD_DEF =
struct

(** registry **)

(*def_thm: the unfolding axiom; block: all constants defined by the same
  gd_def; finitary: whether the block satisfies A5 (recorded at definition
  time, used by later blocks and by gd_approx)*)
type entry = {def_thm: thm, block: string list, finitary: bool,
  fuel_thm: thm option, approx_thm: thm option, grounding: thm list};

fun base c = Long_Name.base_name c;

fun merge_opt (SOME x, _) = SOME x
  | merge_opt (NONE, y) = y;

(*A6: the same constant defined by two different axioms in two merged
  theories is an inconsistency (after a shared gd_decl, one branch may
  define c \<equiv> 0 and another c \<equiv> 1), so the merge is refused.  Identical
  definitions are harmless and are accepted.*)
fun merge_entry c (e1: entry, e2: entry) =
  if Thm.eq_thm_prop (#def_thm e1, #def_thm e2) then
    {def_thm = #def_thm e1, block = #block e1, finitary = #finitary e1,
     fuel_thm = merge_opt (#fuel_thm e1, #fuel_thm e2),
     approx_thm = merge_opt (#approx_thm e1, #approx_thm e2),
     grounding = Library.merge Thm.eq_thm_prop (#grounding e1, #grounding e2)}
  else
    error ("gd_def: " ^ quote (base c) ^
      " is defined differently in two of the merged theories:\n  " ^
      Syntax.string_of_term_global (Thm.theory_of_thm (#def_thm e1))
        (Thm.prop_of (#def_thm e1)) ^ "\n  " ^
      Syntax.string_of_term_global (Thm.theory_of_thm (#def_thm e2))
        (Thm.prop_of (#def_thm e2)) ^
      "\nImporting both would make the two bodies equal.");

(*defined constants, and constants declared by gd_decl but not yet defined*)
structure Data = Generic_Data
(
  type T = entry Symtab.table * unit Symtab.table;
  val empty = (Symtab.empty, Symtab.empty);
  fun merge ((d1, p1), (d2, p2)) =
    let
      val d = Symtab.join merge_entry (d1, d2);
      val p = Symtab.merge (K true) (p1, p2);
    in (d, Symtab.fold (fn (c, _) => Symtab.delete_safe c) d p) end;
);

val get = #1 o Data.get;
fun lookup context name = Symtab.lookup (get context) name;
fun pending context = Symtab.keys (#2 (Data.get context));

fun add_pending c = Data.map (apsnd (Symtab.update (c, ())));

fun register c e =
  Data.map (fn (d, p) => (Symtab.update (c, e) d, Symtab.delete_safe c p));

fun map_entry c f = Data.map (apfst (Symtab.map_entry c f));

fun add_grounding cname th =
  Data.map (apfst (fn tab =>
    (case Symtab.lookup tab cname of
      NONE =>
        error ("grounded_by: " ^ quote cname ^ " was not introduced by gd_def")
    | SOME {def_thm, block, finitary, fuel_thm, approx_thm, grounding} =>
        Symtab.update (cname,
          {def_thm = def_thm, block = block, finitary = finitary,
           fuel_thm = fuel_thm, approx_thm = approx_thm,
           grounding = Library.insert Thm.eq_thm_prop th grounding}) tab)));


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

(*tm => ... => tm, including tm itself*)
fun is_tm_fun T =
  forall (fn U => U = tmT) (binder_types T) andalso body_type T = tmT;


(** reading an axiom back **)

(*Replace outer Pure quantifiers by schematic variables, in case the
  axiomatization closed the equation with !! instead of leaving it schematic.*)
fun strip_all t =
  let
    val i = Term.maxidx_of_term t + 1;
    fun go (Const (@{const_name Pure.all}, _) $ Abs (x, T, b)) =
          go (Term.subst_bound (Var ((x, i), T), b))
      | go u = u;
  in go t end;

(*c x1 ... xn == rhs, with nothing else around it: no premises allowed*)
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

(*schematic variables to fixed ones, so the specification can close over them*)
val freeze =
  Term.map_aterms
    (fn Var ((x, i), T) =>
          Free (if i = 0 then x else x ^ "_" ^ string_of_int i, T)
      | a => a);

(*the pieces for one block.  fuel: the fuel constants as Frees (to be declared)
  or as existing Consts; defs: (name, type, args, rhs), frozen*)
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

fun fuel_eq_spec block fuel_const k (c, _, args, rhs) =
  let
    (*replace every block constant d by  d_fuel (P k)*)
    val fuelize =
      Term.map_aterms
        (fn Const (d, T) =>
              if AList.defined (op =) block d then fuel_const d $ pred k
              else Const (d, T)
          | a => a);
  in
    ((Binding.name (fuel_name c ^ "_def"), []),
     Logic.mk_equals
       (list_comb (fuel_const c, k :: args),
        cond (eq k zero) bot (fuelize (Envir.beta_norm rhs))))
  end;

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

(*Declare the fuel constants of a block and add their equations; a no-op if
  they exist already.*)
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
        fun fuel_const c = the (AList.lookup (op =) fuel_frees c);
        val decls =
          map (fn (c, T) => (Binding.name (fuel_name c), SOME (tmT --> T), NoSyn)) block;
        val specs = map (fuel_eq_spec block fuel_const k) defs;
        val ((_, fuel_thms), thy') = Specification.axiomatization decls [] [] specs thy;
        val fuel_consts = map (fn (c, _) => Sign.full_bname thy' (fuel_name c)) block;
        (*the fuel constants form a finitary block of their own iff the
          original block is finitary*)
        val finitary = #finitary (entry_of context (hd block_names));
        fun set_fuel th {def_thm, block, finitary, fuel_thm = _, approx_thm, grounding} =
          {def_thm = def_thm, block = block, finitary = finitary,
           fuel_thm = SOME th, approx_thm = approx_thm, grounding = grounding};
      in
        thy'
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
    val fuel_consts =
      map (fn (c, T) => (c, Const (Sign.full_bname thy1 (fuel_name c), tmT --> T))) block;
    fun fuel_const c = the (AList.lookup (op =) fuel_consts c);
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


(** gd_decl **)

fun gd_decl_cmd raw_decls thy =
  let
    val ((consts, _), thy') = Specification.axiomatization_cmd raw_decls [] [] [] thy;
    val decls = map dest_Const consts;
    val _ =
      (case filter_out (is_tm_fun o #2) decls of
        [] => ()
      | bad => error ("gd_decl: type must be tm \<Rightarrow> ... \<Rightarrow> tm: " ^
          commas_quote (map (base o #1) bad)));
  in fold (Context.theory_map o add_pending o #1) decls thy' end;


(** gd_def **)

fun gd_def_cmd raw_decls raw_specs thy =
  let
    val context = Context.Theory thy;
    val pend = pending context;
    val defined_before = get context;

    (*Axioms need a nonempty name.  Unnamed equations get a hidden one here
      and are stored as <c>_def once their constant is known (below).*)
    val named_specs =
      map (fn ((b, atts), s) =>
          if Binding.is_empty b
          then ((Binding.concealed (Binding.name ("gd_def_eq_" ^ serial_string ())), atts), s)
          else ((b, atts), s))
        raw_specs;

    val ((consts, thms), thy1) =
      Specification.axiomatization_cmd raw_decls [] [] named_specs thy;
    val declared = map dest_Const_name consts;

    fun label b = if Binding.is_empty b then "An equation" else Binding.print b;

    fun check ((b, _), _) th =
      (case dest_def th of
        NONE =>
          error (label b ^ " is not of the form  c x1 ... xn \<equiv> body")
      | SOME (c, T, lhs, args, rhs) =>
          let
            val name = quote (base c);
            (*A1*)
            val _ =
              if member (op =) declared c orelse member (op =) pend c then ()
              else if Symtab.defined defined_before c then
                error (name ^ " is already defined by gd_def")
              else
                error (name ^ " is neither declared in this gd_def nor by gd_decl.\n\
                  \gd_def only defines constants it introduces; use axiomatization \
                  \for anything else.");
            val _ =
              if is_tm_fun T then ()
              else error (name ^ ": type must be tm \<Rightarrow> ... \<Rightarrow> tm");
            (*A2*)
            val _ =
              if length args = length (binder_types T) then ()
              else error (name ^ " must be applied to all of its arguments on the left");
            val _ =
              if forall is_Var args andalso not (has_duplicates (op aconv) args) then ()
              else error (name ^ ": the arguments on the left must be pairwise distinct \
                \variables.\nA pattern such as  f (P x) \<equiv> x  makes f 0 equal to two \
                \different values.");
            (*A3*)
            val _ =
              (case subtract (op =) (Term.add_vars lhs []) (Term.add_vars rhs []) of
                [] => ()
              | vs =>
                  error (name ^ " has " ^ commas (map (Term.string_of_vname o #1) vs) ^
                    " in the body but not on the left.\nSuch a variable is generalised \
                    \over the whole equation, making the left-hand side equal to \
                    \anything."));
          in (b, c, T, args, rhs) end);

    val defs = map2 check raw_specs thms;
    val defined = map #2 defs;

    (*A4*)
    val _ =
      (case duplicates (op =) defined of
        [] => ()
      | dups =>
          error ("more than one defining equation for: " ^ commas_quote (map base dups) ^
            "\nUse a single equation with if/then/else."));
    val _ =
      (case subtract (op =) defined declared of
        [] => ()
      | missing =>
          error ("declared with no defining equation: " ^ commas_quote (map base missing)));

    (*name unnamed equations <c>_def*)
    val (def_thms, thy2) =
      fold_map (fn ((b, c, _, _, _), th) => fn thy =>
          if Binding.is_empty b
          then Global_Theory.store_thm (Binding.name (base c ^ "_def"), th) thy
          else (th, thy))
        (defs ~~ thms) thy1;

    (*A5 is only checked by gd_approx, but recorded here: later blocks that
      call these constants need to know whether they are finitary*)
    val block = map (fn (_, c, T, _, _) => (c, T)) defs;
    val finitary = forall (fn (_, _, _, _, rhs) => a5_ok context block rhs) defs;
  in
    fold2 (fn c => fn def_thm => Context.theory_map (register c
        {def_thm = def_thm, block = defined, finitary = finitary,
         fuel_thm = NONE, approx_thm = NONE, grounding = []}))
      defined def_thms thy2
  end;


(** outer syntax **)

val spec_list = Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Parse.prop);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>gd_decl\<close>
    "declare constants to be defined later by gd_def (forward reference)"
    (Parse.vars >> (fn decls => Toplevel.theory (gd_decl_cmd decls)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>gd_def\<close>
    "GD recursive definition (unfolding axioms only)"
    ((Parse.vars -- (Parse.where_ |-- Parse.!!! spec_list)
      || (Parse.where_ |-- Parse.!!! spec_list >> pair []))
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
  let val context = Context.Proof ctxt in
    Pretty.chunks
      [Pretty.big_list "gd_def definitions:"
         (map (pretty_entry ctxt) (Symtab.dest (get context))),
       Pretty.block
         [Pretty.str "declared by gd_decl, not yet defined: ",
          Pretty.str (case pending context of [] => "(none)" | cs => commas (map base cs))]]
  end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_gd_defs\<close>
    "print gd_def definitions, fuel versions, approximation axioms and grounding lemmas"
    (Scan.succeed (Toplevel.keep (Pretty.writeln o pretty o Toplevel.context_of)));

end;
