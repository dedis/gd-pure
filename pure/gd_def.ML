(*  Title:      pure/gd_def.ML
    Author:     Omar Muhammad

The gd_def command: recursive definitions in GD via the := mechanism of
GD.thy, in place of a hand-written axiomatization block.  Names the axiom
<const>_def, and keeps a registry pairing each definition with its grounding
lemma, attached later with [grounded_by] and listed by print_gd_defs.

No proof obligation: GD is a language of arbitrary recursion, and whether
"f a N" holds is an ordinary theorem.
*)

signature GD_DEF =
sig
  type entry = {def_thm: thm, grounding: thm list}
  val get: Context.generic -> entry Symtab.table
  val lookup: Context.generic -> string -> entry option
  val pretty: Proof.context -> Pretty.T
end;

structure GD_Def: GD_DEF =
struct

(* registry *)

type entry = {def_thm: thm, grounding: thm list};

structure Data = Generic_Data
(
  type T = entry Symtab.table;
  val empty = Symtab.empty;
  val merge =
    Symtab.join (fn _ => fn (e1: entry, e2: entry) =>
      {def_thm = #def_thm e1,
       grounding = Library.merge Thm.eq_thm_prop (#grounding e1, #grounding e2)});
);

val get = Data.get;
fun lookup context name = Symtab.lookup (Data.get context) name;

fun register_def cname th =
  Data.map (Symtab.update (cname, {def_thm = th, grounding = []}));

fun add_grounding cname th =
  Data.map (fn tab =>
    (case Symtab.lookup tab cname of
      NONE =>
        error ("grounded_by: " ^ quote cname ^ " was not introduced by gd_def")
    | SOME e =>
        Symtab.update (cname,
          {def_thm = #def_thm e,
           grounding = Library.insert Thm.eq_thm_prop th (#grounding e)}) tab));

(* the command *)

(*Recognise  Trueprop (lhs := rhs)  under whatever Pure quantifiers and
  premises the axiomatization closed over, to find the constant defined.*)
fun defined_const prop =
  (case Logic.strip_assums_concl (Term.strip_all_body prop) of
    Const (@{const_name GD.Trueprop}, _) $
      (Const (@{const_name GD.def}, _) $ lhs $ _) =>
        (case Term.head_of lhs of
          Const (cname, _) => SOME cname
        | _ => NONE)
  | _ => NONE);

(*Default the axiom name to <const>_def: the convention used throughout
  GD.thy, and the one unfold_def / fold_def expect, since they look a
  theorem up by name.*)
fun default_names decls specs =
  (case decls of
    (cb, _, _) :: _ =>
      map_index (fn (i, ((b, atts), s)) =>
        if i = 0 andalso Binding.is_empty b
        then ((Binding.suffix_name "_def" cb, atts), s)
        else ((b, atts), s)) specs
  | [] => specs);

(*Each equation must define one of the constants this block declares.
  Without the check, gd_def is a general axiom-asserting command: the body is
  unconstrained, so

    gd_def bogus :: "num => num" where "add x y := 0"

  quietly adds a second := axiom for the existing GD.add, and S 0 + S 0 = 0
  becomes provable.*)
fun gd_def_cmd raw_decls raw_specs thy =
  let
    val specs = default_names raw_decls raw_specs;
    val ((consts, thms), thy') =
      Specification.axiomatization_cmd raw_decls [] [] specs thy;

    val declared = map (fn t => dest_Const_name t) consts;

    fun check ((b, _), _) th =
      (case defined_const (Thm.prop_of th) of
        NONE =>
          error (Binding.print b ^ " is not of the form  <constant> := <body>")
      | SOME cname =>
          if member (op =) declared cname then cname
          else
            error (Binding.print b ^ " defines " ^
              quote (Long_Name.base_name cname) ^
              ", which this gd_def does not declare.\ngd_def defines the \
              \constants it introduces; use axiomatization for anything else."));

    val defined = map2 check specs thms;

    val _ =
      (case subtract (op =) defined declared of
        [] => ()
      | missing =>
          error ("declared with no defining equation: " ^
            commas_quote (map Long_Name.base_name missing)));

    (*:= is not pattern matching.  Two equations for one constant make both
      bodies interchangeable with the left-hand side, hence with each other:
      "f 0 := 0" with "f 0 := S 0" proves S 0 = 0.*)
    val _ =
      (case duplicates (op =) defined of
        [] => ()
      | dups =>
          error ("more than one defining equation for: " ^
            commas_quote (map Long_Name.base_name dups) ^
            "\nUse a single equation with if/then/else."));
  in
    fold (fn (cname, th) => Context.theory_map (register_def cname th))
      (defined ~~ thms) thy'
  end;

val spec_list = Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Parse.prop);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>gd_def\<close>
    "GD recursive definition via :="
    (Parse.vars -- (Parse.where_ |-- Parse.!!! spec_list)
      >> (fn (decls, specs) => Toplevel.theory (gd_def_cmd decls specs)));

(* [grounded_by] and print_gd_defs *)

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>grounded_by\<close>
      (Args.const {proper = true, strict = false} >> (fn cname =>
        Thm.declaration_attribute (fn th => add_grounding cname th)))
      "attach a grounding lemma to a gd_def constant");

fun pretty_entry ctxt (name, {def_thm, grounding}) =
  Pretty.chunks
    [Pretty.block [Pretty.str (Long_Name.base_name name), Pretty.str ":"],
     Pretty.indent 4 (Thm.pretty_thm ctxt def_thm),
     Pretty.indent 4
       (case grounding of
          [] => Pretty.str "grounded_by: (none)"
        | ths =>
            Pretty.block
              (Pretty.str "grounded_by: " ::
                Pretty.commas (map (Thm.pretty_thm ctxt) ths)))];

fun pretty ctxt =
  Pretty.big_list "gd_def definitions:"
    (map (pretty_entry ctxt) (Symtab.dest (get (Context.Proof ctxt))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_gd_defs\<close>
    "print gd_def definitions and their grounding lemmas"
    (Scan.succeed (Toplevel.keep (Pretty.writeln o pretty o Toplevel.context_of)));

end;
