(* gd_cases.ML *)

datatype input = BoolCaseTac of term | InductCaseTac of term

structure GDCases =
struct

val nat_cases_thm = @{thm cases_nat_2}

fun apply_tac tac st =
  let
    val res = DETERM tac st
  in
    case Seq.pull res of
      SOME (st', _) => st'
    | NONE => raise THM ("tactic failed", 0, [st])
  end

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

fun select_cases_thm ctxt t i st =
  let
    val cases_thms = Named_Theorems.get ctxt @{named_theorems cases}
    fun is_instantiable th =
      case (try_inst_thm ctxt t th) of
        NONE     => NONE
      | SOME th' => if (closes_first_prem ctxt i th' st) then SOME th else NONE
  in
    case (get_first is_instantiable cases_thms) of
      SOME th => th
    | NONE    => nat_cases_thm
  end

fun gd_inductive_cases_tac t =
  CONTEXT_SUBGOAL (fn (_, i) => fn (ctxt, st) =>
  let
    val th  = select_cases_thm ctxt t i st
    val tac =
      case (try_inst_thm ctxt t th) of
        SOME th'' => DETERM (match_tac ctxt [th''] i)
      | NONE      => no_tac
    val st' = apply_tac tac st
    val (spec, _) = Rule_Cases.get th
    val cases_prop = Thm.prop_of (Rule_Cases.internalize_params st')
    val cases = Rule_Cases.make_common ctxt cases_prop spec
    val post_tac = TRY ((SOLVED' (assume_tac ctxt) ORELSE' SOLVED' (GDAuto.gd_auto_tac ctxt)) i)
  in
    CONTEXT_CASES cases post_tac (ctxt, st')
  end)

fun gd_bool_cases_tac ctxt x =
  case (try_inst_thm ctxt x @{thm cases_bool}) of
    SOME th => resolve_tac ctxt [th]
  | NONE    => K no_tac

fun gd_cases_tac ctxt input =
  case input of
    BoolCaseTac t   => SIMPLE_METHOD' (gd_bool_cases_tac ctxt t)
  | InductCaseTac t => Method.CONTEXT_METHOD (K (gd_inductive_cases_tac t 1))

val parse_cases_args : input context_parser =
  (Scan.lift (Args.$$$ "bool" |-- Args.colon) |-- Args.term >> BoolCaseTac)
  || (Args.term >> InductCaseTac)

val _ =
  Theory.setup
    (Method.setup @{binding cases}
      (parse_cases_args >> (fn inp => fn ctxt => gd_cases_tac ctxt inp))
      "case analysis")

end
