(*  Title:      gd2/gd_induct.ML

The induct and cases methods, ported from pure/gd_induct.ML and
pure/gd_cases.ML.

  induct t [arbitrary: y z]
                    the first [induct] rule whose first premise, instantiated
                    with t, is a chained fact or an assumption (e.g.
                    list_induct for a fact  t L,  data_induct for  t D);
                    otherwise rule ind
  induct t rule: r  the given rule (its first variable is the subject)
  induct strong t   rule strong_induction  (cases HQ Base Step)
  induct less t     rule less_induct       (cases HQ Step)
  cases t           an applicable [cases] rule, else nat_cases_rule
                    (cases HQ Zero Suc)
  cases bool: p     case split on a decided formula p (cases_bool)

The term t is substituted for the subject variable ?a of the rule.  Chained
facts that mention t (or a variable in arbitrary:) become premises of the goal
first, so they are part of the motive (the fact t N itself is used for the HQ
premise instead).  Without arbitrary, the motive ?Q is found by higher-order
unification with the goal, so every occurrence of t is abstracted.  With
arbitrary: y z the motive is  \<lambda>t. \<And>y z. goal,  built explicitly, so the
induction hypothesis holds for all y z.

Chained facts that mention neither become extra last premises of every case,
so that the cases keep the rule's numbering (Step(1), Step(2), ...) and the
simp/auto solver can use them.  The first subgoal (t N) is closed by a chained
fact or an assumption, or for cases also by auto, when possible.
*)

structure GD_Induct =
struct

datatype kind = Plain | Strong | Less;

fun try_inst ctxt t th =
  try (Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt t)]) th;

(*the subject premise of a rule instantiated with t (its first premise)*)
fun subject_prem ctxt t th =
  (case try_inst ctxt t th of
    SOME th' => (case Thm.prems_of th' of p :: _ => SOME p | [] => NONE)
  | NONE => NONE);

(*first rule of the named collection whose subject premise (instantiated with
  t) is a chained fact or an assumption of the goal, else the default*)
fun select_rule ctxt facts collection default t i st =
  let
    val hyps = map Thm.prop_of facts @ Logic.strip_assums_hyp (Logic.get_goal (Thm.prop_of st) i);
    fun ok th =
      (case subject_prem ctxt t th of
        SOME p => if exists (fn h => h aconv p) hyps then SOME th else NONE
      | NONE => NONE);
  in the_default default (get_first ok (Named_Theorems.get ctxt collection)) end;

fun apply_tac tac st =
  (case Seq.pull (DETERM tac st) of
    SOME (st', _) => st'
  | NONE => raise THM ("gd induct/cases: rule does not apply", 0, [st]));

fun mentions ts th = exists (fn t => Term.exists_subterm (fn u => u aconv t) (Thm.prop_of th)) ts;

fun is_nat_fact t th =
  (case Thm.prop_of th of
    Const (@{const_name GD_Core.Trueprop}, _) $ (Const (@{const_name GD_Core.isNat}, _) $ u) =>
      u aconv t
  | _ => false);

fun insert_context_facts ctxt facts j =
  if null facts then all_tac
  else Method.insert_tac ctxt facts j;   (*appended as last premises*)

(*The rule instantiated with  ?a := t  and  ?Q := \<lambda>t. \<And>ys. facts \<Longrightarrow> goal,
  and then specialised back to the current ys and facts, so that its
  conclusion is the goal itself.  The induction hypothesis and every case keep
  the facts as premises, generalised over t and ys.*)
fun generalized_rule ctxt th t ys facts goal =
  let
    val cert = Thm.cterm_of ctxt;
    val vars = Term.add_vars (Thm.prop_of th) [];
    fun var name =
      (case find_first (fn ((x, _), _) => x = name) vars of
        SOME v => v
      | NONE => error ("induct: the rule has no variable ?" ^ name));
    val (qv, _) = var "Q" and (av, _) = var "a";
    val G = Logic.list_implies (map Thm.prop_of facts, goal);
    val Q = Term.lambda t (fold_rev Logic.all ys G);
    val th1 = Drule.infer_instantiate ctxt [(qv, cert Q), (av, cert t)] th;
    val th2 = Conv.fconv_rule (Thm.beta_conversion true) th1;
    val cprems = take (Thm.nprems_of th) (Drule.strip_imp_prems (Thm.cprop_of th2));
    val concl = fold (fn ct => fn th => Thm.implies_elim th (Thm.assume ct)) cprems th2;
    val concl' = fold (fn f => fn th => Thm.implies_elim th f) facts
      (Drule.forall_elim_list (map cert ys) concl);
  in (fold_rev Thm.implies_intr cprems concl', length cprems) end;

(*generalize: the rule is an induction rule with motive ?Q and subject ?a
  (induct); otherwise a case rule, whose facts are simply added to every case
  after the rule's own premises (Zero(1) is  t = 0  however many facts there are)*)
fun rule_tac generalize select post facts t ys =
  CONTEXT_SUBGOAL (fn (goal, i) => fn (ctxt, st) =>
    let
      val th = select ctxt facts i st;
      val is_subject_fact =
        (case subject_prem ctxt t th of
          SOME p => (fn f => Thm.prop_of f aconv p)
        | NONE => is_nat_fact t);
      val (goal_facts, ctx_facts) =
        if generalize then
          (filter (fn f => mentions (t :: ys) f andalso not (is_subject_fact f)) facts,
           filter_out (mentions (t :: ys)) facts)
        else ([], filter_out is_subject_fact facts);
      val plain = not generalize orelse (null ys andalso null goal_facts);
      val st0 = st;
      val tac =
        if plain then
          (case try_inst ctxt t th of
            SOME th' => DETERM (match_tac ctxt [th'] i)
          | NONE => no_tac)
        else
          let val (rule, n) = generalized_rule ctxt th t ys goal_facts goal
          in compose_tac ctxt (false, rule, n) i THEN ALLGOALS (TRY o Goal.norm_hhf_tac ctxt) end;
      val st' = apply_tac tac st0;
      val new_goals = i upto (i + Thm.nprems_of st' - Thm.nprems_of st0);
      val st'' = apply_tac (EVERY (map (insert_context_facts ctxt ctx_facts) (rev new_goals))) st';
      val (spec, _) = Rule_Cases.get th;
      val cases = Rule_Cases.make_common ctxt (Thm.prop_of (Rule_Cases.internalize_params st'')) spec;
    in CONTEXT_CASES cases (TRY (post ctxt facts i)) (ctxt, st'') end);

fun induct_tac kind rule facts t ys =
  let
    fun select ctxt facts i st =
      (case (rule, kind) of
        (SOME th, _) => th
      | (NONE, Plain) => select_rule ctxt facts @{named_theorems induct} @{thm ind} t i st
      | (NONE, Strong) => Proof_Context.get_thm ctxt "strong_induction"
      | (NONE, Less) => Proof_Context.get_thm ctxt "less_induct");
    fun post ctxt facts = SOLVED' (assume_tac ctxt ORELSE' resolve_tac ctxt facts);
  in rule_tac true select post facts t ys end;

fun cases_tac facts t =
  let
    fun select ctxt facts i st =
      select_rule ctxt facts @{named_theorems cases} @{thm nat_cases_rule} t i st;
    fun post ctxt facts =
      SOLVED' (assume_tac ctxt ORELSE' resolve_tac ctxt facts)
      ORELSE' SOLVED' (GDAuto.gd_auto_tac ctxt);
  in rule_tac false select post facts t [] end;

fun bool_cases_tac ctxt p =
  (case try_inst ctxt p @{thm cases_bool} of
    SOME th => resolve_tac ctxt [th]
  | NONE => K no_tac);

end;

val _ =
  Theory.setup
    (Method.setup @{binding induct}
      (Scan.lift (Scan.optional
          (Args.$$$ "strong" >> K GD_Induct.Strong || Args.$$$ "less" >> K GD_Induct.Less)
          GD_Induct.Plain)
        -- Args.term
        -- Scan.optional (Scan.lift (Args.$$$ "arbitrary" -- Args.colon) |-- Scan.repeat1 Args.term) []
        -- Scan.option (Scan.lift (Args.$$$ "rule" -- Args.colon) |-- Attrib.thm)
        >> (fn (((kind, t), ys), rule) => fn _ =>
          Method.CONTEXT_METHOD (fn facts => GD_Induct.induct_tac kind rule facts t ys 1)))
      "induction on a natural number (ind, strong_induction, less_induct, or an [induct] rule)" #>
     Method.setup @{binding cases}
      ((Scan.lift (Args.$$$ "bool" -- Args.colon) |-- Args.term >> (fn p => fn ctxt =>
          SIMPLE_METHOD' (GD_Induct.bool_cases_tac ctxt p)))
       || (Args.term >> (fn t => fn _ =>
          Method.CONTEXT_METHOD (fn facts => GD_Induct.cases_tac facts t 1))))
      "case analysis on a natural number or a decided formula");
