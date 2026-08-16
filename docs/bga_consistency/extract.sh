#!/usr/bin/env bash
# Regenerates snippets/ from the theory sources.  See README.md.
#   usage: bash extract.sh [path-to-pure-dir]     (default ../../pure)
# Start/end patterns are matched against the raw sources, so they are written
# with Isabelle's ASCII escapes rather than with Unicode.
set -uo pipefail

PURE="${1:-../../pure}"
OUT="snippets"
FAIL=0
mkdir -p "$OUT"

unesc() {
  sed -e 's/\r$//' \
      -e 's/\\<Longrightarrow>/⟹/g'      -e 's/\\<Rightarrow>/⇒/g' \
      -e 's/\\<Longleftarrow>/⟸/g'      -e 's/\\<longleftrightarrow>/⟷/g' \
      -e 's/\\<longrightarrow>/⟶/g'     -e 's/\\<lbrakk>/⟦/g' \
      -e 's/\\<rbrakk>/⟧/g'             -e 's/\\<open>/‹/g' \
      -e 's/\\<close>/›/g'              -e 's/\\<And>/⋀/g' \
      -e 's/\\<forall>/∀/g'             -e 's/\\<exists>/∃/g' \
      -e 's/\\<lambda>/λ/g'             -e 's/\\<equiv>/≡/g' \
      -e 's/\\<noteq>/≠/g'              -e 's/\\<not>/¬/g' \
      -e 's/\\<and>/∧/g'                -e 's/\\<or>/∨/g' \
      -e 's/\\<le>/≤/g'                 -e 's/\\<ge>/≥/g' \
      -e 's/\\<langle>/⟨/g'             -e 's/\\<rangle>/⟩/g' \
      -e 's/\\<triangleright>/▹/g'      -e 's/\\<tturnstile>/⊩/g' \
      -e 's/\\<turnstile>/⊢/g'          -e 's/\\<in>/∈/g' \
      -e 's/\\<emptyset>/∅/g'           -e 's/\\<Down>/⇓/g' \
      -e 's/\\<mapsto>/↦/g'             -e 's/\\<rightarrow>/→/g' \
      -e 's/\\<phi>/φ/g'                -e 's/\\<Gamma>/Γ/g'
}

# span FILE START_RE END_RE NAME [SKIP]
#   inclusive span; SKIP says how many earlier START matches to ignore
#   (needed where a name occurs both in the dead bga_full block and in
#   the live bga_fuller one).
span() {
  local f="$1" a="$2" b="$3" n="$4" skip="${5:-0}" i
  local src; src=$(cat "$PURE/$f")
  for ((i = 0; i < skip; i++)); do
    src=$(printf '%s\n' "$src" | sed "1,/$a/d")
  done
  # first pass: from the first START match to EOF; second pass: up to the
  # first END match.  (A single /a/,/b/ range would restart on later matches.)
  printf '%s\n' "$src" | sed -n "/$a/,\$p" | sed -n "1,/$b/p" | unesc > "$OUT/$n.thy"
  if [ ! -s "$OUT/$n.thy" ]; then
    echo "!! EMPTY: $n  ($f  /$a/,/$b/)" >&2; FAIL=1; return 0
  fi
  local l; l=$(wc -l < "$OUT/$n.thy")
  if [ "$l" -gt 120 ]; then echo "!! RUNAWAY ($l lines): $n" >&2; FAIL=1; fi
  printf '  %-26s %4s lines\n' "$n" "$l"
}

# lines FILE FIRST LAST NAME
lines() {
  local f="$1" a="$2" b="$3" n="$4"
  sed -n "${a},${b}p" "$PURE/$f" | unesc > "$OUT/$n.thy"
  printf '  %-26s %4s lines\n' "$n" "$(wc -l < "$OUT/$n.thy")"
}

echo "GD.thy:"
span GD.thy '^typedecl o'                     '^  exF:'                        gd-prop
span GD.thy '^  eq :: '                       '^  eq_reflection'               gd-eq
span GD.thy '^definition neq'                 '^  where .*longleftrightarrow'  gd-defs
span GD.thy '^  zero :: '                     '^ *"..lbrakk>a N; Q zero'       gd-nat
span GD.thy '^definition True'                '^  where .*False .*equiv'       gd-truefalse
span GD.thy '^  entails :: '                  '^  entailsE:'                   gd-entails
span GD.thy '^  forall :: '                   '^  existsE:'                    gd-quant
span GD.thy '^  cond :: '                     '^  cond_elseQ_I:'               gd-cond
span GD.thy '^  def :: '                      '^  defI:'                       gd-def
span GD.thy '^  add   :: '                    '^  omega_def:'                  gd-arith
span GD.thy '^axiomatization cpair'           '^ *else cpair x P(y)'           gd-cpair
span GD.thy '^  cpx :: '                      '^ *else S(cpy (P x))"'          gd-cpxcpy
span GD.thy "^  cpi' :: "                     "^ *else cpy (cpi' (n-1) x)"     gd-cpi
span GD.thy '^type_synonym List'              '^  "list_tl x .*cpy (P x)"'     gd-list
span GD.thy '^axiomatization mem'             '^ *else mem x (list_tl G)"'     gd-mem
span GD.thy '^axiomatization nth'             '^ *else nth (i - 1)'            gd-nth
span GD.thy '^axiomatization len'             '^  len_def:'                    gd-len
span GD.thy '^axiomatization subset'          '^ *else mem (list_hd'           gd-subset
span GD.thy '^lemma strong_induction'         '^  shows "a N '                 gd-strong-induction
span GD.thy '^lemma list_induct'              '^  "a N .*Q Nil'                gd-list-induct
span GD.thy '^lemma cpair_surjective'         '^  shows  "..exists>b c'       gd-cpair-surj
span GD.thy '^lemma cpair_inj:'               '^  shows "a N '                 gd-cpair-inj
span GD.thy '^lemma cpx_proj'                 '^lemma cpy_proj'                gd-cpair-proj
span GD.thy '^lemma cpy_mono'                 '^lemma cpx_mono'                gd-cp-mono

echo "BGA_on_GA.thy:"
span BGA_on_GA.thy '^type_synonym tm'         '^  where "f .*Cons f G"'        bga-types
span BGA_on_GA.thy '^locale suff_syntax'      '^  assumes proof_bool'          bga-suff-syntax
span BGA_on_GA.thy '^locale suff_semantics'   'evals b A y; x .*R"' bga-suff-semantics
span BGA_on_GA.thy '^locale consistent'       '^  shows " ..not> (is_valid_proof p1' bga-consistent
span BGA_on_GA.thy '^  abbreviation T_VAR'    '^  abbreviation F_NEQ'          bga-tags
span BGA_on_GA.thy '^locale bga_encoding' '^  assumes fresh_H_def'   bga-enc-fixes
span BGA_on_GA.thy '^  assumes pack_F_N'      '^  assumes mono_pack_F'         bga-enc-axioms
span BGA_on_GA.thy '^locale bga_dfns'         '^  assumes dfn_is_def'          bga-dfns
span BGA_on_GA.thy '^  assumes eval_def:'     '^ *else 0)"\r\?$'                   bga-eval
span BGA_on_GA.thy '^locale bga_fuel_semantics' '^ *P (eval_fuel (P k) (conc_of (conc_of (load_T t))) A) .*Nil)"' bga-eval-fuel
span BGA_on_GA.thy '^definition evals ::'     '^  "evals t A r '               bga-evals
span BGA_on_GA.thy '^definition sat ::'       '^  "sat_hyp G A '               bga-sat
span BGA_on_GA.thy '^definition sat_fuel'     '^  "sat_fuel f A '              bga-sat-fuel
span BGA_on_GA.thy '^definition sat_hyp_fuel' '^  "sat_hyp_fuel G A '          bga-sat-hyp-fuel
span BGA_on_GA.thy '^locale bga_subst ='      '^ *subst_body (cpy (cpy (load_T b))) x y'  bga-subst
span BGA_on_GA.thy '^  fixes asn_put'         '^ *else list_hd A .*asn_put (list_tl A)'   bga-asn-put
span BGA_on_GA.thy '^  fixes check_template'  '^    else False"\r\?$'              bga-check-template
span BGA_on_GA.thy '^  fixes rep_vars_T'      '^ *rep_vars_T (cpy (cpy (load_T t))) i'    bga-rep-vars-t
span BGA_on_GA.thy '^  fixes find_phi'        '^    else find_phi J a b (list_tl ptr)"'   bga-find-phi
span BGA_on_GA.thy '^  fixes find_eq'         '^assumes check_subst_def'       bga-find-eq
span BGA_on_GA.thy '^  fixes check_eq_rules'  '^    else False"\r\?$'              bga-eq-rules
span BGA_on_GA.thy '^  fixes check_neq_rules' '^    else False"\r\?$'              bga-neq-rules
span BGA_on_GA.thy '^fixes check_ind_template' '^    else False"\r\?$'             bga-ind-template
span BGA_on_GA.thy '^  fixes check_ind  '     '^    else False"\r\?$'              bga-check-ind
span BGA_on_GA.thy '^locale bga_struct_rule'  '^  assumes check_struct_def'    bga-struct
span BGA_on_GA.thy '^fixes app_try'           '^  assumes check_app_def'       bga-app
span BGA_on_GA.thy '^fixes valid_step'        '^ *(tag_T (cpx (load_F (conc_of J)))) (tag_T (cpy (load_F (conc_of J)))) rest"' bga-valid-step
span BGA_on_GA.thy '^fixes check_list'        '^    else False"\r\?$'              bga-check-list
span BGA_on_GA.thy '^assumes is_valid_proof_def' '^    else False"\r\?$'           bga-is-valid-proof
span BGA_on_GA.thy "^sublocale consistent mk_eq mk_neq dfns is_valid_proof evals sat_fuel sat_hyp_fuel" '^    by (rule soundness_bridge_fuel)\r\?$'  bga-sublocale

echo "encode.thy:"
span encode.thy '^definition swap01'   '^definition pack_F'             enc-encoders
span encode.thy '^lemma swap01_0'      '^  done\r\?$'                       enc-swap01
span encode.thy '^axiomatization\r\?$'     '^  asn_put            ::'       enc-signature
span encode.thy '^  eval_def:'         '^ *else 0)" and\r\?$'               enc-eval
span encode.thy '^  asn_put_def:'      '^ *else list_hd A .*asn_put (list_tl A)'  enc-asn-put
span encode.thy '^lemma pack_F_N'      '^  unfolding load_T_def by (rule cpy_terminates\[OF t\])\r\?$'  enc-hq
span encode.thy '^lemma tag_pack_F'    '^lemma pack_tag_F'              enc-roundtrip
span encode.thy '^lemma decrease_F'    '^  unfolding tag_T_def by simp\r\?$' enc-decrease
span encode.thy '^lemma mono_pack_T'   '^  unfolding pack_F_def by (rule pair_mono_2\[OF tg x y h\])\r\?$' enc-mono
span encode.thy '^interpretation conc2' '^  done\r\?$'                      enc-interpretation
span encode.thy '^theorem BGA_syntactically_consistent' '^  using assms by (rule conc2.syntactically_consistent)\r\?$' enc-theorem

echo "BGA_on_GA.thy (proof):"
span BGA_on_GA.thy '^lemma eval_fuel_success_add'   '^  shows "eval_fuel (k + n) t A'   bga-fuel-add
span BGA_on_GA.thy '^lemma eval_fuel_success_unique:' '^  shows "r = q"'                 bga-fuel-unique
span BGA_on_GA.thy '^lemma evals_functional'        '^  shows "r = q"'                   bga-evals-functional
span BGA_on_GA.thy '^lemma sat_fuel_subst_FD'      '^  shows "sat_fuel f (asn_put A i v)"'  bga-subst-down
span BGA_on_GA.thy '^lemma sat_fuel_subst_FI'      '^  shows "sat_fuel (subst_F f i s) A"'  bga-subst-up
span BGA_on_GA.thy '^lemma template_instance_sound_fuel' '^  shows "sat_fuel f A"'       bga-template-sound
span BGA_on_GA.thy '^lemma find_phi_sound_fuel'     '^  shows "sat_fuel (conc_of J) A"'  bga-find-phi-sound
span BGA_on_GA.thy '^lemma nat_ind_sound_put_fuel'  '^  shows "sat_fuel (subst_F p i a) A"' bga-nat-ind-sound
span BGA_on_GA.thy '^lemma valid_step_sound_fuel'   '^  shows "sat_fuel (conc_of J) A"'  bga-valid-step-sound
span BGA_on_GA.thy '^lemma check_list_induct_N'     '^ \{16\}sat_hyp (hyp_of J) A .*sat (conc_of J) A"' bga-check-list-induct 1
span BGA_on_GA.thy '^lemma check_list_sound_fuel_N' '^    sat_fuel (conc_of J) A"'       bga-check-list-sound
span BGA_on_GA.thy '^lemma soundness_bridge_fuel'   '^  shows "sat_fuel (conc_of J) A"'  bga-bridge
span BGA_on_GA.thy '^definition mk_eq ::'           '^    "mk_neq a b .*pack_F 1'        bga-mk-eq 1
span BGA_on_GA.thy '^lemma sat_fuel_mk_eqE'         '^  obtains q where'                 bga-sat-eqE
span BGA_on_GA.thy '^lemma sat_fuel_mk_neqE'        '^  obtains x y where'               bga-sat-neqE

if [ "$FAIL" -ne 0 ]; then echo "FAILED (see !! above)"; exit 1; fi
echo "done."
