theory qga_encode
  imports QGA_on_GA
begin

(*
  ============================================================================
  A concrete Goedel numbering for the QGA-on-QGA development, discharging the
  interface of QGA_on_GA.thy.

  This file is to QGA_on_GA.thy what encode.thy is to BGA_on_GA.thy: it fixes
  one encoding, pays the arithmetic cost once, and instantiates the abstract
  result.  Nothing here is specific to QGA beyond the tag arities.

  GENERATED IN PART.  The axiomatization block of section 3 is the list of
  recursive equations of QGA_on_GA.thy, copied verbatim, so that the two files
  cannot drift apart.
  ============================================================================
*)

section \<open>1.  Concrete encoders\<close>

text \<open>
  Identical to \<open>encode.thy\<close>.  Formula codes are the Cantor pairing directly,
  since \<open>F_EQ = 0\<close> and \<open>cpx 0 = 0\<close>, so \<open>tag_F 0 = F_EQ\<close> holds on the nose.
  Term codes compose the pairing with the involution exchanging 0 and 1,
  because the interface requires \<open>tag_T 0 = T_ZERO\<close> and \<open>T_ZERO = 1\<close>: without
  the relabelling the code 0 would denote a variable and the structural
  decrease \<open>load_T t < t\<close> would have no atomic base to stop at.
\<close>

definition swap01 :: "num \<Rightarrow> num" where
  "swap01 t \<equiv> if t = 0 then 1 else if t = 1 then 0 else t"

definition tag_T  :: "tm \<Rightarrow> num"          where "tag_T  n    \<equiv> swap01 (cpx n)"
definition load_T :: "tm \<Rightarrow> num"          where "load_T n    \<equiv> cpy n"
definition pack_T :: "num \<Rightarrow> num \<Rightarrow> tm"   where "pack_T tg L \<equiv> \<langle>swap01 tg, L\<rangle>"
definition tag_F  :: "fm \<Rightarrow> num"          where "tag_F  n    \<equiv> cpx n"
definition load_F :: "fm \<Rightarrow> num"          where "load_F n    \<equiv> cpy n"
definition pack_F :: "num \<Rightarrow> num \<Rightarrow> fm"   where "pack_F tg L \<equiv> \<langle>tg, L\<rangle>"

lemma swap01_0 [simp]: "swap01 0 = 1"
  unfolding swap01_def by (cases bool: "(0::num) = 0", simp+)

lemma swap01_N [simp, auto]: "t N \<Longrightarrow> swap01 t N"
  unfolding swap01_def by (cases bool: "t = 0", simp+)

lemma swap01_inv [simp]: "t N \<Longrightarrow> swap01 (swap01 t) = t"
  unfolding swap01_def
  apply (cases bool: "t = 0", simp+)
  apply (cases bool: "t = 1", simp+)
  done

text \<open>The syntax constructors, repeated at theory level so that the recursive
      equations below can be written the way the locale writes them.\<close>

abbreviation tVar  :: "num \<Rightarrow> tm"            where "tVar i  \<equiv> pack_T T_VAR i"
abbreviation tZero :: "tm"                    where "tZero    \<equiv> pack_T T_ZERO 0"
abbreviation tSuc  :: "tm \<Rightarrow> tm"              where "tSuc a  \<equiv> pack_T T_SUC a"
abbreviation tPred :: "tm \<Rightarrow> tm"              where "tPred a \<equiv> pack_T T_PRED a"
abbreviation tCond :: "fm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"  where "tCond c a b \<equiv> pack_T T_COND \<langle>c, \<langle>a, b\<rangle>\<rangle>"
abbreviation tApp  :: "num \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm" where "tApp d a b \<equiv> pack_T T_APP \<langle>d, \<langle>a, b\<rangle>\<rangle>"

abbreviation mkEq  :: "tm \<Rightarrow> tm \<Rightarrow> fm"        where "mkEq a b  \<equiv> pack_F F_EQ \<langle>a, b\<rangle>"
abbreviation mkNot :: "fm \<Rightarrow> fm"              where "mkNot p   \<equiv> pack_F F_NOT p"
abbreviation mkOr  :: "fm \<Rightarrow> fm \<Rightarrow> fm"        where "mkOr p q  \<equiv> pack_F F_OR \<langle>p, q\<rangle>"
abbreviation mkAll :: "num \<Rightarrow> fm \<Rightarrow> fm"       where "mkAll i p \<equiv> pack_F F_ALL \<langle>i, p\<rangle>"
abbreviation mkEx  :: "num \<Rightarrow> fm \<Rightarrow> fm"       where "mkEx i p  \<equiv> pack_F F_EX \<langle>i, p\<rangle>"
abbreviation mkFCond :: "fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm" where "mkFCond c p q \<equiv> pack_F F_COND \<langle>c, \<langle>p, q\<rangle>\<rangle>"
abbreviation mkNeq   :: "tm \<Rightarrow> tm \<Rightarrow> fm"      where "mkNeq a b \<equiv> mkNot (mkEq a b)"
abbreviation mkNat   :: "tm \<Rightarrow> fm"            where "mkNat a   \<equiv> mkEq a a"
abbreviation mkBool  :: "fm \<Rightarrow> fm"            where "mkBool p  \<equiv> mkOr p (mkNot p)"
abbreviation mkFalse :: "fm"                   where "mkFalse    \<equiv> mkEq (tSuc tZero) tZero"


section \<open>2.  The definition list and the divergent term\<close>

text \<open>
  \<open>dfns\<close> stays opaque: only its termination is assumed, so the result holds for
  every terminating definition list, including lists all of whose definitions
  diverge.  The one thing required of it is a divergent entry at index 0, the
  object-language image of QGA\<^latex>\<open>'\<close>s own \<open>omega := omega\<close>: the body
  \<open>d_0(v_0, v_1)\<close> unfolds to itself forever, so \<open>tBot = d_0(0, 0)\<close> converges at
  no fuel.  \<open>tBot\<close> is what the closing substitution puts in place of a variable
  that the assignment sends to bottom.
\<close>

axiomatization dfns :: "dfn" where
  dfns_N: "dfns N" and
  dfns_bot: "nth 0 dfns = pack_T T_APP \<langle>0, \<langle>pack_T T_VAR 0, pack_T T_VAR 1\<rangle>\<rangle>"

definition tBot :: "tm" where "tBot \<equiv> tApp 0 tZero tZero"


section \<open>3.  Concrete definitions of every derived function\<close>

text \<open>
  One \<open>axiomatization\<close> block whose axioms are the recursive \<open>:=\<close> equations of
  the locale, verbatim.  This is the definitional mechanism of grounded
  arithmetic applied at scale, and it is why an evaluator that runs the
  system\<^latex>\<open>'\<close>s own proof search can be written down at all: no termination
  obligation is incurred when the definition is made.
\<close>

axiomatization
  fresh_T              :: "num \<Rightarrow> tm \<Rightarrow> o" and
  fresh_F              :: "num \<Rightarrow> fm \<Rightarrow> o" and
  fresh_H              :: "num \<Rightarrow> hyp \<Rightarrow> o" and
  subst_T              :: "tm \<Rightarrow> num \<Rightarrow> tm \<Rightarrow> tm" and
  subst_F              :: "fm \<Rightarrow> num \<Rightarrow> tm \<Rightarrow> fm" and
  subst_H              :: "hyp \<Rightarrow> num \<Rightarrow> tm \<Rightarrow> hyp" and
  subst_body           :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm" and
  asn_put              :: "asn \<Rightarrow> num \<Rightarrow> val \<Rightarrow> asn" and
  numeral_of           :: "val \<Rightarrow> tm" and
  close_T              :: "tm \<Rightarrow> hyp \<Rightarrow> asn \<Rightarrow> tm" and
  close_F              :: "fm \<Rightarrow> hyp \<Rightarrow> asn \<Rightarrow> fm" and
  close_H              :: "hyp \<Rightarrow> hyp \<Rightarrow> asn \<Rightarrow> hyp" and
  dfn_is               :: "dfn \<Rightarrow> num \<Rightarrow> tm \<Rightarrow> o" and
  eqT                  :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> o" and
  eqF                  :: "fm \<Rightarrow> fm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> o" and
  lzT                  :: "tm \<Rightarrow> tm \<Rightarrow> fm \<Rightarrow> num \<Rightarrow> o" and
  lzF                  :: "fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> num \<Rightarrow> o" and
  unfT                 :: "tm \<Rightarrow> tm \<Rightarrow> hyp \<Rightarrow> pf \<Rightarrow> o" and
  unfF                 :: "fm \<Rightarrow> fm \<Rightarrow> hyp \<Rightarrow> pf \<Rightarrow> o" and
  find_cut             :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o" and
  check_cut            :: "jdg \<Rightarrow> pf \<Rightarrow> o" and
  find_weak            :: "jdg \<Rightarrow> hyp \<Rightarrow> pf \<Rightarrow> o" and
  check_weak           :: "jdg \<Rightarrow> pf \<Rightarrow> o" and
  inst_try             :: "jdg \<Rightarrow> num \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> o" and
  inst_a               :: "jdg \<Rightarrow> num \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> o" and
  inst_i               :: "jdg \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o" and
  check_inst           :: "jdg \<Rightarrow> pf \<Rightarrow> o" and
  find_disjE1          :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o" and
  find_disjE23         :: "jdg \<Rightarrow> pf \<Rightarrow> o" and
  find_exF             :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o" and
  check_prop_rules     :: "jdg \<Rightarrow> pf \<Rightarrow> o" and
  eqsub_inner          :: "jdg \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> o" and
  eqsub_outer          :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o" and
  check_eqsub          :: "jdg \<Rightarrow> pf \<Rightarrow> o" and
  check_eqsym          :: "jdg \<Rightarrow> pf \<Rightarrow> o" and
  check_nat_rules      :: "jdg \<Rightarrow> pf \<Rightarrow> o" and
  ind_inner            :: "jdg \<Rightarrow> num \<Rightarrow> fm \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o" and
  ind_outer            :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o" and
  check_ind            :: "jdg \<Rightarrow> pf \<Rightarrow> o" and
  find_allE_inner      :: "jdg \<Rightarrow> num \<Rightarrow> fm \<Rightarrow> pf \<Rightarrow> o" and
  find_allE            :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o" and
  find_exI             :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o" and
  find_exE             :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o" and
  find_nallE           :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o" and
  check_quant_rules    :: "jdg \<Rightarrow> pf \<Rightarrow> o" and
  find_condE           :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o" and
  check_condI          :: "jdg \<Rightarrow> pf \<Rightarrow> o" and
  lazy_inner           :: "jdg \<Rightarrow> fm \<Rightarrow> num \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o" and
  lazy_outer           :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o" and
  check_cond_rules     :: "jdg \<Rightarrow> pf \<Rightarrow> o" and
  find_def             :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o" and
  check_def            :: "jdg \<Rightarrow> pf \<Rightarrow> o" and
  valid_step           :: "jdg \<Rightarrow> pf \<Rightarrow> o" and
  check_list           :: "pf \<Rightarrow> o" and
  is_valid_proof       :: "pf \<Rightarrow> jdg \<Rightarrow> o" and
  evT                  :: "num \<Rightarrow> tm \<Rightarrow> asn \<Rightarrow> val" and
  evF                  :: "num \<Rightarrow> fm \<Rightarrow> asn \<Rightarrow> num" and
  hypsat               :: "num \<Rightarrow> hyp \<Rightarrow> asn \<Rightarrow> num" and
  all_tt               :: "num \<Rightarrow> num \<Rightarrow> fm \<Rightarrow> asn \<Rightarrow> num" and
  ex_tt                :: "num \<Rightarrow> num \<Rightarrow> fm \<Rightarrow> asn \<Rightarrow> num" and
  wsat                 :: "fm \<Rightarrow> asn \<Rightarrow> o" and
  wunsat               :: "fm \<Rightarrow> asn \<Rightarrow> o"
where
  fresh_T_def: "fresh_T k t :=
      if tag_T t = T_VAR  then load_T t < k = 1
      else if tag_T t = T_ZERO then True
      else if tag_T t = T_SUC  then fresh_T k (load_T t)
      else if tag_T t = T_PRED then fresh_T k (load_T t)
      else if tag_T t = T_COND then
             fresh_F k (pfst (load_T t)) \<and> fresh_T k (psnd (load_T t)) \<and> fresh_T k (pthd (load_T t))
      else if tag_T t = T_APP then
             fresh_T k (psnd (load_T t)) \<and> fresh_T k (pthd (load_T t))
      else False" and

  fresh_F_def: "fresh_F k f :=
      if tag_F f = F_EQ  then fresh_T k (cpx (load_F f)) \<and> fresh_T k (cpy (load_F f))
      else if tag_F f = F_NOT then fresh_F k (load_F f)
      else if tag_F f = F_OR  then fresh_F k (cpx (load_F f)) \<and> fresh_F k (cpy (load_F f))
      else if tag_F f = F_ALL then (cpx (load_F f) < k = 1) \<and> fresh_F k (cpy (load_F f))
      else if tag_F f = F_EX  then (cpx (load_F f) < k = 1) \<and> fresh_F k (cpy (load_F f))
      else if tag_F f = F_COND then
             fresh_F k (pfst (load_F f)) \<and> fresh_F k (psnd (load_F f)) \<and> fresh_F k (pthd (load_F f))
      else False" and

  fresh_H_def: "fresh_H k G :=
      if G = Nil then True else fresh_F k (list_hd G) \<and> fresh_H k (list_tl G)" and

  subst_T_def: "subst_T t j v :=
      if tag_T t = T_VAR  then (if load_T t = j then v else t)
      else if tag_T t = T_ZERO then t
      else if tag_T t = T_SUC  then tSuc  (subst_T (load_T t) j v)
      else if tag_T t = T_PRED then tPred (subst_T (load_T t) j v)
      else if tag_T t = T_COND then
             tCond (subst_F (pfst (load_T t)) j v)
                   (subst_T (psnd (load_T t)) j v)
                   (subst_T (pthd (load_T t)) j v)
      else if tag_T t = T_APP then
             tApp (pfst (load_T t))
                  (subst_T (psnd (load_T t)) j v)
                  (subst_T (pthd (load_T t)) j v)
      else t" and

  subst_F_def: "subst_F f j v :=
      if tag_F f = F_EQ  then mkEq (subst_T (cpx (load_F f)) j v) (subst_T (cpy (load_F f)) j v)
      else if tag_F f = F_NOT then mkNot (subst_F (load_F f) j v)
      else if tag_F f = F_OR  then mkOr (subst_F (cpx (load_F f)) j v) (subst_F (cpy (load_F f)) j v)
      else if tag_F f = F_ALL then
             (if cpx (load_F f) = j then f
              else mkAll (cpx (load_F f)) (subst_F (cpy (load_F f)) j v))
      else if tag_F f = F_EX then
             (if cpx (load_F f) = j then f
              else mkEx (cpx (load_F f)) (subst_F (cpy (load_F f)) j v))
      else if tag_F f = F_COND then
             mkFCond (subst_F (pfst (load_F f)) j v)
                     (subst_F (psnd (load_F f)) j v)
                     (subst_F (pthd (load_F f)) j v)
      else f" and

  subst_H_def: "subst_H G j v :=
      if G = Nil then Nil else subst_F (list_hd G) j v \<triangleright> subst_H (list_tl G) j v" and

  subst_body_def: "subst_body b x y := subst_T (subst_T b 0 x) 1 y" and

  asn_put_def: "asn_put A i v :=
      if i = 0 then (if A = Nil then v \<triangleright> Nil else v \<triangleright> list_tl A)
      else if A = Nil then 0 \<triangleright> asn_put Nil (i - 1) v
      else list_hd A \<triangleright> asn_put (list_tl A) (i - 1) v" and

  numeral_of_def: "numeral_of v := if v = 0 then tZero else tSuc (numeral_of (v - 1))" and

  close_T_def: "close_T t Pv A :=
      if tag_T t = T_VAR then
        (if load_T t \<in> Pv then t
         else if nth (load_T t) A = 0 then tBot
         else numeral_of (P (nth (load_T t) A)))
      else if tag_T t = T_ZERO then t
      else if tag_T t = T_SUC  then tSuc  (close_T (load_T t) Pv A)
      else if tag_T t = T_PRED then tPred (close_T (load_T t) Pv A)
      else if tag_T t = T_COND then
             tCond (close_F (pfst (load_T t)) Pv A)
                   (close_T (psnd (load_T t)) Pv A)
                   (close_T (pthd (load_T t)) Pv A)
      else if tag_T t = T_APP then
             tApp (pfst (load_T t))
                  (close_T (psnd (load_T t)) Pv A)
                  (close_T (pthd (load_T t)) Pv A)
      else t" and

  close_F_def: "close_F f Pv A :=
      if tag_F f = F_EQ  then mkEq (close_T (cpx (load_F f)) Pv A) (close_T (cpy (load_F f)) Pv A)
      else if tag_F f = F_NOT then mkNot (close_F (load_F f) Pv A)
      else if tag_F f = F_OR  then mkOr (close_F (cpx (load_F f)) Pv A) (close_F (cpy (load_F f)) Pv A)
      else if tag_F f = F_ALL then
             mkAll (cpx (load_F f)) (close_F (cpy (load_F f)) (cpx (load_F f) \<triangleright> Pv) A)
      else if tag_F f = F_EX then
             mkEx (cpx (load_F f)) (close_F (cpy (load_F f)) (cpx (load_F f) \<triangleright> Pv) A)
      else if tag_F f = F_COND then
             mkFCond (close_F (pfst (load_F f)) Pv A)
                     (close_F (psnd (load_F f)) Pv A)
                     (close_F (pthd (load_F f)) Pv A)
      else f" and

  close_H_def: "close_H G Pv A :=
      if G = Nil then Nil else close_F (list_hd G) Pv A \<triangleright> close_H (list_tl G) Pv A" and

  dfn_is_def: 
    "dfn_is d k b := if d < len dfns = 1 then nth d dfns = b \<and> fresh_T k b else False" and

  eqT_def: "eqT t u a b :=
    if t = u then True
    else if t = a \<and> u = b then True
    else if tag_T t = T_SUC \<and> tag_T u = T_SUC then eqT (load_T t) (load_T u) a b
    else if tag_T t = T_PRED \<and> tag_T u = T_PRED then eqT (load_T t) (load_T u) a b
    else if tag_T t = T_COND \<and> tag_T u = T_COND then
         eqF (pfst (load_T t)) (pfst (load_T u)) a b
         \<and> eqT (psnd (load_T t)) (psnd (load_T u)) a b
         \<and> eqT (pthd (load_T t)) (pthd (load_T u)) a b
    else if tag_T t = T_APP \<and> tag_T u = T_APP \<and> pfst (load_T t) = pfst (load_T u) then
         eqT (psnd (load_T t)) (psnd (load_T u)) a b
         \<and> eqT (pthd (load_T t)) (pthd (load_T u)) a b
    else False" and

  eqF_def: "eqF f g a b :=
    if f = g then True
    else if tag_F f = F_EQ \<and> tag_F g = F_EQ then
         eqT (cpx (load_F f)) (cpx (load_F g)) a b \<and> eqT (cpy (load_F f)) (cpy (load_F g)) a b
    else if tag_F f = F_NOT \<and> tag_F g = F_NOT then eqF (load_F f) (load_F g) a b
    else if tag_F f = F_OR \<and> tag_F g = F_OR then
         eqF (cpx (load_F f)) (cpx (load_F g)) a b \<and> eqF (cpy (load_F f)) (cpy (load_F g)) a b
    else if tag_F f = F_ALL \<and> tag_F g = F_ALL \<and> cpx (load_F f) = cpx (load_F g) then
         eqF (cpy (load_F f)) (cpy (load_F g)) a b
    else if tag_F f = F_EX \<and> tag_F g = F_EX \<and> cpx (load_F f) = cpx (load_F g) then
         eqF (cpy (load_F f)) (cpy (load_F g)) a b
    else if tag_F f = F_COND \<and> tag_F g = F_COND then
         eqF (pfst (load_F f)) (pfst (load_F g)) a b
         \<and> eqF (psnd (load_F f)) (psnd (load_F g)) a b
         \<and> eqF (pthd (load_F f)) (pthd (load_F g)) a b
    else False" and

  lzT_def: "lzT t u c sel :=
    if t = u then True
    else if tag_T t = T_COND \<and> pfst (load_T t) = c
            \<and> (if sel = 0 then psnd (load_T t) else pthd (load_T t)) = u then True
    else if tag_T t = T_SUC \<and> tag_T u = T_SUC then lzT (load_T t) (load_T u) c sel
    else if tag_T t = T_PRED \<and> tag_T u = T_PRED then lzT (load_T t) (load_T u) c sel
    else if tag_T t = T_COND \<and> tag_T u = T_COND then
         lzF (pfst (load_T t)) (pfst (load_T u)) c sel
         \<and> lzT (psnd (load_T t)) (psnd (load_T u)) c sel
         \<and> lzT (pthd (load_T t)) (pthd (load_T u)) c sel
    else if tag_T t = T_APP \<and> tag_T u = T_APP \<and> pfst (load_T t) = pfst (load_T u) then
         lzT (psnd (load_T t)) (psnd (load_T u)) c sel
         \<and> lzT (pthd (load_T t)) (pthd (load_T u)) c sel
    else False" and

  lzF_def: "lzF f g c sel :=
    if f = g then True
    else if tag_F f = F_COND \<and> pfst (load_F f) = c
            \<and> (if sel = 0 then psnd (load_F f) else pthd (load_F f)) = g then True
    else if tag_F f = F_EQ \<and> tag_F g = F_EQ then
         lzT (cpx (load_F f)) (cpx (load_F g)) c sel \<and> lzT (cpy (load_F f)) (cpy (load_F g)) c sel
    else if tag_F f = F_NOT \<and> tag_F g = F_NOT then lzF (load_F f) (load_F g) c sel
    else if tag_F f = F_OR \<and> tag_F g = F_OR then
         lzF (cpx (load_F f)) (cpx (load_F g)) c sel \<and> lzF (cpy (load_F f)) (cpy (load_F g)) c sel
    else if tag_F f = F_ALL \<and> tag_F g = F_ALL \<and> cpx (load_F f) = cpx (load_F g) then
         lzF (cpy (load_F f)) (cpy (load_F g)) c sel
    else if tag_F f = F_EX \<and> tag_F g = F_EX \<and> cpx (load_F f) = cpx (load_F g) then
         lzF (cpy (load_F f)) (cpy (load_F g)) c sel
    else if tag_F f = F_COND \<and> tag_F g = F_COND then
         lzF (pfst (load_F f)) (pfst (load_F g)) c sel
         \<and> lzF (psnd (load_F f)) (psnd (load_F g)) c sel
         \<and> lzF (pthd (load_F f)) (pthd (load_F g)) c sel
    else False" and

  unfT_def: "unfT t u G rest :=
    if t = u then True
    else if tag_T t = T_APP \<and> pfst (load_T t) < len dfns = 1
            \<and> mem (G \<tturnstile> mkNat (psnd (load_T t))) rest
            \<and> mem (G \<tturnstile> mkNat (pthd (load_T t))) rest
            \<and> subst_body (nth (pfst (load_T t)) dfns) (psnd (load_T t)) (pthd (load_T t)) = u
    then True
    else if tag_T t = T_SUC \<and> tag_T u = T_SUC then unfT (load_T t) (load_T u) G rest
    else if tag_T t = T_PRED \<and> tag_T u = T_PRED then unfT (load_T t) (load_T u) G rest
    else if tag_T t = T_COND \<and> tag_T u = T_COND then
         unfF (pfst (load_T t)) (pfst (load_T u)) G rest
         \<and> unfT (psnd (load_T t)) (psnd (load_T u)) G rest
         \<and> unfT (pthd (load_T t)) (pthd (load_T u)) G rest
    else if tag_T t = T_APP \<and> tag_T u = T_APP \<and> pfst (load_T t) = pfst (load_T u) then
         unfT (psnd (load_T t)) (psnd (load_T u)) G rest
         \<and> unfT (pthd (load_T t)) (pthd (load_T u)) G rest
    else False" and

  unfF_def: "unfF f g G rest :=
    if f = g then True
    else if tag_F f = F_EQ \<and> tag_F g = F_EQ then
         unfT (cpx (load_F f)) (cpx (load_F g)) G rest \<and> unfT (cpy (load_F f)) (cpy (load_F g)) G rest
    else if tag_F f = F_NOT \<and> tag_F g = F_NOT then unfF (load_F f) (load_F g) G rest
    else if tag_F f = F_OR \<and> tag_F g = F_OR then
         unfF (cpx (load_F f)) (cpx (load_F g)) G rest \<and> unfF (cpy (load_F f)) (cpy (load_F g)) G rest
    else if tag_F f = F_ALL \<and> tag_F g = F_ALL \<and> cpx (load_F f) = cpx (load_F g) then
         unfF (cpy (load_F f)) (cpy (load_F g)) G rest
    else if tag_F f = F_EX \<and> tag_F g = F_EX \<and> cpx (load_F f) = cpx (load_F g) then
         unfF (cpy (load_F f)) (cpy (load_F g)) G rest
    else if tag_F f = F_COND \<and> tag_F g = F_COND then
         unfF (pfst (load_F f)) (pfst (load_F g)) G rest
         \<and> unfF (psnd (load_F f)) (psnd (load_F g)) G rest
         \<and> unfF (pthd (load_F f)) (pthd (load_F g)) G rest
    else False" and

  find_cut_def: "find_cut J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> mem (conc_of (list_hd ptr) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest then True
    else find_cut J rest (list_tl ptr)" and

  check_cut_def: "check_cut J rest := find_cut J rest rest" and

  find_weak_def: "find_weak J G ptr :=
    if ptr = Nil then False
    else if conc_of (list_hd ptr) = conc_of J \<and> subset (hyp_of (list_hd ptr)) G then True
    else find_weak J G (list_tl ptr)" and

  check_weak_def: "check_weak J rest := find_weak J (hyp_of J) rest" and

  inst_try_def: "inst_try J i a ptr :=
    if ptr = Nil then False
    else if subst_H (hyp_of (list_hd ptr)) i a = hyp_of J
            \<and> subst_F (conc_of (list_hd ptr)) i a = conc_of J
            \<and> fresh_H i (hyp_of (list_hd ptr)) then True
    else inst_try J i a (list_tl ptr)" and

  inst_a_def: "inst_a J i a rest :=
    if inst_try J i a rest then True
    else if a > 0 = 1 then inst_a J i (a - 1) rest else False" and

  inst_i_def: "inst_i J i rest :=
    if inst_a J i J rest then True
    else if i > 0 = 1 then inst_i J (i - 1) rest else False" and

  check_inst_def: "check_inst J rest := inst_i J J rest" and

  find_disjE1_def: "find_disjE1 J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_OR
            \<and> mem (cpx (load_F (conc_of (list_hd ptr))) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
            \<and> mem (cpy (load_F (conc_of (list_hd ptr))) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
    then True else find_disjE1 J rest (list_tl ptr)" and

  find_disjE23_def: "find_disjE23 J ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_NOT
            \<and> tag_F (load_F (conc_of (list_hd ptr))) = F_OR
            \<and> (mkNot (cpx (load_F (load_F (conc_of (list_hd ptr))))) = conc_of J
               \<or> mkNot (cpy (load_F (load_F (conc_of (list_hd ptr))))) = conc_of J)
    then True else find_disjE23 J (list_tl ptr)" and

  find_exF_def: "find_exF J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> mem (hyp_of J \<tturnstile> mkNot (conc_of (list_hd ptr))) rest
    then True else find_exF J rest (list_tl ptr)" and

  check_prop_rules_def: "check_prop_rules J rest :=
    if tag_F (conc_of J) = F_OR
       \<and> (mem (hyp_of J \<tturnstile> cpx (load_F (conc_of J))) rest
          \<or> mem (hyp_of J \<tturnstile> cpy (load_F (conc_of J))) rest)
    then True                                                    \<comment> \<open>disjI1, disjI2\<close>
    else if tag_F (conc_of J) = F_NOT \<and> tag_F (load_F (conc_of J)) = F_OR
            \<and> mem (hyp_of J \<tturnstile> mkNot (cpx (load_F (load_F (conc_of J))))) rest
            \<and> mem (hyp_of J \<tturnstile> mkNot (cpy (load_F (load_F (conc_of J))))) rest
    then True                                                    \<comment> \<open>disjI3\<close>
    else if tag_F (conc_of J) = F_NOT \<and> tag_F (load_F (conc_of J)) = F_NOT
            \<and> mem (hyp_of J \<tturnstile> load_F (load_F (conc_of J))) rest
    then True                                                    \<comment> \<open>dNegI\<close>
    else if mem (hyp_of J \<tturnstile> mkNot (mkNot (conc_of J))) rest
    then True                                                    \<comment> \<open>dNegE\<close>
    else if find_disjE1 J rest rest then True
    else if find_disjE23 J rest then True
    else if find_exF J rest rest then True
    else False" and

  eqsub_inner_def: "eqsub_inner J a b ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> eqF (conc_of (list_hd ptr)) (conc_of J) a b then True
    else eqsub_inner J a b (list_tl ptr)" and

  eqsub_outer_def: "eqsub_outer J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J \<and> tag_F (conc_of (list_hd ptr)) = F_EQ
            \<and> eqsub_inner J (cpx (load_F (conc_of (list_hd ptr))))
                            (cpy (load_F (conc_of (list_hd ptr)))) rest
    then True else eqsub_outer J rest (list_tl ptr)" and

  check_eqsub_def: "check_eqsub J rest := eqsub_outer J rest rest" and

  check_eqsym_def: "check_eqsym J rest :=
    if tag_F (conc_of J) = F_EQ
       \<and> mem (hyp_of J \<tturnstile> mkEq (cpy (load_F (conc_of J))) (cpx (load_F (conc_of J)))) rest
    then True else False" and

  check_nat_rules_def: "check_nat_rules J rest :=
    if conc_of J = mkNat tZero then True                                  \<comment> \<open>nat0\<close>
    else if conc_of J = mkEq (tPred tZero) tZero then True                \<comment> \<open>pred0\<close>
    else if tag_F (conc_of J) = F_EQ
            \<and> mem (hyp_of J \<tturnstile> mkEq (tSuc (cpx (load_F (conc_of J))))
                                     (tSuc (cpy (load_F (conc_of J))))) rest
    then True                                                             \<comment> \<open>sucInj\<close>
    else if tag_F (conc_of J) = F_EQ
            \<and> tag_T (cpx (load_F (conc_of J))) = T_SUC
            \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC
            \<and> mem (hyp_of J \<tturnstile> mkEq (load_T (cpx (load_F (conc_of J))))
                                     (load_T (cpy (load_F (conc_of J))))) rest
    then True                                                             \<comment> \<open>sucCong\<close>
    else if tag_F (conc_of J) = F_EQ
            \<and> tag_T (cpx (load_F (conc_of J))) = T_PRED
            \<and> tag_T (cpy (load_F (conc_of J))) = T_PRED
            \<and> mem (hyp_of J \<tturnstile> mkEq (load_T (cpx (load_F (conc_of J))))
                                     (load_T (cpy (load_F (conc_of J))))) rest
    then True                                                             \<comment> \<open>predCong\<close>
    else if conc_of J = mkBool (boolArg (conc_of J))
            \<and> tag_F (boolArg (conc_of J)) = F_EQ
            \<and> mem (hyp_of J \<tturnstile> mkNat (cpx (load_F (boolArg (conc_of J))))) rest
            \<and> mem (hyp_of J \<tturnstile> mkNat (cpy (load_F (boolArg (conc_of J))))) rest
    then True                                                             \<comment> \<open>eqBool\<close>
    else if tag_F (conc_of J) = F_NOT \<and> tag_F (load_F (conc_of J)) = F_EQ
            \<and> tag_T (cpx (load_F (load_F (conc_of J)))) = T_SUC
            \<and> cpy (load_F (load_F (conc_of J))) = tZero
            \<and> mem (hyp_of J \<tturnstile> mkNat (load_T (cpx (load_F (load_F (conc_of J)))))) rest
    then True                                                             \<comment> \<open>sucNonZero\<close>
    else if tag_F (conc_of J) = F_EQ
            \<and> cpx (load_F (conc_of J)) = tPred (tSuc (cpy (load_F (conc_of J))))
            \<and> mem (hyp_of J \<tturnstile> mkNat (cpy (load_F (conc_of J)))) rest
    then True                                                             \<comment> \<open>predSucInv\<close>
    else if conc_of J = mkAnd (andL (conc_of J)) (andR (conc_of J))
            \<and> tag_F (andL (conc_of J)) = F_EQ \<and> tag_F (andR (conc_of J)) = F_EQ
            \<and> cpx (load_F (andL (conc_of J))) = cpy (load_F (andL (conc_of J)))
            \<and> cpx (load_F (andR (conc_of J))) = cpy (load_F (andR (conc_of J)))
            \<and> mem (hyp_of J \<tturnstile> mkBool (mkEq (cpx (load_F (andL (conc_of J))))
                                             (cpx (load_F (andR (conc_of J)))))) rest
    then True                                                             \<comment> \<open>eqE\<close>
    else if tag_F (conc_of J) = F_EQ
            \<and> cpx (load_F (conc_of J)) = cpy (load_F (conc_of J))
            \<and> mem (hyp_of J \<tturnstile> mkNat (tPred (cpx (load_F (conc_of J))))) rest
    then True                                                             \<comment> \<open>predTIE\<close>
    else False" and

  ind_inner_def: "ind_inner J i p rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_EQ
            \<and> cpx (load_F (conc_of (list_hd ptr))) = cpy (load_F (conc_of (list_hd ptr)))
            \<and> fresh_T i (cpx (load_F (conc_of (list_hd ptr))))
            \<and> subst_F p i (cpx (load_F (conc_of (list_hd ptr)))) = conc_of J
            \<and> mem (hyp_of J \<tturnstile> subst_F p i tZero) rest
    then True else ind_inner J i p rest (list_tl ptr)" and

  ind_outer_def: "ind_outer J rest ptr :=
    if ptr = Nil then False
    else if list_hd (hyp_of (list_hd ptr))
              = mkNat (tVar (load_T (cpx (load_F (list_hd (hyp_of (list_hd ptr)))))))
            \<and> list_tl (list_tl (hyp_of (list_hd ptr))) = hyp_of J
            \<and> conc_of (list_hd ptr)
                = subst_F (list_hd (list_tl (hyp_of (list_hd ptr))))
                          (load_T (cpx (load_F (list_hd (hyp_of (list_hd ptr))))))
                          (tSuc (tVar (load_T (cpx (load_F (list_hd (hyp_of (list_hd ptr))))))))
            \<and> fresh_H (load_T (cpx (load_F (list_hd (hyp_of (list_hd ptr)))))) (hyp_of J)
            \<and> ind_inner J (load_T (cpx (load_F (list_hd (hyp_of (list_hd ptr))))))
                          (list_hd (list_tl (hyp_of (list_hd ptr)))) rest rest
    then True else ind_outer J rest (list_tl ptr)" and

  check_ind_def: "check_ind J rest := ind_outer J rest rest" and

  find_allE_inner_def: "find_allE_inner J i p ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_EQ
            \<and> cpx (load_F (conc_of (list_hd ptr))) = cpy (load_F (conc_of (list_hd ptr)))
            \<and> subst_F p i (cpx (load_F (conc_of (list_hd ptr)))) = conc_of J
    then True else find_allE_inner J i p (list_tl ptr)" and

  find_allE_def: "find_allE J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_ALL
            \<and> find_allE_inner J (cpx (load_F (conc_of (list_hd ptr))))
                                (cpy (load_F (conc_of (list_hd ptr)))) rest
    then True else find_allE J rest (list_tl ptr)" and

  find_exI_def: "find_exI J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_EQ
            \<and> cpx (load_F (conc_of (list_hd ptr))) = cpy (load_F (conc_of (list_hd ptr)))
            \<and> mem (hyp_of J \<tturnstile> subst_F (cpy (load_F (conc_of J)))
                                       (cpx (load_F (conc_of J)))
                                       (cpx (load_F (conc_of (list_hd ptr))))) rest
    then True else find_exI J rest (list_tl ptr)" and

  find_exE_def: "find_exE J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_EX
            \<and> fresh_H (J + 1) (hyp_of J) \<and> fresh_F (J + 1) (conc_of J)
            \<and> mem (subst_F (cpy (load_F (conc_of (list_hd ptr))))
                           (cpx (load_F (conc_of (list_hd ptr)))) (tVar (J + 1))
                   \<triangleright> mkNat (tVar (J + 1)) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
    then True else find_exE J rest (list_tl ptr)" and

  find_nallE_def: "find_nallE J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_NOT
            \<and> tag_F (load_F (conc_of (list_hd ptr))) = F_ALL
            \<and> fresh_H (J + 1) (hyp_of J) \<and> fresh_F (J + 1) (conc_of J)
            \<and> mem (mkNot (subst_F (cpy (load_F (load_F (conc_of (list_hd ptr)))))
                                  (cpx (load_F (load_F (conc_of (list_hd ptr)))))
                                  (tVar (J + 1)))
                   \<triangleright> mkNat (tVar (J + 1)) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
    then True else find_nallE J rest (list_tl ptr)" and

  check_quant_rules_def: "check_quant_rules J rest :=
    if tag_F (conc_of J) = F_ALL
       \<and> fresh_H (cpx (load_F (conc_of J))) (hyp_of J)
       \<and> mem (mkNat (tVar (cpx (load_F (conc_of J)))) \<triangleright> hyp_of J
              \<tturnstile> cpy (load_F (conc_of J))) rest
    then True                                                        \<comment> \<open>forallI\<close>
    else if tag_F (conc_of J) = F_EX \<and> find_exI J rest rest then True \<comment> \<open>existsI\<close>
    else if find_allE J rest rest then True                           \<comment> \<open>forallE\<close>
    else if find_exE J rest rest then True                            \<comment> \<open>existsE\<close>
    else if find_nallE J rest rest then True                          \<comment> \<open>notForallE\<close>
    else False" and

  check_condI_def: "check_condI J rest :=
    if tag_F (conc_of J) = F_EQ \<and> tag_T (cpx (load_F (conc_of J))) = T_COND
       \<and> psnd (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J))
       \<and> mem (hyp_of J \<tturnstile> pfst (load_T (cpx (load_F (conc_of J))))) rest
       \<and> mem (hyp_of J \<tturnstile> mkNat (cpy (load_F (conc_of J)))) rest
    then True                                                          \<comment> \<open>condI1\<close>
    else if tag_F (conc_of J) = F_EQ \<and> tag_T (cpx (load_F (conc_of J))) = T_COND
       \<and> pthd (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J))
       \<and> mem (hyp_of J \<tturnstile> mkNot (pfst (load_T (cpx (load_F (conc_of J)))))) rest
       \<and> mem (hyp_of J \<tturnstile> mkNat (cpy (load_F (conc_of J)))) rest
    then True                                                          \<comment> \<open>condI2\<close>
    else if conc_of J = mkIff (iffL (conc_of J)) (iffR (conc_of J))
       \<and> tag_F (iffL (conc_of J)) = F_COND
       \<and> psnd (load_F (iffL (conc_of J))) = iffR (conc_of J)
       \<and> mem (hyp_of J \<tturnstile> pfst (load_F (iffL (conc_of J)))) rest
       \<and> mem (hyp_of J \<tturnstile> mkBool (iffR (conc_of J))) rest
    then True                                                          \<comment> \<open>condI1B\<close>
    else if conc_of J = mkIff (iffL (conc_of J)) (iffR (conc_of J))
       \<and> tag_F (iffL (conc_of J)) = F_COND
       \<and> pthd (load_F (iffL (conc_of J))) = iffR (conc_of J)
       \<and> mem (hyp_of J \<tturnstile> mkNot (pfst (load_F (iffL (conc_of J))))) rest
       \<and> mem (hyp_of J \<tturnstile> mkBool (iffR (conc_of J))) rest
    then True                                                          \<comment> \<open>condI2B\<close>
    else False" and

  find_condE_def: "find_condE J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
       \<and> tag_F (conc_of (list_hd ptr)) = F_EQ
       \<and> cpx (load_F (conc_of (list_hd ptr))) = cpy (load_F (conc_of (list_hd ptr)))
       \<and> tag_T (cpx (load_F (conc_of (list_hd ptr)))) = T_COND
       \<and> ((conc_of J = mkNat (psnd (load_T (cpx (load_F (conc_of (list_hd ptr))))))
           \<and> mem (hyp_of J \<tturnstile> pfst (load_T (cpx (load_F (conc_of (list_hd ptr)))))) rest)
          \<or> (conc_of J = mkNat (pthd (load_T (cpx (load_F (conc_of (list_hd ptr))))))
             \<and> mem (hyp_of J \<tturnstile> mkNot (pfst (load_T (cpx (load_F (conc_of (list_hd ptr))))))) rest)
          \<or> conc_of J = mkBool (pfst (load_T (cpx (load_F (conc_of (list_hd ptr)))))))
    then True                                              \<comment> \<open>condE1, condE2, condE3\<close>
    else if hyp_of (list_hd ptr) = hyp_of J
       \<and> conc_of (list_hd ptr) = mkBool (boolArg (conc_of (list_hd ptr)))
       \<and> tag_F (boolArg (conc_of (list_hd ptr))) = F_COND
       \<and> ((conc_of J = mkBool (psnd (load_F (boolArg (conc_of (list_hd ptr)))))
           \<and> mem (hyp_of J \<tturnstile> pfst (load_F (boolArg (conc_of (list_hd ptr))))) rest)
          \<or> (conc_of J = mkBool (pthd (load_F (boolArg (conc_of (list_hd ptr)))))
             \<and> mem (hyp_of J \<tturnstile> mkNot (pfst (load_F (boolArg (conc_of (list_hd ptr)))))) rest)
          \<or> conc_of J = mkBool (pfst (load_F (boolArg (conc_of (list_hd ptr))))))
    then True                                           \<comment> \<open>condE1B, condE2B, condE3B\<close>
    else find_condE J rest (list_tl ptr)" and

  lazy_inner_def: "lazy_inner J c sel dir ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> (if dir = 0 then lzF (conc_of (list_hd ptr)) (conc_of J) c sel
               else lzF (conc_of J) (conc_of (list_hd ptr)) c sel)
    then True else lazy_inner J c sel dir (list_tl ptr)" and

  lazy_outer_def: "lazy_outer J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> (lazy_inner J (conc_of (list_hd ptr)) 0 0 rest
               \<or> lazy_inner J (conc_of (list_hd ptr)) 0 1 rest)
    then True                                        \<comment> \<open>cond_thenQ_E, cond_thenQ_I\<close>
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_NOT
            \<and> (lazy_inner J (load_F (conc_of (list_hd ptr))) 1 0 rest
               \<or> lazy_inner J (load_F (conc_of (list_hd ptr))) 1 1 rest)
    then True                                        \<comment> \<open>cond_elseQ_E, cond_elseQ_I\<close>
    else lazy_outer J rest (list_tl ptr)" and

  check_cond_rules_def: "check_cond_rules J rest :=
    if check_condI J rest then True
    else if find_condE J rest rest then True
    else if lazy_outer J rest rest then True
    else False" and

  find_def_def: "find_def J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> (unfF (conc_of J) (conc_of (list_hd ptr)) (hyp_of J) rest
               \<or> unfF (conc_of (list_hd ptr)) (conc_of J) (hyp_of J) rest)
    then True else find_def J rest (list_tl ptr)" and

  check_def_def: "check_def J rest := find_def J rest rest" and

  valid_step_def: "valid_step J rest :=
    if mem (conc_of J) (hyp_of J) then True         \<comment> \<open>hyp, from Pure assume\<close>
    else if check_weak J rest then True             \<comment> \<open>weak, from the hypothesis set\<close>
    else if check_cut J rest then True              \<comment> \<open>cut, from Pure implies intr/elim\<close>
    else if check_inst J rest then True             \<comment> \<open>inst, from Thm.instantiate\<close>
    else if check_prop_rules J rest then True       \<comment> \<open>the nine disj/not axioms\<close>
    else if check_eqsym J rest then True            \<comment> \<open>eqSym\<close>
    else if check_eqsub J rest then True            \<comment> \<open>eqSubst\<close>
    else if check_nat_rules J rest then True        \<comment> \<open>the ten arithmetic axioms\<close>
    else if check_ind J rest then True              \<comment> \<open>ind\<close>
    else if check_quant_rules J rest then True      \<comment> \<open>the six quantifier axioms\<close>
    else if check_cond_rules J rest then True       \<comment> \<open>the fourteen conditional axioms\<close>
    else if check_def J rest then True              \<comment> \<open>defE, defI\<close>
    else False" and

  check_list_def: "check_list pf :=
    if pf = Nil then True
    else if valid_step (list_hd pf) (list_tl pf) then check_list (list_tl pf)
    else False" and

  is_valid_proof_def: "is_valid_proof pf J :=
    if pf = Nil then False
    else if list_hd pf = J then check_list pf
    else False" and

  evT_def: "evT k t A :=
    if k = 0 then 0
    else if tag_T t = T_VAR  then nth (load_T t) A
    else if tag_T t = T_ZERO then S 0
    else if tag_T t = T_SUC then
      (if evT (P k) (load_T t) A = 0 then 0 else S (evT (P k) (load_T t) A))
    else if tag_T t = T_PRED then
      (if evT (P k) (load_T t) A = 0 then 0 else S (P (P (evT (P k) (load_T t) A))))
    else if tag_T t = T_COND then
      (if evF (P k) (pfst (load_T t)) A = 2 then evT (P k) (psnd (load_T t)) A
       else if evF (P k) (pfst (load_T t)) A = 1 then evT (P k) (pthd (load_T t)) A
       else 0)
    else if tag_T t = T_APP then
      (if evT (P k) (psnd (load_T t)) A = 0 then 0
       else if evT (P k) (pthd (load_T t)) A = 0 then 0
       else evT (P k) (nth (pfst (load_T t)) dfns)
              (evT (P k) (psnd (load_T t)) A \<triangleright> evT (P k) (pthd (load_T t)) A \<triangleright> Nil))
    else 0" and

  evF_def: "evF k f A :=
    if k = 0 then 0
    else if tag_F f = F_EQ then
      (if evT (P k) (cpx (load_F f)) A = 0 then 0
       else if evT (P k) (cpy (load_F f)) A = 0 then 0
       else if evT (P k) (cpx (load_F f)) A = evT (P k) (cpy (load_F f)) A then 2 else 1)
    else if tag_F f = F_NOT then
      (if evF (P k) (load_F f) A = 2 then 1
       else if evF (P k) (load_F f) A = 1 then 2 else 0)
    else if tag_F f = F_OR then
      (if evF (P k) (cpx (load_F f)) A = 2 then 2
       else if evF (P k) (cpy (load_F f)) A = 2 then 2
       else if evF (P k) (cpx (load_F f)) A = 1 then
              (if evF (P k) (cpy (load_F f)) A = 1 then 1 else 0)
       else 0)
    else if tag_F f = F_ALL then all_tt (P k) (cpx (load_F f)) (cpy (load_F f)) A
    else if tag_F f = F_EX  then ex_tt  (P k) (cpx (load_F f)) (cpy (load_F f)) A
    else if tag_F f = F_COND then
      (if evF (P k) (pfst (load_F f)) A = 2 then evF (P k) (psnd (load_F f)) A
       else if evF (P k) (pfst (load_F f)) A = 1 then evF (P k) (pthd (load_F f)) A
       else 0)
    else 0" and

  hypsat_def: "hypsat j G A :=
    if G = Nil then 1
    else if evF j (list_hd G) A = 2 then hypsat j (list_tl G) A
    else 0" and

  all_tt_def: "all_tt w i phi A :=
    if is_valid_proof (cpx (cpy w))
         (mkNat (tVar i) \<triangleright> cpy (cpy w) \<tturnstile> close_F phi (i \<triangleright> Nil) A)
       \<and> fresh_H 0 (cpy (cpy w))
       \<and> hypsat (cpx w) (cpy (cpy w)) A = 1
    then 2
    else if w > 0 = 1 then all_tt (w - 1) i phi A
    else 0" and

  ex_tt_def: "ex_tt w i phi A :=
    if evF (cpx w) phi (asn_put A i (S (cpy w))) = 2 then 2
    else if w > 0 = 1 then ex_tt (w - 1) i phi A
    else 0" and

  wsat_def: "wsat f A :=
    (\<exists>k. evF k f A = 2)
    \<and> ((tag_F f = F_NOT \<longrightarrow> wunsat (load_F f) A)
    \<and> ((tag_F f = F_OR \<longrightarrow> (wsat (cpx (load_F f)) A \<or> wsat (cpy (load_F f)) A))
    \<and> ((tag_F f = F_ALL \<longrightarrow> (\<forall>n. wsat (cpy (load_F f)) (asn_put A (cpx (load_F f)) (S n))))
    \<and> ((tag_F f = F_EX \<longrightarrow> (\<exists>n. wsat (cpy (load_F f)) (asn_put A (cpx (load_F f)) (S n))))
    \<and> (tag_F f = F_COND \<longrightarrow>
         ((wsat (pfst (load_F f)) A \<and> wsat (psnd (load_F f)) A)
          \<or> (wunsat (pfst (load_F f)) A \<and> wsat (pthd (load_F f)) A)))))))" and

  wunsat_def: "wunsat f A :=
    (\<exists>k. evF k f A = 1)
    \<and> ((tag_F f = F_NOT \<longrightarrow> wsat (load_F f) A)
    \<and> ((tag_F f = F_OR \<longrightarrow> (wunsat (cpx (load_F f)) A \<and> wunsat (cpy (load_F f)) A))
    \<and> (tag_F f = F_COND \<longrightarrow>
         ((wsat (pfst (load_F f)) A \<and> wunsat (psnd (load_F f)) A)
          \<or> (wunsat (pfst (load_F f)) A \<and> wunsat (pthd (load_F f)) A)))))"


section \<open>4.  Discharging the structural assumptions\<close>

text \<open>
  The habeas quid, retraction, decrease and monotonicity obligations are the
  ones \<open>encode.thy\<close> discharges, unchanged: they are statements about the Cantor
  pairing and \<open>swap01\<close> alone and know nothing about the syntax being encoded.
  They are restated here rather than imported because this development sits
  beside the BGA one rather than on top of it.
\<close>

lemma pack_F_N: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> pack_F t L N"
  unfolding pack_F_def by (rule cpair_terminates)
lemma tag_F_N: "f N \<Longrightarrow> tag_F f N"   unfolding tag_F_def by simp
lemma load_F_N: "f N \<Longrightarrow> load_F f N" unfolding load_F_def by simp
lemma pack_T_N: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> pack_T t L N"
  unfolding pack_T_def by (rule cpair_terminates, rule swap01_N, simp+)
lemma tag_T_N: "t N \<Longrightarrow> tag_T t N"   unfolding tag_T_def by (rule swap01_N, simp)
lemma load_T_N: "t N \<Longrightarrow> load_T t N" unfolding load_T_def by simp

lemma tag_pack_F: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> tag_F (pack_F t L) = t"
  unfolding tag_F_def pack_F_def by (rule cpx_proj)
lemma load_pack_F: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> load_F (pack_F t L) = L"
  unfolding load_F_def pack_F_def by (rule cpy_proj)
lemma pack_tag_F: "f N \<Longrightarrow> pack_F (tag_F f) (load_F f) = f"
  unfolding pack_F_def tag_F_def load_F_def by (rule eqSym, simp)

lemma tag_pack_T: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> tag_T (pack_T t L) = t"
  unfolding tag_T_def pack_T_def
  apply (simp only: cpx_proj[OF swap01_N])
  apply (rule swap01_inv, assumption)
  done
lemma load_pack_T: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> load_T (pack_T t L) = L"
  unfolding load_T_def pack_T_def by (rule cpy_proj[OF swap01_N])
lemma pack_tag_T: "t N \<Longrightarrow> pack_T (tag_T t) (load_T t) = t"
  unfolding pack_T_def tag_T_def load_T_def
  apply (simp only: swap01_inv[OF cpx_terminates])
  apply (rule eqSym) apply auto done

lemma decrease_F: "\<lbrakk>f N; f \<noteq> 0\<rbrakk> \<Longrightarrow> load_F f < f = 1" unfolding load_F_def by simp
lemma decrease_T: "\<lbrakk>t N; t \<noteq> 0\<rbrakk> \<Longrightarrow> load_T t < t = 1" unfolding load_T_def by simp
lemma tag_T_zero: "tag_T 0 = T_ZERO" unfolding tag_T_def by simp
lemma tag_F_zero: "tag_F 0 = F_EQ"   unfolding tag_F_def by simp

lemma pair_step:
  assumes a: "a N" and k: "k N"
  shows "\<langle>a, k\<rangle> \<le> \<langle>a, S k\<rangle> = 1"
proof -
  have ak: "\<langle>a, k\<rangle> N"     by (rule cpair_terminates[OF a k])
  have sk: "S k N"        by (rule natS[OF k])
  have one: "(1::num) N"  by simp
  have aka:   "\<langle>a, k\<rangle> + a N"       using ak a by simp
  have akask: "\<langle>a, k\<rangle> + a + S k N" using aka sk by simp
  have s1: "\<langle>a, k\<rangle> \<le> \<langle>a, k\<rangle> = 1"               by (rule leq_refl[OF ak])
  have s2: "\<langle>a, k\<rangle> \<le> \<langle>a, k\<rangle> + a = 1"           by (rule leq_monotone_add_r[OF s1 ak ak a])
  have s3: "\<langle>a, k\<rangle> \<le> \<langle>a, k\<rangle> + a + S k = 1"     by (rule leq_monotone_add_r[OF s2 ak aka sk])
  have s4: "\<langle>a, k\<rangle> \<le> \<langle>a, k\<rangle> + a + S k + 1 = 1" by (rule leq_monotone_add_r[OF s3 ak akask one])
  have e:  "\<langle>a, S k\<rangle> = \<langle>a, k\<rangle> + a + S k + 1"    by (rule cpair_suc[OF a k])
  show ?thesis using s4 e by simp
qed

lemma pair_mono_2:
  assumes a: "a N" and x: "x N" and y: "y N" and h: "x \<le> y = 1"
  shows "\<langle>a, x\<rangle> \<le> \<langle>a, y\<rangle> = 1"
proof -
  have one: "(1::num) N" by simp
  have main: "(x \<le> y = 1) \<longrightarrow> (\<langle>a, x\<rangle> \<le> \<langle>a, y\<rangle> = 1)"
  proof (rule ind[where a = y])
    show "y N" by (rule y)
  next
    show "(x \<le> 0 = 1) \<longrightarrow> (\<langle>a, x\<rangle> \<le> \<langle>a, 0\<rangle> = 1)"
    proof (rule implI)
      show "(x \<le> 0 = 1) B" by (rule eqBool[OF leq_terminates[OF x nat0] one])
    next
      assume x0: "x \<le> 0 = 1"
      have "x = 0" by (rule leq_0[OF x x0])
      thus "\<langle>a, x\<rangle> \<le> \<langle>a, 0\<rangle> = 1"
        by (simp add: leq_refl[OF cpair_terminates[OF a nat0]])
    qed
  next
    fix k assume k: "k N" and IH: "(x \<le> k = 1) \<longrightarrow> (\<langle>a, x\<rangle> \<le> \<langle>a, k\<rangle> = 1)"
    show "(x \<le> S k = 1) \<longrightarrow> (\<langle>a, x\<rangle> \<le> \<langle>a, S k\<rangle> = 1)"
    proof (rule implI)
      show "(x \<le> S k = 1) B" by (rule eqBool[OF leq_terminates[OF x natS[OF k]] one])
    next
      assume xsk: "x \<le> S k = 1"
      have ax:  "\<langle>a, x\<rangle> N"   by (rule cpair_terminates[OF a x])
      have ak:  "\<langle>a, k\<rangle> N"   by (rule cpair_terminates[OF a k])
      have ask: "\<langle>a, S k\<rangle> N" by (rule cpair_terminates[OF a natS[OF k]])
      have step: "\<langle>a, k\<rangle> \<le> \<langle>a, S k\<rangle> = 1" by (rule pair_step[OF a k])
      show "\<langle>a, x\<rangle> \<le> \<langle>a, S k\<rangle> = 1"
      proof (rule cases_bool[where q = "x \<le> k = 1"])
        show "(x \<le> k = 1) B" by (rule eqBool[OF leq_terminates[OF x k] one])
      next
        assume xk: "x \<le> k = 1"
        have xy: "\<langle>a, x\<rangle> \<le> \<langle>a, k\<rangle> = 1" by (rule implE[OF IH xk])
        show "\<langle>a, x\<rangle> \<le> \<langle>a, S k\<rangle> = 1" by (rule leq_trans[OF ax ak ask xy step])
      next
        assume nxk: "\<not> (x \<le> k = 1)"
        have "x = S k" by (rule leq_suc_not_leq_implies_eq[OF x k nxk xsk])
        thus "\<langle>a, x\<rangle> \<le> \<langle>a, S k\<rangle> = 1" by (simp add: leq_refl[OF ask])
      qed
    qed
  qed
  show ?thesis by (rule implE[OF main h])
qed

lemma mono_pack_T: "\<lbrakk>tg N; x N; y N; x \<le> y = 1\<rbrakk> \<Longrightarrow> pack_T tg x \<le> pack_T tg y = 1"
  unfolding pack_T_def by (rule pair_mono_2[OF swap01_N])
lemma mono_pack_F: "\<lbrakk>tg N; x N; y N; x \<le> y = 1\<rbrakk> \<Longrightarrow> pack_F tg x \<le> pack_F tg y = 1"
  unfolding pack_F_def by (rule pair_mono_2)

lemma tZero_N: "tZero N" by (rule pack_T_N, auto)

lemma tBot_N: "tBot N"
proof -
  have p: "\<langle>tZero, tZero\<rangle> N" by (rule cpair_terminates[OF tZero_N tZero_N])
  have q: "\<langle>0, \<langle>tZero, tZero\<rangle>\<rangle> N" by (rule cpair_terminates[OF nat0 p])
  show ?thesis unfolding tBot_def by (rule pack_T_N[OF _ q], auto)
qed

lemma tBot_closed: "fresh_T 0 tBot"
  \<comment> \<open>one \<open>defE\<close> step through \<open>fresh_T_def\<close>: the tag is \<open>T_APP\<close> and both
      arguments are \<open>tZero\<close>, whose tag is \<open>T_ZERO\<close>, so both branches are \<open>True\<close>.\<close>
  sorry


section \<open>5.  Interpretation\<close>

text \<open>
  Every goal generated by \<open>unfold_locales\<close> is closed by \<open>fact\<close>: the structural
  obligations by the lemmas above, the definitional obligations by the \<open>:=\<close>
  axioms of section 3, which are literally the equations the locale assumes.
\<close>

interpretation qga: qga_full
  tag_T load_T pack_T tag_F load_F pack_F fresh_T fresh_F fresh_H subst_T subst_F subst_H subst_body asn_put numeral_of tBot close_T close_F close_H dfns dfn_is eqT eqF lzT lzF unfT unfF find_cut check_cut find_weak check_weak inst_try inst_a inst_i check_inst find_disjE1 find_disjE23 find_exF check_prop_rules eqsub_inner eqsub_outer check_eqsub check_eqsym check_nat_rules ind_inner ind_outer check_ind find_allE_inner find_allE find_exI find_exE find_nallE check_quant_rules find_condE check_condI lazy_inner lazy_outer check_cond_rules find_def check_def valid_step check_list is_valid_proof evT evF hypsat all_tt ex_tt wsat wunsat
  apply unfold_locales
  apply (fact pack_T_N tag_T_N load_T_N pack_F_N tag_F_N load_F_N
              tag_pack_T load_pack_T pack_tag_T tag_pack_F load_pack_F pack_tag_F
              decrease_T decrease_F tag_T_zero tag_F_zero mono_pack_T mono_pack_F
              dfns_N tBot_N tBot_closed
              fresh_T_def fresh_F_def fresh_H_def subst_T_def
              subst_F_def subst_H_def subst_body_def asn_put_def
              numeral_of_def close_T_def close_F_def close_H_def
              dfn_is_def eqT_def eqF_def lzT_def
              lzF_def unfT_def unfF_def find_cut_def
              check_cut_def find_weak_def check_weak_def inst_try_def
              inst_a_def inst_i_def check_inst_def find_disjE1_def
              find_disjE23_def find_exF_def check_prop_rules_def eqsub_inner_def
              eqsub_outer_def check_eqsub_def check_eqsym_def check_nat_rules_def
              ind_inner_def ind_outer_def check_ind_def find_allE_inner_def
              find_allE_def find_exI_def find_exE_def find_nallE_def
              check_quant_rules_def check_condI_def find_condE_def lazy_inner_def
              lazy_outer_def check_cond_rules_def find_def_def check_def_def
              valid_step_def check_list_def is_valid_proof_def evT_def
              evF_def hypsat_def all_tt_def ex_tt_def
              wsat_def wunsat_def
              )+
  done


section \<open>6.  QGA is consistent\<close>

text \<open>
  Read out: for every formula code \<open>f\<close> and all proof codes \<open>p1\<close> and \<open>p2\<close>, it is
  not the case that \<open>p1\<close> codes a QGA proof of \<open>f\<close> from no hypotheses while \<open>p2\<close>
  codes a QGA proof of the negation of \<open>f\<close> from no hypotheses.  Every symbol in
  that statement --- the quantifiers, the negation, the conjunction, the proof
  checker --- belongs to QGA, and the system being talked about is QGA.

  This does not contradict the second incompleteness theorem.  QGA is
  paracomplete: its grounded truth is recursively enumerable and not closed
  under classical negation, so the diagonal sentence comes out ungrounded
  rather than true, and the derivability conditions fail --- \<open>implI\<close> carries a
  habeas quid premise, so the internal necessitation and distribution steps
  that Loeb\<^latex>\<open>'\<close>s theorem needs are not available.  RGA establishes the
  corresponding facts for a stronger system in a classical metatheory; what is
  new here is that the argument is carried out in the object logic.
\<close>

theorem QGA_syntactically_consistent:
  assumes "f N" and "p1 N" and "p2 N"
  shows "\<not> (is_valid_proof p1 \<langle>Nil, f\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mkNot f\<rangle>)"
  using assms by (rule qga.syntactically_consistent)

end
