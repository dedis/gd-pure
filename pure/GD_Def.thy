theory GD_Def
  imports GD
begin

text \<open>
  Examples for \<^theory_text>\<open>gd_def\<close>, which is defined in \<open>GD.thy\<close> --- it has to be,
  since the arithmetic definitions there use it. This theory exercises the
  command and is imported by nothing.

  \<^theory_text>\<open>gd_def\<close> introduces a recursive definition through the \<open>:=\<close> mechanism. It
  declares the constants, asserts the equations, names the first one \<open>\<langle>const\<rangle>_def\<close> when
  no name is given --- the form \<open>unfold_def\<close> and \<open>fold_def\<close> expect, since they
  look a theorem up by name --- and records the definition so that a grounding
  lemma can be attached to it afterwards with \<open>[grounded_by]\<close>.

  Each declared constant takes exactly one equation, and each equation must
  define a constant the block declares. \<open>:=\<close> is not pattern matching: an
  equation for some other constant would silently give an existing definition
  a second one, and two equations for the same constant make their bodies
  interchangeable with each other.

  There is no proof obligation on the body. GD is a language of arbitrary
  recursion, so whether \<open>f a N\<close> holds, and for which arguments, is an
  ordinary theorem.
\<close>


section \<open>Examples\<close>

gd_def dbl :: \<open>num \<Rightarrow> num\<close>
  where \<open>dbl x := if x = 0 then 0 else S(S(dbl (P x)))\<close>

lemma dbl_N [grounded_by dbl, auto]: \<open>x N \<Longrightarrow> dbl x N\<close>
  apply (induct x)
   apply (unfold_def dbl_def, simp)+
  done

lemma dbl_zero [simp]: \<open>dbl 0 = 0\<close>
  by (unfold_def dbl_def, simp)

lemma dbl_suc: \<open>x N \<Longrightarrow> dbl S(x) = S(S(dbl x))\<close>
  by (unfold_def dbl_def, simp)

text \<open>A definition need not be grounded, and nothing is imposed on it.\<close>

gd_def loop :: \<open>num \<Rightarrow> num\<close>
  where \<open>loop x := S(loop x)\<close>

text \<open>Including at type \<open>o\<close>, where the Liar is a definition like any other.\<close>

gd_def L :: \<open>o\<close>
  where \<open>L := \<not>L\<close>

text \<open>
  \<^theory_text>\<open>print_gd_defs\<close> lists each definition with its grounding lemma or the
  absence of one, so it doubles as a worklist of terminations not yet proved.
\<close>

print_gd_defs

end
