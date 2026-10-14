theory GD_Hammer_Test
  imports GD_Hammer
begin

text \<open>Regression for the oracle. Runs E, so it is kept out of GD_Hammer itself.\<close>

ML \<open>
  fun expect t names =
    (case GD_Hammer.run \<^context> 10 t of
      SOME ns =>
        if eq_set (op =) (ns, map (fn n => "GD." ^ n) names) then ()
        else error ("gd_hammer gave " ^ commas ns ^ " for " ^
                    Syntax.string_of_term \<^context> t)
    | NONE => error ("gd_hammer found nothing for " ^
                     Syntax.string_of_term \<^context> t));

  fun expect_none t =
    (case GD_Hammer.run \<^context> 5 t of
      NONE => ()
    | SOME ns => error ("gd_hammer should have found nothing, gave " ^ commas ns));

  expect @{prop "x N \<Longrightarrow> S (S x) N"} ["natS"];
  expect @{prop "x N \<Longrightarrow> y N \<Longrightarrow> x + y N"} ["add_terminates"];
  expect @{prop "a N \<Longrightarrow> S a \<noteq> 0"} ["sucNonZero", "natS"];
  expect @{prop "x N \<Longrightarrow> P (S x) N"} ["natP", "natS"];
  expect_none @{prop "x N \<Longrightarrow> zebra x N"};
\<close>

text \<open>
  Decidedness is not classically free. \<open>L B\<close> and its unfolding \<open>L \<or> \<not>L\<close> are
  both underivable in GD, and the oracle must not claim otherwise just because
  excluded middle holds on the classical side.
\<close>

gd_def L :: \<open>o\<close> where \<open>L := \<not>L\<close>

ML \<open>
  expect_none @{prop "L B"};
  expect_none @{prop "L \<or> \<not>L"};
  expect @{prop "x N \<Longrightarrow> (x = 0) B"} ["zeroRefl"];
\<close>

text \<open>The command itself.\<close>

lemma "x N  \<Longrightarrow> x * 2 N"
  gd_hammer
  by (simp add: GD.mult_terminates GD.natS GD.cpair_1_0_1)

end
