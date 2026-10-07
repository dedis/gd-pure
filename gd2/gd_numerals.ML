(*  Title:      gd2/gd_numerals.ML

Numerals 2, 3, ... as iterated successors of 0.  The tokens 0 and 1 are
delimiters of GD_Core (the constant zero and the abbreviation one), so they
never reach this translation.
*)

structure GD_Numerals =
struct

fun peano 0 = Syntax.const @{const_syntax zero}
  | peano n = Syntax.const @{const_syntax suc} $ peano (n - 1);

fun parse_numeral _ [Free (s, _)] =
      (case Int.fromString s of
        SOME n => if n >= 0 then peano n else error ("Not a numeral: " ^ s)
      | NONE => error ("Not a numeral: " ^ s))
  | parse_numeral _ ts = raise TERM ("parse_numeral", ts);

end;
