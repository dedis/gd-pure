structure Peano_Syntax = struct

  fun nat_to_peano 0 = Syntax.const @{const_syntax "zero"}
    | nat_to_peano n = Syntax.const @{const_syntax "suc"} $ nat_to_peano (n - 1)

  fun parse_gd_numeral _ [Free (s, _)] =
        (case Int.fromString s of
           SOME n => nat_to_peano n
         | NONE => error ("Not a numeral: " ^ s))
    | parse_gd_numeral _ _ = error "Unexpected numeral syntax"

end
