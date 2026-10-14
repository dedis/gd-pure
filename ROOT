(* The encoding theories (BGA_on_GA, encode, QGA_on_GA, qga_encode) are not
   listed.  To check them, add:

     theories
       BGA_on_GA
       encode
     theories [quick_and_dirty]
       QGA_on_GA
       qga_encode

   Those two need quick_and_dirty (39 sorry between them); GD and GD_Def are
   clean without it. *)

session GD in "pure" = Pure +
  options [document = false]
  theories
    GD
    GD_Def
    GD_Classical
    GD_Hammer
    GD_Hammer_Test

session QGA_HOL in "hol" = HOL +
  options [document = false, timeout = 180]
  sessions
    "HOL-Library"
  theories
    QGA_Model
    QGA_Syntax
    QGA_Proof
