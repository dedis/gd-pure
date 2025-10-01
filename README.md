# Isabelle/GA
This is the thesis repository of "Formalizing Grounded Arithmetic in Isabelle/Pure".

The `./docs` subdirectory contains the thesis source `.typ` files and compiled pdf, and the `./pure` subdirectory contains the Isabelle `.thy` files and `.ML` files used by the main `GD.thy` file.

The `./pure/GD.thy` file contains the entire formalization described in the thesis `./docs/thesis/thesis.pdf`, that is,
- a full axiomatization of Grounded Arithmetic (GA)
- a formalization of basic arithmetic functions and their properties
- a formalization of Cantor tuples, its inverses, and some properties about them
- a manual encoding of a `List` datatype along with proofs of all the properties making it an inductive type

Simply open the `./pure/GD.thy` file in an editor supporting Isabelle interactively to inspect the artifact.
