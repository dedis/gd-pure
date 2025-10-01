# Grounded Arithmetic Formalized atop Isabelle/Pure
This is the repository of [_Formalizing Grounded Arithmetic in Isabelle/Pure_](./docs/thesis/thesis.pdf), a B.Sc. thesis submitted by Sascha Kehrli at ETH Zürich in September 2025.

It contains a prototype implementation of the [_Grounded Arithmetic_ (_GA_) logic](https://bford.info/pub/lang/gd/) in the minimal metalogical framework [Isabelle/Pure](https://isabelle.in.tum.de/), in the [`GD.thy`](./pure/GD.thy) file. In particular, this file contains the entire formalization described in the thesis [`thesis.pdf`](./docs/thesis/thesis.pdf), that is,
- a full axiomatization of Grounded Arithmetic (GA)
- a formalization of basic arithmetic functions and their properties
- a formalization of Cantor tuples, its inverses, and some properties about them
- a manual encoding of a `List` datatype along with proofs of all the properties making it an inductive type

The `./docs` subdirectory contains the thesis source `.typ` files and compiled pdf, and the `./pure` subdirectory contains the Isabelle `.thy` files and `.ML` files used by the main `./pure/GD.thy` file.

To go through the Isabelle source file, simply open the [`./pure/GD.thy`](./docs/pure/GD.thy) file in an editor supporting Isabelle interactively. For example, there are great installation instructions for Isabelle and its native IDE on the [Isabelle website](https://isabelle.in.tum.de/installation.html).
