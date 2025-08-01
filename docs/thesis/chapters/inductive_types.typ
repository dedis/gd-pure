// =====================================================
// The inductive datatype chapter. Formalizes required
// number theory to be able to express cantor pairings.
// Then, writes a package that encodes arbitrary data-
// types into the formalized integers.
// =====================================================

#import "../style.typ": definition-box
#import "../formalisms.typ": *
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#show: codly-init.with()
#codly(zebra-fill: none)

= Encoding Inductive Datatypes in GD

We now have all the tools to formalize the GD logic in Isabelle.
