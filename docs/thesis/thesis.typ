// =====================================================
// The main thesis file that brings together all
// other logic and contains the body of the thesis.
// =====================================================

#import "thesis-template.typ": thesis-template
#import "titlepage.typ": title-page

#let abstract-thesis = text[
  
This thesis presents a foundational formalization of Grounded Arithmetic (GA), a first-order arithmetic based on the principles of Grounded Deduction (GD), directly within the Isabelle/Pure framework. Unlike classical and constructive logics, which impose strict termination requirements on definitions to preserve consistency, GD admits arbitrary recursion at the definitional level while weakening other inference rules to preserve its own consistency. The goal of this thesis is to investigate the feasibility of GA as a basis for mathematical reasoning by fully axiomatizing it in Pure.

The contributions of this thesis are the following. First, GA is fully axomatized in Pure, including axioms for propositional reasoning, natural numbers, quantifiers, conditional evaluation, and unrestricted definitional mechanisms. Second, core arithmetic functions are defined, their termination properties established, and many basic properties about them proved, supported by tooling written in Standard ML (SML), such as a subgoal solver, syntactic extensions, and methods for case analysis and induction. Third, the expressive power of GA is demonstrated by introducing a general framework for encoding inductive datatypes via Cantor tuples, and by establishing their fundamental properties (distinctness, injectivity, exhaustiveness, closure, and induction), which are explicitly stated and proved for the List datatype.

The resulting system, Isabelle/GA, enables interactive reasoning directly in GA with proof automation adapted to the grounded setting. While the implementation of a fully general definitional mechanism for inductive datatypes remains future work, the foundations laid in this thesis provide a robust platform for further exploration of grounded reasoning as a viable alternative to classical foundations of mathematics.
]

#show: thesis-template.with(
  title-page: title-page.with(
    title: "A Foundational Formalization of Grounded Arithmetic in Isabelle/Pure",
    thesistype: "BSc Thesis",
    author: "Sascha Kehrli",
    email: "skehrli@ethz.ch",
    supervisors: (
      "Prof. Dr. Bryan Ford",
      "Prof. Dr. Roger Wattenhofer"
    ),
    institute: (
      "Distributed Computing Group",
      "Computer Engineering and Networks Laboratory",
      "ETH Zürich"
    ),
    image-left: image("figures/eth-logo.png", width: 75%),
    image-right: image("figures/disco-logo.png", width: 50%),
    date: datetime.today()
  ),
  abstract: abstract-thesis,
  bibliography: bibliography("references.bib"),
)

#include "chapters/introduction.typ"
#include "chapters/background.typ"
#include "chapters/gd_formalization.typ"
#include "chapters/gd_tooling.typ"
#include "chapters/inductive_types.typ"
 
// == Tabellen

// #figure(
//   caption: "Eine Tabelle",
//   table(
//     columns: (1fr, 50%, auto),
//     inset: 10pt,
//     align: horizon,
//     table.header(
//       [],
//       [*Area*],
//       [*Parameters*],
//     ),

//     text("cylinder.svg"),
//     $ pi h (D^2 - d^2) / 4 $,
//     [
//       $h$: height \
//       $D$: outer radius \
//       $d$: inner radius
//     ],

//     text("tetrahedron.svg"), $ sqrt(2) / 12 a^3 $, [$a$: edge length],
//   ),
// )<table>

// == Programm Quellcode

// Quellcode mit entsprechender Formatierung wird wie folgt eingefügt:

// #import "@preview/codelst:2.0.2": *
// #figure(
//   caption: "Ein Stück Quellcode",
//   sourcecode[```ts
//     const ReactComponent = () => {
//       return (
//         <div>
//           <h1>Hello World</h1>
//         </div>
//       );
//     };

//     export default ReactComponent;
//     ```],
// )
