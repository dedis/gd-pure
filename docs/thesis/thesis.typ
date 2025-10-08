// =====================================================
// The main thesis file that brings together all
// other logic and contains the body of the thesis.
// =====================================================

#import "thesis-template.typ": thesis-template
#import "titlepage.typ": title-page

#let abstract-thesis = text[
  This thesis presents a foundational formalization of Grounded Arithmetic (GA), a first-order arithmetic based on the principles of Grounded Deduction (GD), directly within the Isabelle/Pure framework. Unlike classical and constructive logics, which impose strict termination requirements on definitions to preserve consistency, GD admits arbitrary recursion at the definitional level. To remain consistent, GD weakens other inference rules, many of which demand explicit _habeas quid_ termination proofs of subexpressions as premises. The goal of this thesis is to investigate the feasibility of GA as a practical basis for mathematical and computational reasoning by fully axiomatizing it in Pure.

  The formalization, Isabelle/GA, achieves three main contributions. It provides a complete axiomatization of GA in Pure, together with definitions of core arithmetic functions using the native recursive definitional mechanism of GA, and proofs of their fundamental properties. It develops a suite of reasoning tools, such as subgoal solvers, syntactic extensions, and methods for case analysis and induction, automating many of GA’s _habeas quid_ proof obligations and moving away from axiom-level proofs. Finally, it shows GA’s expressive power by encoding inductive datatypes via Cantor tuples and proving their essential properties, demonstrated by a fully verified List datatype.

  The resulting system demonstrates that GA "works", despite many weakened inference rules: one can reason productively in it, prove termination of functions beyond primitive recursion such as Ackermann’s function, and encode arbitrary inductive datatypes. While the implementation of a fully general definitional mechanism for inductive datatypes remains future work, the foundations developed here provide the necessary basis. Altogether, this thesis shows that grounded reasoning is practical and that GA has the potential to mature into a serious alternative foundation for reasoning about computation.
]

#show: thesis-template.with(
  title-page: title-page.with(
    title: "Formalizing Grounded Arithmetic atop Isabelle/Pure",
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
#include "chapters/conclusion.typ"
 
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
