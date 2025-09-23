// =====================================================
// The main thesis file that brings together all
// other logic and contains the body of the thesis.
// =====================================================

#import "thesis-template.typ": thesis-template
#import "titlepage.typ": title-page

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
