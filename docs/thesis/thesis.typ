#import "@preview/codelst:2.0.2": *
#import "template.typ": template
#import "titlepage.typ": title-page

#let institute = [
  Distributed Computing Group\
  Computer Engineering and Networks Laboratory\
  ETH Zürich
]
#let supervisors = (
  "Prof. Dr. Bryan Ford",
  "Prof. Dr. Roger Wattenhofer"
)

#show: template.with(
  title-page: title-page.with(
    title: "A Foundational Formalization of GD in Isabelle/Pure",
    thesistype: "BSc Thesis",
    author: "Sascha Kehrli",
    email: "skehrli@ethz.ch",
    supervisors: supervisors,
    institute: institute,
    image-left: image("figures/eth-logo.png", width: 75%),
    image-right: image("figures/disco-logo.png", width: 50%),
    date: datetime.today()
  ),
  bibliography: bibliography("references.bib"),
)

= Introduction

#lorem(100)

#lorem(80)

#lorem(120)

= Background

== Grounded Deduction (GD)

== Isabelle/Pure

Pure is the minimal meta-logic in Isabelle. The popular Isabelle/HOL fragment is formalized atop Pure, as are all other object logics in Isabelle. Aside from a bare-bones logic, Pure provides infrastructure to define datatypes and axioms to facilitate the formalization of object logics in it.
= Syntax of Pure

The core syntax of Pure includes types and terms. Types describe the kinds of values in the system, while terms are the expressions manipulated by the logic.

== Types

$ tau &::= alpha "(type variable)" \
      &| op("prop") "(type of propositions)" \
      &| tau => tau "(function type)"
$

== Terms

$ t &::= x "(variable)" \
    &| c "(constant)" \
    &| t t "(application)" \
    &| lambda x. t "(object-level abstraction)" \
    &| Lambda x. t "(meta-level abstraction, big lambda)"
$

=== Tabellen

#figure(
  caption: "Eine Tabelle",
  table(
    columns: (1fr, 50%, auto),
    inset: 10pt,
    align: horizon,
    table.header(
      [],
      [*Area*],
      [*Parameters*],
    ),

    text("cylinder.svg"),
    $ pi h (D^2 - d^2) / 4 $,
    [
      $h$: height \
      $D$: outer radius \
      $d$: inner radius
    ],

    text("tetrahedron.svg"), $ sqrt(2) / 12 a^3 $, [$a$: edge length],
  ),
)<table>

== Programm Quellcode

Quellcode mit entsprechender Formatierung wird wie folgt eingefügt:

#figure(
  caption: "Ein Stück Quellcode",
  sourcecode[```ts
    const ReactComponent = () => {
      return (
        <div>
          <h1>Hello World</h1>
        </div>
      );
    };

    export default ReactComponent;
    ```],
)


== Verweise

Für Literaturverweise verwendet man die `cite`-Funktion oder die Kurzschreibweise mit dem \@-Zeichen:
// - `#cite(form: "prose", <iso18004>)` ergibt: \ #cite(form: "prose", <iso18004>)
// - Mit `@iso18004` erhält man: @iso18004

Tabellen, Abbildungen und andere Elemente können mit einem Label in spitzen Klammern gekennzeichnet werden (die Tabelle oben hat z.B. das Label `<table>`). Sie kann dann mit `@table` referenziert werden. Das ergibt im konkreten Fall: @table

= Fazit

#lorem(50)

#lorem(120)

#lorem(80)
