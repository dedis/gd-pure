#set page(
  paper: "us-letter",
  header: align(right)[
            BSc Thesis Proposal
            ],
  numbering: "1",
  columns: 2,
)

#set par(justify: true)

#set text(
  hyphenate: true,
)

#place(
  top + center,
  float: true,
  scope: "parent",
  clearance: 3em,
)[
  #align(center, text(14pt)[
    *A Foundational Formalization of Grounded Deduction In Isabelle\/Pure*
  ])

  #grid(
    columns: (1fr, 1fr, 1fr),
    align(center)[
      Sascha Kehrli \
      ETH Zürich \
      Author
    ],
    align(center)[
      Prof. Dr. Roger Wattenhofer \
      ETH Zürich \
      Supervisor
    ],
    align(center)[
      Prof. Dr. Bryan Ford \
      EPFL \
      Co-Supervisor
    ],
  )
]

== Introduction
Modern theorem provers such as Coq and Lean rely on strong foundational logics and support inductive definitions and recursive functions. These powerful definitional mechanisms can only retain consistency by being tightly constrained, typically requiring termination, well-foundedness, or other syntactic criteria on recursion.

Grounded Deduction (GD) is a novel logical framework developed to invert this model. Rather than constraining what users may define, GD permits arbitrary definitional recursion, even non-terminating or circular definitions such as $L equiv not L$ @gd.

To maintain consistency in the presence of such unconstrained recursion, expansions of definitions in proofs are syntactically restricted and generate proof obligations for the expanded term. This principle is the foundational promise of GD: definitional freedom without compromising consistency.

== Goal
GD is not well studied yet and in particular remains to be proven consistent relative to any logic. Ongoing work formalizes GD in Isabelle/HOL to study such meta-logical properties.

This formalization is atop the higher-order logic (HOL) fragment of Isabelle, which is a rich logic with extensive tooling, allowing for convenient reasoning about GD within HOL. However, it is desirable to formalize GD within a minimal base logic instead, as this essentially removes a layer of abstraction in the form of HOL as the meta-theory. With such a formalization, reasoning within the embedded GD logic is simpler and closer to the intended foundational principles, without being clouded by the language of a rich meta-logic. Such a development would also make GD more usable as a tool for automated reasoning itself.

This thesis seeks to realize such an implementation in Isabelle’s minimal base logic, _Pure_, which is designed for precisely such a task @isa.

The thesis aims to:

- Formalize the syntax of GD.
- Implement the deductive rules of GD: Axiomatize the inference system.
- Develop Grounded Arithmetic (GA): Build a basic arithmetic theory within GD.
- Construct encoded data structures: Implement finite datatypes such as lists and trees using purely arithmetical encodings over GA.
- Prototype definitional tooling: Create user-facing infrastructure for defining functions, data structures, and interpretations within GD, while reducing all such features to GA representations.

// == Methodology
// - Begin with a minimal GD.thy theory that imports only Pure, and defines syntactic entities.
// - Translate the formal rules of deduction from the GD specification into Isabelle axioms using axiomatization, ensuring no inference rule allows unrestricted evaluation or interpretation.
// - Represent grounded values and recursive interpretations using arithmetic encodings, avoiding Isabelle datatypes.
// - Encode and prove internal correctness of recursive definitions for pairing, sequences, and other basic structures.
// - Design macros or syntactic constructs to simulate native datatype and function definitions, while maintaining reduction to GA primitives.

== Bibliography
#bibliography("proposal.bib", title: none)
