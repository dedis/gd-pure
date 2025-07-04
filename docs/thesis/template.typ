#import "@preview/codelst:2.0.2": *
#import "@preview/hydra:0.6.1": hydra

#let std-bibliography = bibliography
#let template(
  title-page: none,
  title: none,
  thesistype: none,
  author: none,
  email: none,
  supervisors: none, 
  institute: none,
  date: none,
  abstract: none,
  appendix: none,
  bibliography: none,
  bib-style: "ieee",
  math-numbering: "(1)",
  date-format: "[day].[month].[year]",
  body,
) = {
  // ===================
  // Global Settings
  // ===================
  set par(justify: true)
  let body-font = "New Computer Modern"
  let body-size = 11pt
  let heading-font = "New Computer Modern"
  let h1-size = 20pt
  let h2-size = 11pt
  let h3-size = 11pt
  let h4-size = 11pt
  let page-grid = 13.6pt

  let in-frontmatter = state("in-frontmatter", true)    // to control page number format in frontmatter
  let in-body = state("in-body", true)                  // to control heading formatting in/outside of body

  // customize look of figure
  set figure.caption(separator: [ --- ], position: bottom)

  // math numbering
  set math.equation(numbering: math-numbering)

  title-page()

  // Reset page numbering and start the main content.
  // pagebreak()
  set page(numbering: "1 / 1")
  counter(page).update(1)
  
  set text(
    font: body-font, 
    lang: "en", 
    size: body-size - 0.5pt,
    top-edge: 0.75 * body-size, 
    bottom-edge: -0.25 * body-size,
    fill: luma(0),
  )
  set par(
    spacing: page-grid,
    leading: page-grid - body-size, 
    justify: true,
  )

  set page(
    paper: "a4",
    margin: (
      top: 2.5cm,
      bottom: 3.0cm,
      left: 3.0cm + 5mm,
      right: 2.5cm,
    ),
    header:
      grid(
        columns: (1fr, 1fr),
        align: (left, right),
        row-gutter: 0.5em,
        smallcaps(text(font: heading-font, size: body-size, 
          context {
            hydra(1, display: (_, it) => it.body, use-last: true, skip-starting: false)
          },
        )),
        text(font: heading-font, size: body-size, 
          number-type: "lining",
          context {if in-frontmatter.get() {
              counter(page).display("i")      // roman page numbers for the frontmatter
            } else {
              counter(page).display("1")      // arabic page numbers for the rest of the document
            }
          }
        ),
        grid.cell(colspan: 2, line(length: 100%, stroke: 0.5pt)),
      ),
      header-ascent: page-grid,
  )


  // ========== FRONTMATTER ===================================
  
  // ---------- Heading Format (Part I) -----------------------

  show heading: set text(weight: "bold", font: heading-font)
  show heading.where(level: 1): it => {v(2 * page-grid) + text(size: 2 * page-grid, it)}

  // ---------- Abstract --------------------------------------

  heading(level: 1, numbering: none, outlined: false, "Abstract")
  text(abstract)
  pagebreak()

  // ---------- ToC (Outline) ---------------------------------

  // top-level TOC entries in bold without filling
  show outline.entry.where(level: 1): it => {
    set block(above: page-grid)
    set text(font: heading-font, weight: "semibold", size: body-size)
    link(
      it.element.location(),    // make entry linkable
      it.indented(it.prefix(), it.body() + box(width: 1fr,) +  it.page())
    )
  }

  // other TOC entries in regular with adapted filling
  show outline.entry.where(level: 2).or(outline.entry.where(level: 3)): it => {
    set block(above: page-grid - body-size)
    set text(font: heading-font, size: body-size)
    link(
      it.element.location(),  // make entry linkable
      it.indented(
          it.prefix(),
          it.body() + "  " +
            box(width: 1fr, repeat([.], gap: 2pt), baseline: 30%) +
            "  " + it.page()
      )
    )
  }

  outline(
    title: "Contents",
    indent: auto,
    depth: 3,
  )

  in-frontmatter.update(false)  // end of frontmatter
  counter(page).update(0)       // so the first chapter starts at page 1 (now in arabic numbers)

  // ========== DOCUMENT BODY =================================

  // ---------- Heading Format (Part II: H1-H4) ---------------

  set heading(numbering: "1.1.1")

  show heading: it => {
    set par(leading: 4pt, justify: false)
    text(it, top-edge: 0.75em, bottom-edge: -0.25em)
    v(page-grid, weak: true)
  }

  show heading.where(level: 1): it => {
    set par(leading: 0pt, justify: false)
    pagebreak()
    context{ 
      if in-body.get() {
        v(page-grid * 1.5)
        place(
          top + right,
          //dx: 25pt, // move further right, adjust as needed
          dy: page-grid * 0.55,         // no vertical shift
          text(counter(heading).display(), 
            top-edge: "bounds",
            size: h1-size, weight: 0, luma(43.53%),
            font: "New Computer Modern Math" 
          )
        )
        text(               // heading text on separate line
          it.body, size: h1-size,
          top-edge: 0em, 
          bottom-edge: 0em,
        )
      } else {
        v(2 * page-grid) 
        text(size: 2 * page-grid, counter(heading).display() + h(0.5em) + it.body)   // appendix
      }
    }
  }

  show heading.where(level: 2): it => {v(16pt) + text(size: h2-size, it)}
  show heading.where(level: 3): it => {v(16pt) + text(size: h3-size, it)}
  show heading.where(level: 4): it => {v(16pt) + smallcaps(text(size: h4-size, weight: "semibold", it.body))}

 // ---------- Body Text ---------------------------------------

  body


  // ========== APPENDIX ========================================

  in-body.update(false)
  set heading(numbering: "A.1")
  counter(heading).update(0)

  // ---------- Bibliography ---------------------------------------

  show std-bibliography: set heading(numbering: "A.1")
  if bibliography != none {
    set std-bibliography(
      title: "References",
      style: bib-style,
    )
    bibliography
  }

  // ---------- Appendix (other contents) ---------------------

  if (appendix != none) {
    appendix
  }

  // ========== LEGAL BACKMATTER ==============================

  set heading(numbering: it => h(-18pt) + "", outlined: false)

  // ---------- Confidentiality Statement ---------------------
}
