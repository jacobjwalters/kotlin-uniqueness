// Kotlin Uniqueness
// Author: Jacob Walters

#set document(
  title: "Kotlin Uniqueness",
  author: "Jacob Walters",
)

#set page(paper: "a4")
//#set text(font: "New Computer Modern")
#set page(numbering: "1")
#set heading(numbering: "1.1")

// Hyperlinks
#show link: underline

// Import local definitions
#import "defs.typ": *

// Title
#align(center)[
  #text(size: 17pt, weight: "bold")[Kotlin Uniqueness]

  #v(0.5em)

  Jacob Walters

  #v(1em)
]

// Table of contents
#outline(indent: auto)

// Content
#pagebreak()
#include "sections/base.typ"

#pagebreak()
#include "sections/class.typ"

#pagebreak()
// Bibliography
#bibliography("refs.bib", title: "Bibliography", style: "apa")
