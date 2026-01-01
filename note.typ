#import "@preview/ctheorems:1.1.3": *
#import "@preview/codelst:2.0.2": sourcecode, sourcefile
#import "@preview/equate:0.2.1": equate

#let title = [Gödel's God in Lean 4]
#let authors = (
  (name: "SnO2WMaN", github: "SnO2WMaN"),
)

#set document(title: title, author: authors.map(a => a.name).join(", "))
#set page(numbering: "1", number-align: center)

#set heading(numbering: "1.")
#show heading: set text(font: "Nimbus Sans")
#show heading.where(level: 1): set text(size: 18pt)
#show heading.where(level: 2): set text(size: 14pt)

#set text(size: 10pt, font: "Nimbus Roman")
#set par(justify: false)

#set cite(form: "normal")

#text(size: 20pt, weight: "bold", font: "Nimbus Sans")[#title]

#pad(grid(
  gutter: .5em,
  ..authors.map(author => [
    #text(size: 12pt, font: "Nimbus Sans", author.name)
    #text(size: 10pt, font: "JuliaMono")[\@#author.github]
  ]),
))


= Intoduction

*First of All, Termiology Remark*:
Since they are denoted similar notion, we select carefully the word _mechanize_ and _formalize_.
If we used _mechanize_, it intends to verify the argument by computer i.e. proof assistant.
Otherwise, we use _formalize_ to mean to translate the argument into usual formal languages, in other word, symbolic logic or other usual mathematical means.


In @Pal22, Palalansoukî mechanized the argument of Gödel's God by Lean 3.
We rewrite into Lean 4.

Gödel's ontological proof is published in 3rd volume of Gödel's collected works @GödCW3 (Hand written version is collected @Sob03GödNote in @Sob03)

@Fit02

Scott's variant of Gödel's proof is @Sob03ScoNote in @Sob03.
Later, we mechanize this variant in @sect:Scott.



= Related Mechanization

Here is the list of related mechanizations of Gödel's ontological proof.

== Isabelle

@BP13A, @Ben20, @BS25A for @BS25

== Lean

Mechanization Scott's argument by Lean3 in @Pal22.

= Scott's Variant <sect:Scott>

#bibliography("references.yml", style: "elsevier-harvard")
