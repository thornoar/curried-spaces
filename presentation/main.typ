#import "@local/common:0.0.0"

#import "@local/theorem:0.0.0": *
#show: theorem-rule
#let definition = plainstyle("Definition")
#let notation = plainstyle("Notation")
#let example = plainstyle("Example")
#let exercise = plainstyle("Exercise")
#let note = plainstyle("Note")
#let remark = plainstyle("Remark")
#let theorem = statestyle("Theorem")
#let lemma = statestyle("Lemma")
#let proposition = statestyle("Proposition")
#let statement = statestyle("Statement")
#let problem = statestyle("Problem")
#let corollary = statestyle("Corollary")
#let proof = proofstyle()

#import "@preview/touying:0.7.3": *
#import themes.simple: *
#show: simple-theme.with(aspect-ratio: "16-9")

#set text(size: 28pt, font: "TeX Gyre Schola")

#import "@preview/cetz:0.5.2" as cz

= Curried Functional Spaces

== Premise

#cz.canvas(
  length: 1cm,
  {
    import cz.draw: *
    circle((0,0), radius: 4)
    
  }
)
