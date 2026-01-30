#import "@local/common:0.0.0": *
#import "@local/theorem-shorthands-en:0.0.0": *
#import "@preview/equate:0.3.1": equate
#show: theorem

#set page("a4", margin: 1in, numbering: "1")
#set text(font: "TeX Gyre Schola")
#set heading(numbering: "1.")

#set math.equation(numbering: "(1)", supplement: none)
#show: equate.with(sub-numbering: false, number-mode: "label")

#let st(cnt, class: []) = $stretch(->)_(#cnt)^(#class)$
#let nn(X) = $cal(N)(#X)$
#let SS = $cal(S)$
#let CC = $cal(C)$
#let FF = $cal(F)$

#align(center)[
  #text(size: 22pt)[*Continuous Convergence and Curried Functional Spaces*]
  #v(.5in)
]

= Preliminary definitions

#def[
  Let $X$ be a set. A _filter_ on $X$ is a non-empty set $F subset 2^X$ which is closed under supersets and finite intersections, and does not contain the empty set. The set of all filters on $X$ will be denoted by $FF(X)$.
]

#def[
  A filter $F$ on $X$ is called an _ultrafilter_ if is not properly contained in any other filter. A standard application of Zorn's lemma shows that every filter in contained in at least one ultrafilter @bou. Moreover, for any filter $F in FF(X)$ we have
  $
    F = inter.big {G mid(|) G "is an ultrafilter and" F subset G}.
  $
]

#def[
  Let $X$ be a topological space. Then we say that a filter $F$ on $X$ _converges_ to a point $x in X$, and write $F -> x$, if it contains all open neighborhoods of $x$.
]

#rem[
  The language of filters is expressive enough to encode all topological properties. For example @bou:
  - A sequence ${x_n}_(n = 1)^oo$ converges to a point $x in X$ iff the filter
    $
      F = {A subset X mid(|) x_n in A "for all but finitely many" n}
    $
    converges to $x$. This filter $F$ is called the _derived filter_ of ${x_n}_(n = 1)^oo$.
  - A subset $E subset X$ is closed if for every point $x in E$ there is a filter $F in FF(X)$ converging to $x$ such that $A inter E != diameter$ for all $A in F$.
  - A function $f : X -> Y$ between topological spaces is continuous iff it preserves convergent filters, i.e. $F -> x in X$ implies $f(F) -> f(x) in Y$.
]

#def[
  Let $X, Y$ be topological spaces. By $CC(X,Y)$ denote the set of all continuous functions from $X$ to $Y$. 
]

#bibliography("bibliography.yml")
