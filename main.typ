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

// #def[
//   A filter $F$ on $X$ is called an _ultrafilter_ if is not properly contained in any other filter. A standard application of Zorn's lemma shows that every filter in contained in at least one ultrafilter @bou. Moreover, for any filter $F in FF(X)$ we have
//   $
//     F = inter.big {G mid(|) G "is an ultrafilter and" F subset G}.
//   $
// ]

#def[
  Let $X$ be a set. A family $cal(B) subset 2^X$ is called a _filter base_ if it does not contain the empty set and is closed under finite intersection. The filter $[cal(B)]$ _generated_ by $cal(B)$ is defined as the collection of all supersets of sets from $cal(B)$.\
  If $cal(B) = {{x}}$ where $x in X$, the filter $[x] = [{{x}}]$ is called the _universal filter_ of $x$.\
  If $f : X -> Y$ is a map and $F in FF(X)$ is a filter on $X$, then ${f(A) mid(|) A in F}$ is a filter base that generates the _image filter_ denoted $f(F)$.
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
  - A topological space $X$ is compact iff every filter $F$ on $X$ is contained in a convergent filter on $X$.
  - A function $f : X -> Y$ between topological spaces is continuous iff it preserves convergent filters, i.e. $F -> x in X$ implies $f(F) -> f(x) in Y$.
]

#def[
  One may try to decouple the notion of convergent filters from topology. Let $X$ be a set with a relation $op(->) subset FF(X) times X$. Then $(X, ->)$ is called a _convergence space_ if
  - For all $x in X$, we have $[x] -> x$;
  - If $F -> x$ and $G -> x$, then $F inter G -> x$;
  - If $F -> x$ and $F subset G$, then $G -> x$.
]

#def[
  A map $f : X -> Y$ between convergence spaces is said to be _continuous_ if $f(F) -> f(x) in Y$ whenever $F -> x in X$.
]

#def[
  Let $X, Y$ be two convergence spaces. Then the product $X times Y$ can be endowed with the following convergence structure: a filter $F in FF(X times Y)$ converges to $(x,y) in X times Y$ if and only if $p_X (F) -> x in X$ and $p_Y (F) -> y in Y$.
]

#def[
  Let $X, Y$ be convergence spaces. By $CC(X,Y)$ denote the set of all continuous functions from $X$ to $Y$. Then $CC(X,Y)$ can be endowed with a convergence structure as follows. For a filter $F in FF(CC(X,Y))$, we say that $F -> f in CC(X,Y)$ if and only if $F(P) -> f(p)$ whenever $P -> p in X$. Here, the filter $F(P)$ is based on
  $
    {A(B) mid(|) A in F, B in P} = {{a(b) mid(|) a in A, b in B} mid(|) A in F, B in P}.
  $
  The resulting convergence structure on $CC(X,Y)$ is called the structure of _continuous convergence._
] <cxydef>

#rem[
  Continuous convergence on $CC(X,Y)$ is the coarsest convergence structure that makes the _evaluation mapping_
  $
    omega : CC(X,Y) times X -> Y
  $
  continuous. Here, the product $CC(X,Y) times X$ is endowed with the product convergence structure.
]

#prop([see @bb, page 26])[
  Let $X, Y, Z$ be convergence spaces. Then a map $h : X -> CC(Y, Z)$ is continuous if and only if the associated map
  $
    tilde(h) : X times Y -> Z
  $
  defined by $tilde(h)(x, y) = h(x)(y)$, is continuous.
] <convcurry>
#pf[
  Assume that $h$ is continuous. To show the continuity of $tilde(h)$, it suffices to take two convergent filters $F -> x in X$ and $G -> y in Y$, and show that $tilde(h)(F times G) -> tilde(h)(x,y)$, where the filter $F times G$ is based on ${A times B mid(|) A in F, B in G}$. Indeed, we have
  $
    tilde(h)(F times G) = h(F)(G) -> h(x)(y) = tilde(h)(x,y),
  $
  since $h(F) -> h(x)$ by the continuity of $h$. The converse is proven similarly.
]

#prop([see @bb, page 34])[
  Let $X, Y$ be topological spaces such that $X$ is locally compact and $Y$ is regular. Then the convergence space $CC(X,Y)$ is topologized by the compact-open topology. That is, the convergence relation arising from this topology coincides precisely with the convergence structure given in @cxydef.
]

= Curried functional spaces

#prop[
  Let $X, Y$ be topological spaces such that $X$ is first countable. Then a sequence ${f_k}_(k = 1)^oo subset CC(X,Y)$ converges to a function $f in CC(X,Y)$ (in the sense that its derived filter converges) if and only if $f_k (x_k) st(k -> oo) f(x)$ whenever $x_k st(k -> oo) x$ in $X$.
]
#pf[
  First, let $F$ be the derived filter of ${f_k}_(k = 1)^oo$ and suppose that $F$ converges to a function $f in CC(X,Y)$. Consider a sequence ${x_k}_(k = 1)^oo$ converging to $x in X$.
]

#bibliography("bibliography.yml")
