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

#prop([see @bb, page 27])[
  Let $X, Y, Z$ be convergence spaces. Then the map
  $
    gamma : CC(X times Y, Z) -> CC(X, CC(Y, Z))
  $
  defined as $gamma(f)(x)(y) = f(x,y)$, is well-defined and is a homeomorphism.
] <convcurry>

#prop([see @bb, page 34])[
  Let $X, Y$ be topological spaces such that $X$ is locally compact and $Y$ is regular. Then the convergence space $CC(X,Y)$ is topologized by the compact-open topology. That is, the convergence relation arising from this topology coincides precisely with the convergence structure given in @cxydef.
] <top>

#prop[
  Let $X$ be a convergence space and let $Y$ be a Hausdorff convergence space (i.e. every filter in $Y$ converges to at most one point). Then $CC(X,Y)$ is also a Hausdorff convergence space.
] <haus>

#prop([see @bb, page 29])[
  Let $X$ be a convergence space and $Y$ be a convergence vector space, i.e. a set endowed with both structures such that the operations $+ : Y times Y -> Y$ and $dot : RR times Y -> Y$ are continuous. Then $CC(X,Y)$ is also a convergence vector space.
] <cvs>

#cor[
  If $X$ is a topological space and $Y$ is a topological vector space, then $CC(X,Y)$ is a topological vector space.
] <cor1>

= Curried continuous functions

#prop[
  Let $X, Y$ be topological spaces such that $X$ is first countable. Then a sequence ${f_k}_(k in NN) subset CC(X,Y)$ converges to a function $f in CC(X,Y)$ (in the sense that its derived filter converges) if and only if $f_k (x_k) st(k -> oo) f(x)$ whenever $x_k st(k -> oo) x$ in $X$.
]
#pf[
  First, let $F$ be the derived filter of ${f_k}_(k in NN)$ and suppose that $F$ converges to a function $f in CC(X,Y)$. Consider a sequence ${x_k}_(k in NN)$ converging to $x in X$, with its derived filter $P$. Now let $V$ be a neighborhood of $f(x)$ in $Y$. By the definition of continuous convergence, we have $F(P) -> f(x)$, and so $V in F(P)$. This means that $V$ contains an element of the base of $F(P)$, namely a set
  $
    B_(n_0, m_0) = {f_n (x_m) mid(|) n >= n_0, hs m >= m_0}.
  $
  Hence, for $k >= max(n_0\, m_0)$, we have $f_k (x_k) in V$, as desired.\

  Conversely, suppose that $f_k (x_k) st(k -> oo) f(x)$ whenever $x_k st(k -> oo) x in X$. First let us show that for any subsequence ${f_(n_k)}_(k in NN)$, we have $f_(n_k)(x_k) st(k -> oo) f(x)$.\
  To this end, let $n in NN$. We let $z_n = x_(phi(n))$, where $phi(n)$ is the minimal number of those $k in NN$ that satisfy $n <= n_k$. We clearly see that $n_1 >= n_2$ implies $phi(n_1) >= phi(n_2)$ and that $phi(n_k) = k$ for all $k in NN$. Therefore, the sequence ${z_n}_(n in NN)$ converges to $x$. Hence we have $f_k (z_k) st(k -> oo) f(x)$, and so
  $
    f_(n_k) (x_k) = f_(n_k) (z_(n_k)) st(k -> oo) f(x).
  $ <subseq>
  Now, to show that $f_k -> f$ in $CC(X,Y)$, we need to show that the derived filter $F$ generated by the sets $C_n = {f_k mid(|) k >= n}$ converges to $f$. To this end, let $P$ be a filter in $X$ converging to a point $x in X$. Note that since $X$ is first countable, the filter $P$ has a countable base ${A_m}_(m in NN)$ of neighborhoods of $x$. To show that $F(P)$ converges to $f(x)$, assume the contrary. Then some neighborhood $V$ of $f(x)$ does not lie in $F(P)$, which is to say that for all $n, m in NN$, we have $C_n (A_m) subset.not V$. That means that for all $n,m in NN$, there are $k_m >= m$ and $x_m in A_m$ such that $f_(k_n)(x_m) in.not V$.\
  In particular, we have $f_(k_n)(x_n) in.not V$ for all $n in NN$. At the same time, since the sets $A_n$ generate $P$, we see that $x_n st(n -> oo) x$, so we must have $f_(k_n)(x_n) st(n -> oo) f(x)$ by (@subseq), a contradiction.
]

#def[
  Let $n in NN_0 = {0, 1, 2, ...}$. The _space of curried continuous functions_ $C_n (RR)$ is a Hausdorff topological vector space defined recursively as follows:
  - If $n = 0$, we set $C_0 (RR) = RR$.
  - If $C_n (RR)$ is defined, we set $C_(n+1) (RR) = CC(RR, C_n (RR))$. @top, @haus, and @cor1 ensure that $C_(n+1)(RR)$ is a Hausdorff topological vector space, provided that $C_n (RR)$ is.
]

// #prop[
//   For all $n in NN_0$, the space $C_n (RR)$ is a Hausdorff topological vector space.
// ]
// #pf[
//   If $n = 0$, the statement is trivial. Suppose that $C_n (RR)$ is a Hausdorff TVS. We aim to show the same for $C_(n+1)(RR)$.
//
//   Since $RR$ is locally compact and $C_n (RR)$ is regular, we see by @top that the convergence space $CC(RR, C_n (RR))$ is topological. It is given the pointwise vector space structure, i.e.
//     $
//       (alpha f + beta g)(x) = alpha f(x) + beta g(x)
//     $
//     for $alpha, beta in RR$ and $f, g in C_(n+1)(RR)$.\
//     First of all, as proved in @bb (page 28), we see that $C_(n+1)(RR)$ is Hausdorff. It remains to show that the addition and scalar multiplication maps are continuous.\
//
//     Consider the addition map $+ : C_(n+1)(RR) times C_(n+1)(RR) -> C_(n+1)(RR)$. Let $F_1 -> f_1$ and $F_2 -> f_2$ in $C_(n+1)(RR)$. We aim to show that $F_1 + F_2 -> f_1 + f_2$, where $F_1 + F_2$ is a shorthand for $(+)(F_1 times F_2)$. To this end, let $P -> x in RR$. Observe that we have $F_1 (P) -> f_1 (x)$ and $F_2 (P) -> f_2 (x)$ since $f_i in CC(RR, C_n (RR))$. Moreover, since $C_n (RR)$ is a TVS, we see that
//     $
//       F_1 (P) + F_2 (P) -> f_1 (x) + f_2 (x) = (f_1 + f_2)(x).
//     $
//     It remains to show that $(F_1 + F_2)(P)$ is finer than $F_1 (P) + F_2 (P)$. For $i = 1,2$, let\ $C_i in F_i$ and $A_i in P$. We then see that
//     $
//       C_1 (A_1) + C_2 (A_2) supset (C_1 + C_2)(A_1 inter A_2).
//     $
//     Therefore, we have
//     $
//       F_1 (P) + F_2 (P) &= [{C_1 (A_1) + C_2 (A_2) mid(|) C_i in F_i wh A_i in P}]\
//       &subset [(C_1 + C_2)(A) mid(|) C_i in F_i wh A in P] = (F_1 + F_2)(P),
//     $
//     and so $(F_1 + F_2)(P) -> (f_1 + f_2)(x)$, which allows us to conclude that
//     $
//       F_1 + F_2 -> f_1 + f_2 in C_(n+1)(RR).
//     $
//
//     Finally, consider the multiplication map $dot : RR times C_(n+1)(RR) -> C_(n+1)(RR)$. Let $P -> alpha in RR$ and $F -> f in C_(n+1)(RR)$. To show that $P dot F -> alpha f$, take a filter $Q -> x in RR$. One can easily show that $(P F)(Q) = P dot F(Q)$, and, since $dot : RR times C_n (RR) -> C_n (RR)$ is continuous, we have
//     $
//       (P F)(Q) = P dot (F(Q)) -> alpha dot f(x) = (alpha f)(x),
//     $
//     q.e.d.
// ]

#prop[
  Let $n in NN_0$. Then the map
  $
    gamma : CC(RR^n, RR) -> C_n (RR)
  $
  defined by $gamma(f)(t_1)(t_2)...(t_n) = f(t_1, ..., t_n)$, is well-defined and is a homeomorphism.
]
#pf[
  If $n = 0$, the statement is trivial. Assume it is proven for $C_n (RR)$. By @convcurry, we have
  $
    CC(RR^(n+1), RR) = CC(RR times RR^n, RR) tilde.equiv CC(RR, CC(RR^n, RR)) tilde.equiv CC(RR, C_n (RR)) = C_(n+1)(RR),
  $
  q.e.d.
]

= Curried differentiable functions

#bibliography("bibliography.yml")
