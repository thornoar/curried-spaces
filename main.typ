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

== The language of filters

#def[
  Let $X$ be a set. A _filter_ on $X$ is a non-empty set $F subset 2^X$ which is closed under supersets and finite intersections, and does not contain the empty set. The set of all filters on $X$ will be denoted by $FF(X)$.
]

#def[
  Let $X$ be a set. A family $cal(B) subset 2^X$ is called a _filter base_ if it does not contain the empty set and is closed under finite intersection. The filter $[cal(B)]$ _generated_ by $cal(B)$ is defined as the collection of all supersets of sets from $cal(B)$.\
  If $cal(B) = {{x}}$ where $x in X$, the filter $[x] = [{{x}}]$ is called the _universal filter_ of $x$.\
  If $f : X -> Y$ is a map and $F in FF(X)$ is a filter on $X$, then ${f(A) mid(|) A in F}$ is a filter base that generates the _image filter_ denoted $f(F)$.
]

#def[
  Let $X$ be a topological space. Then we say that a filter $F$ on $X$ _converges_ to a point $x in X$, and write $F -> x$, if it contains all open neighborhoods of $x$.
]

#rem[
  The language of filters is expressive enough to encode all topological properties. For example @bou1:
  - A sequence ${x_n}_(n = 1)^oo$ converges to a point $x in X$ iff the filter
    $
      F = {A subset X mid(|) x_n in A "for all but finitely many" n}
    $
    converges to $x$. This filter $F$ is called the _derived filter_ of ${x_n}_(n = 1)^oo$.
  - A subset $E subset X$ is closed if for every point $x in E$ there is a filter $F in FF(X)$ converging to $x$ such that $A inter E != diameter$ for all $A in F$.
  - A topological space $X$ is compact iff every filter $F$ on $X$ is contained in a convergent filter on $X$.
  - A function $f : X -> Y$ between topological spaces is continuous iff it preserves convergent filters, i.e. $F -> x in X$ implies $f(F) -> f(x) in Y$.
]

#lm([see @bou1, page 74])[
  Let $X$ be a set and $f_i : X -> Y_i$ be a family of maps, where $Y_i$ are topological spaces. Let $X$ be endowed with the coarsest topology such that $f_i$ is continuous for each $i$. Then a filter $F in FF(X)$ converges to $x in X$ if and only if $f_i (F)$ converges to $f_i (x)$ for all $i$.
]

== The topology of pointwise convergence

#def([pointwise convergence topology, see @bou2])[
  Let $X$ be a set, $Y$ a topological space, and denote by $SS(X,Y)$ the set of functions from $X$ to $Y$. For each $x in X$ and each open set $U subset Y$, let $V(x, U)$ be the set of all functions $f in SS(X,Y)$ such that $f(x) in U$. The collection
  $
    {V(x,U) mid(|) x in X, U subset Y}
  $
  forms a subbase of a topology on $SS(X,Y)$, called the _topology of pointwise convergence._
]

#rem[
  Let $X$ be a set and $Y$ a topological space. It is not hard to see that a filter $F in FF(SS(X,Y))$ converges to a function $f in SS(X,Y)$ if and only if, for any $x in X$, the filter $F(x) = [{A(x) mid(|) A in F}]$ converges to $f(x) in Y$.
]

#lm[
  Let $X$ be a set and $Y$ a Hausdorff topological space. Then $SS(X,Y)$ is also Hausdorff.
] <pwhaus>
#pf[
  Consider two functions $f, g in SS(X,Y)$ such that $f != g$. This implies that there is $x_0 in X$ such that $f(x_0) != g(x_0)$. Since $Y$ is Hausdorff, there are neighborhoods $U_f in.rev f(x_0)$ and $U_g in.rev g(x_0)$ such that $U_f inter U_g = diameter$. It then follows that $f in V(x_0, U_f)$, $g in V(x_0, U_g)$, and $V(x_0, U_f) inter V(x_0, U_g) = diameter$.
]

#lm[
  Let $X$ be a set and let $Y$ be a real topological vector space. Then $SS(X,Y)$ is also a real topological vector space with respect to the topology of pointwise convergence and the pointwise linear structure.
] <pwtvs>
#pf[
  We need to show that the maps $+ : SS(X,Y) times SS(X,Y) -> SS(X,Y)$ and $dot : RR times SS(X,Y) -> SS(X,Y)$ are continuous.\
  To begin, consider two filters $F_1, F_2 in FF(SS(X,Y))$, converging to $f_1$ and $f_2$ respectively. To show that $F_1 + F_2$ converges to $f_1 + f_2$, consider $x in X$. We have
  $
    (F_1 + F_2)(x) &= [{(A + B)(x) mid(|) A in F_1, B in F_2}]\
    &= [{A(x) + B(x) mid(|) A in F_1, B in F_2}]\ 
    &= F_1 (x) + F_2 (x) -> f_1 (x) + f_2 (x) = (f_1 + f_2)(x).
  $
  This shows that the addition operation is continuous. Scalar multiplication is continuous by a similar argument.
]

== The compact-open topology

#def([compact-open topology, see @bou2])[
  Let $X$ and $Y$ be two topological spaces, and by $CC(X,Y)$ denote the set of all continuous functions from $X$ to $Y$. For each compact set $K subset X$ and each open set $U subset Y$, let $V(K,U)$ be the set of all functions $f in CC(X,Y)$ such that $f(K) subset U$. The collection
  $
  {V(K,U) mid(|) K subset X, U subset Y}
  $
  forms a subbase of a topology on $CC(X,Y)$, called the _compact-open_ topology.
]

#rem[
  Clearly, the topology of pointwise convergence on $CC(X,Y)$ is coarser than the compact-open topology.
]

#prop([see @bb])[
  Let $X$ and $Y$ be topological spaces such that $X$ is locally compact and $Y$ is regular. Then a filter $F in FF(CC(X,Y))$ converges to a function $f in CC(X,Y)$ if and only if, for any filter $P in FF(X)$ converging to $p in X$, we have $F(P) -> f(p)$ in $Y$, where the filter $F(P)$ is based on
  $
    {A(B) mid(|) A in F, B in P} = {{a(b) mid(|) a in A, b in B} mid(|) A in F, B in P}.
  $
]

#prop([see @bou2, page 302])[
  Let $X, Y, Z$ be topological spaces such that $X$ is Hausdorff and $Y$ is locally compact. Then the map
  $
    gamma : CC(X times Y, Z) -> CC(X, CC(Y, Z))
  $
  defined as $gamma(f)(x)(y) = f(x,y)$, is well-defined and is a homeomorphism.
] <curry>

#lm[
  Let $X, Y$ be topological spaces such that $Y$ is Hausdorff. Then the space $CC(X,Y)$ is also Hausdorff.
] <cohaus>
#pf[
  The compact-open topology on $CC(X,Y)$ is finer than the topology of pointwise convergence, and the latter is Hausdorff, which implies that the former is Hausdorff.
]

#lm[
  Let $X$ be a topological space and $Y$ a real topological vector space. Then $CC(X,Y)$ is also a real topological vector space with respect to the pointwise linear structure and the compact-open topology.
] <cotvs>
#pf[
  We will show that the map $+ : CC(X,Y) times CC(X,Y) -> CC(X,Y)$ is continuous. Let $F_1, F_2 in FF(CC(X,Y))$ converge to $f_1 in CC(X,Y)$ and $f_2 in CC(X,Y)$ respectively. For any filter $P in FF(X)$ converging to $p in X$, we have
  $
    (F_1 + F_2)(P) &= [{(A_1 + A_2)(B) mid(|) A_i in F_i, B in P}]\
    &supset [{A_1 (B_1) + A_2 (B_2) mid(|) A_i in F_i, B_i in P}]\
    &= F_1 (P) + F_2 (P) -> f_1 (p) + f_2 (p) = (f_1 + f_2)(p).
  $
  The continuity of scalar multiplication is proven similarly.
]

// #prop([see @bb, page 28])[
//   Let $X$ be a convergence space and let $Y$ be a Hausdorff convergence space (i.e. every filter in $Y$ converges to at most one point). Then $CC(X,Y)$ is also a Hausdorff convergence space.
// ] <haus>

// #prop([see @bb, page 29])[
//   Let $X$ be a convergence space and $Y$ be a convergence vector space, i.e. a set endowed with both structures such that the operations $+ : Y times Y -> Y$ and $dot : RR times Y -> Y$ are continuous. Then $CC(X,Y)$ is also a convergence vector space.
// ] <tvs>

#lm[
  Let $X, Y$ be topological spaces such that $X$ is first countable. Then a sequence ${f_k}_(k in NN) subset CC(X,Y)$ converges to a function $f in CC(X,Y)$ if and only if $f_k (x_k) st(k -> oo) f(x)$ whenever $x_k st(k -> oo) x$ in $X$.
] <simul>
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

= The spaces of curried functions

== General functions

#def[
  Let $n in NN_0 = {0, 1, 2, ...}$. The set $H_n (RR)$ of _curried $n$-variable functions_ is a topological vector space defined recursively as follows:
  - If $n = 0$, we set $H_0 (RR) = RR$;
  - If $H_n (RR)$ is defined, we let $H_(n+1) (RR)$ to be the set of all functions from $RR$ to $H_n (RR)$. This set is given the pointwise linear structure and the topology of pointwise convergence. @pwhaus and @pwtvs ensure that $H_(n+1)(RR)$ is a Hausdorff topological vector space.
]

#def[
  Let $tilde(f) : RR^n -> RR$ be a function. Define
  $
    gamma(tilde(f))(x_1)(x_2)...(x_n) = tilde(f)(x_1, x_2, ..., x_n).
  $
  Then $gamma : "Hom"(RR^n, RR) -> H_n (RR)$ is clearly a bijection. The function $f = gamma(tilde(f))$ will be called the _curried version_ of $tilde(f)$.
]

== Continuous functions

#def[
  Let $n in NN_0$. The set $C_n (RR)$ of _curried continuous functions_ is a Hausdorff topological vector space defined recursively as follows:
  - If $n = 0$, we set $C_0 (RR) = RR$.
  - If $C_n (RR)$ is defined, we set $C_(n+1) (RR) = CC(RR, C_n (RR))$, endowed with pointwise linear structure and the compact-open topology. @cohaus and @cotvs ensure that $C_(n+1)(RR)$ is a Hausdorff topological vector space, provided that $C_n (RR)$ is.
]

#exam[
  The topology on $C_n (RR)$ is finer than the topology induced from $H_n (RR)$, and does not coincide with it, unless $n = 0$. To see this, take $n = 1$ and consider the classical function
  $
    phi (x) = cases(
      exp(1/(abs(x)^2 - 1))\, #h(10pt)& abs(x) < 1,
      0\, & abs(x) >= 1.
    )
  $
  This is a $C^oo (RR)$ function supported on $[-1,1]$. Its graph looks as follows:
  #figure(
    image("./figures/bump.pdf")
  )
  Now consider the following sequence of functions:
  $
    f_k (x) = e dot phi(k dot (x - 1/k)).
  $
  Clearly, $f_k$ is infinitely differentiable on $RR$, supported on $[0,2\/k]$, and has a maximum at $x = 1\/k$ with $f_k (1\/k) = 1$. It is clear that for all $x in RR$, we have $f_k (x) st(k -> oo) 0$, so $f_k -> 0$ in the topology induced from $H_1 (RR)$. However, $f_k$ do not converge to $0$ in the native topology of $C_1 (RR)$. To see this, take $x_k = 1\/k$ and observe that $f_k (x_k) equiv 1 != 0$.\

  A similar argument applies for any other $n >= 2$. Hence we conclude that $C_n (RR)$ is not a subspace of $H_n (RR)$.
]

#prop[
  Let $n in NN_0$. Then the map
  $
    gamma : CC(RR^n, RR) -> C_n (RR)
  $
  defined by $gamma(f)(x_1)(x_2)...(x_n) = f(x_1, ..., x_n)$, is well-defined and is a homeomorphism.
] <cogamma>
#pf[
  If $n = 0$, the statement is trivial. Assume it is proven for $C_n (RR)$. By @curry, we have
  $
    CC(RR^(n+1), RR) = CC(RR times RR^n, RR) tilde.equiv CC(RR, CC(RR^n, RR)) tilde.equiv CC(RR, C_n (RR)) = C_(n+1)(RR),
  $
  q.e.d.
]

== Differentiable functions

#def[
  Let $n in NN_0$. The set $D_n (RR)$ of _curried differentiable functions_ is a topological vector space defined recursively as follows:
  - If $n = 0$, we set $D_0 (RR) = RR$, as usual;
  - If $D_n (RR)$ is defined for some $n$, we let $D_(n+1)(RR) subset CC(RR, D_n (RR))$ consist of all functions $f$ such that there is a function $f' in C_(n+1)(RR)$ (called the derivative of $f$) which satisfies
    $
      (f(x + h) - f(x))/h st(h -> 0) f'(x) in H_n (RR)
    $
    for all $x in RR$, where *the convergence is taken in the space $H_n (RR)$*. Clearly, if $f, g in D_(n+1)(RR)$ and $alpha, beta in RR$, we have
    $
      (alpha f + beta g)' = alpha f' + beta g',
    $
    so in particular, $alpha f + beta g in D_(n+1)(RR)$.\
    We endow $D_(n+1)(RR)$ with the coarsest topology in which the maps
    $
      i : D_(n+1)(RR) &-> CC(RR, D_n (RR)), #h(3cm) d : D_(n+1)(RR) -> C_(n+1)(RR) #<maps>\
      f &|-> f #h(6.81cm) f |-> f'
    $
    are continuous. This topology will be called the _differential topology._ We prove below that $D_(n+1)(RR)$ is a Hausdorff topological vector space.
]

#rem[
  It is clear that the map $i : D_n (RR) -> C_n (RR)$ is continuous, meaning that the topology on $D_n (RR)$ is finer than the topology induced from $C_n (RR)$.
]

#lm[
  For all $n in NN_0$, the topological space $D_n (RR)$ is Hausdorff.
] <diffhaus>
#pf[
  Since $C_n (RR)$ is Hausdorff and $i : D_n (RR) -> C_n (RR)$ is continuous, we see that $D_n (RR)$ is also Hausdorff.
]

#lm[
  For all $n in NN_0$, the linear and topological structures on $D_n (RR)$ are compatible, making $D_n (RR)$ a topological vector space.
] <difftvs>
#pf[
  We prove by induction over $n$. If $n = 0$, we have $D_0 (RR) = RR$ with the usual topology and linear structure. Suppose now that $D_(n-1)(RR)$ is a TVS. We need to establish the continuity of the following two maps:
  $
    + : D_n (RR) times D_n (RR) -> D_n (RR), #h(2cm) dot : RR times D_n (RR) -> D_n (RR).
  $
  In turn, by the definition of the differential topology, this task is equivalent to proving that the maps $i circ (+), d circ (+), i circ (dot), d circ (dot)$ are continuous, where the maps $i$ and $d$ are defined in (@maps).\
  To this end, note that we have commutative diagrams
  #centering(shallow: false)[
    #import "@preview/commute:0.3.0": *
    #let s1 = 2
    #let s2 = 1
    #let ll = 10pt
    #let pd = 1em
    #let np = (40pt, 40pt)
    #commutative-diagram(
      padding: pd, node-padding: np,
      node((0,0), $D_n (RR) times D_n (RR)$, "00"),
      node((0,s1), $D_n (RR)$, "01"),
      node((s2,0), $CC(RR, D_(n-1)(RR)) times CC(RR, D_(n-1)(RR))$, "10"),
      node((s2,s1), $CC(RR, D_(n-1)(RR))$, "11"),
      arr("00", "01", $(+)$, label-pos: ll),
      arr("00", "10", $i times i$, label-pos: -1.6*ll, "inj"),
      arr("01", "11", $i$, label-pos: 0.8*ll, "inj"),
      arr("10", "11", $(+)$, label-pos: -ll),
    )
    #v(1em)
    #commutative-diagram(
      padding: pd, node-padding: np,
      node((0,0), $D_n (RR) times D_n (RR)$, "00"),
      node((0,s1), $D_n (RR)$, "01"),
      node((s2,0), $C_n (RR) times C_n (RR)$, "10"),
      node((s2,s1), $C_n (RR)$, "11"),
      arr("00", "01", $(+)$, label-pos: ll),
      arr("00", "10", $d times d$, label-pos: -1.6*ll),
      arr("01", "11", $d$, label-pos: 0.8*ll),
      arr("10", "11", $(+)$, label-pos: -ll),
    )
    #v(1em)
    #commutative-diagram(
      padding: pd, node-padding: np,
      node((0,0), $RR times D_n (RR)$, "00"),
      node((0,s1), $D_n (RR)$, "01"),
      node((s2,0), $RR times CC(RR, D_(n-1)(RR))$, "10"),
      node((s2,s1), $CC(RR, D_(n-1)(RR))$, "11"),
      arr("00", "01", $(dot)$, label-pos: ll),
      arr("00", "10", $"id" times i$, label-pos: -1.8*ll, "inj"),
      arr("01", "11", $i$, label-pos: 0.8*ll, "inj"),
      arr("10", "11", $(dot)$, label-pos: -ll),
    )
    #v(1em)
    #commutative-diagram(
      padding: pd, node-padding: np,
      node((0,0), $RR times D_n (RR)$, "00"),
      node((0,s1), $D_n (RR)$, "01"),
      node((s2,0), $RR times C_n (RR)$, "10"),
      node((s2,s1), $C_n (RR)$, "11"),
      arr("00", "01", $(dot)$, label-pos: ll),
      arr("00", "10", $"id" times d$, label-pos: -1.8*ll),
      arr("01", "11", $d$, label-pos: 0.8*ll),
      arr("10", "11", $(dot)$, label-pos: -ll),
    )
  ]
  Since the down-then-right path in each diagram is continuous, the right-then-down paths are continuous as well, and we are done.
]

#th[
  Let $n in NN$. A curried function $f in H_n (RR)$ lies in the class $D_n (RR)$ if and only if its counterpart $tilde(f) : RR^n -> RR$ has continuous partial derivatives on $RR^n$. Moreover, for each $1 <= i <= n$, we have
  $
    (partial tilde(f))/(partial x_i)(x_1, x_2, ..., x_n) = f(x_1)...(x_(i-1))'(x_i)...(x_n).
  $ <difftrans>
] <diffgamma>
#pf[
  We employ induction over $n in NN_0$. If $n = 1$, the statement clearly holds. Now, consider $n >= 2$ and assume that the statement holds for $n-1$.\
  First, let $f in D_n (RR)$ and $(x_1, x_2, ..., x_n) in RR^n$. For $i >= 2$, we have
  $
    (partial tilde(f))/(partial x_i)(x_1, ..., x_n) &= lim_(h -> 0) (tilde(f)(x_1, ..., x_i + h, ..., x_n) - tilde(f)(x_1, ..., x_n))/h\
    &= lim_(h -> 0) (tilde(f(x_1))(x_2, ..., x_i + h, ..., x_n) - tilde(f(x_1))(x_2, ..., x_n))/h\
    &= (partial tilde(f(x_1)))/(partial x_i)(x_2, ..., x_n) = f(x_1)...(x_(i-1))'(x_i)...(x_n)
  $
  by the induction hypothesis, since $f(x_1) in D_(n-1)(RR)$. For the derivative with respect to $x_1$, we have
  $
    f'(x_1)(x_2)...(x_n) &= (lim_(h -> 0) (f(x_1 + h) - f(x_1))/h)(x_2)...(x_n)\
    &= lim_(h -> 0) (f(x_1+h)(x_2)...(x_n) - f(x_1)...(x_n))/h\
    &= lim_(h -> 0) (tilde(f)(x_1 + h, x_2, ..., x_n) - tilde(f)(x_1, ..., x_n))/h = (partial tilde(f))/(partial x_1)(x_1, ..., x_n),
  $
  so $partial tilde(f)\/partial x_1 = f'$, and we see that (@difftrans) holds. We also immediately observe that $partial tilde(f)\/partial x_1$ is continuous by @cogamma, since $f' in C_n (RR)$. It remains to show that the derivatives with respect to $x_2, ..., x_n$ are continuous. To this end, let $(h_1, ..., h_n) -> 0 in RR^n$. Since $D_n (RR) subset CC(RR, D_(n-1)(RR))$, the function $f : RR -> D_(n-1)(RR)$ is continuous, and so we have the convergence
  $
    f(x_1 + h_1) st(h_1 -> 0) f(x_1) in D_(n-1)(RR).
  $
  Now, since the map $d : D_(n-1)(RR) -> C_(n-1)(RR)$ is continuous, the above implies
  $
    f(x_1 + h_1)' st(h_1 -> 0) f(x_1)' in C_(n-1)(RR).
  $
  From here, by @simul, we have
  $
    &(partial tilde(f))/(partial x_2)(x_1 + h_1, ..., x_n + h_n)\
    = &f(x_1 + h_1)'(x_2 + h_2)...(x_n + h_n) st(#h(5pt) h_1\, h_2\, ... h_n -> 0 #h(5pt)) f(x_1)'(x_2)...(x_n) = (partial tilde(f))/(partial x_2)(x_1, ..., x_n).
  $
  A similar argument shows that the partial derivatives with respect to $x_3, ..., x_n$ are continuous as well.

  Now, we prove the other direction. Consider $f in H_n (RR)$ such that $tilde(f) : RR^n -> RR$ has continuous partial derivatives. To show that $f in D_n (RR)$, we follow three steps:
  + For all $x_1 in RR$, we have $f(x_1) in D_(n-1)(RR)$. This holds by the induction hypothesis, since $tilde(f(x_1)) : RR^(n-1) -> RR$ clearly has continuous partial derivatives, being a restriction of $tilde(f)$.
  + The function $f : RR -> D_(n-1)(RR)$ is continuous. To show this, consider a sequence ${x_k^((1))}_(k in NN) subset RR$ converging to $x_0^((1)) in RR$. We aim to prove that $f(x_k^((1))) -> f(x_0^((1)))$ in $D_(n-1)(RR)$. This is equivalent to showing that
    $
      f(x_k^((1))) -> f(x_k^((1))) in CC(RR, D_(n-2)(RR)) #h(10pt) "and" #h(10pt) f(x_k^((1)))' -> f(x_0^((1)))' in C_(n-1)(RR).
    $ <twocond>
    The latter of these conditions holds by the induction hypothesis, since
    $
      (partial tilde(f))/(partial x_2)(x_1, ..., x_n) = (partial tilde(f(x_1)))/(partial x_2)(x_2, ..., x_n) =_(#hs #[by (@difftrans)] #hs) f(x_1)'(x_2)...(x_n),
    $ <par2>
    and $partial tilde(f)\/partial x_2$ is continuous, which means that the map $x |-> f(x)'$ is continuous. To prove the former condition in (@twocond), we again consider a sequence $x_k^((2)) -> x_0^((2)) in RR$ and aim to prove
    $
      f(x_k^((1)))(x_k^((2))) -> f(x_0^((1)))(x_0^((2))) in D_(n-2)(RR),
    $
    which (unless $n = 2$) is again equivalent to
    $
      f(x_k^((1)))(x_k^((2))) -> f(x_k^((1)))(x_k^((2))) #h(10pt) "and" #h(10pt) f(x_k^((1)))(x_k^((2)))' -> f(x_0^((1)))(x_0^((2)))'.
    $
    The latter follows from the induction hypothesis and the continuity of $partial tilde(f)\/partial x_3$, similarly to (@par2), and the former can again be expanded further. This chain leads us finally to the convergence
    $
      f(x_k^((1)))(x_k^((2)))...(x_k^((n))) -> f(x_0^((1)))(x_0^((2)))...(x_0^((n))) in RR,
    $
    which is evident since $f in C_n (RR)$ by @cogamma. Hence we see that $f$ lies in $CC(RR, D_(n-1)(RR))$. We have also established (@difftrans) for $f$ and $i >= 2$, via (@par2).
  + Finally, we need to find $f' in C_n (RR)$ such that
    $
      (f(x + h) - f(x))/h st(h -> 0) f'(x) in H_(n-1)(RR)
    $ <conv>
    for all $x in RR$. Indeed, following (@difftrans), let us define $f' := gamma(partial tilde(f)\/partial x_1)$. We immediately see by (@cogamma) that $f'$ so defined lies in $C_n (RR)$. To see that (@conv) holds, consider $x_1, ..., x_n in RR$ and write
    $
      f'(x_1)(x_2)...(x_n) &= (partial tilde(f)/(partial x_1)(x_1, ..., x_n)\
      &= lim_(h -> 0) (tilde(f)(x_1 + h, x_2, ..., x_n) - tilde(f)(x_1, ..., x_n))/h\
      &= (lim_(h -> 0) (f(x_1 + h) - f(x_1))/h)(x_2)...(x_n),
    $
    and we are done.
]

#bibliography("bibliography.yml")
