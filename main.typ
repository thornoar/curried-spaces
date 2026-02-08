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

= The language of filters

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

= Curried functions

#def[
  Let $n in NN_0 = {0, 1, 2, ...}$. The set $H_n (RR)$ of _curried $n$-variable functions_ is a topological vector space defined as follows:
  - If $n = 0$, we set $H_0 (RR) = RR$;
  - If $H_n (RR)$ is defined, we define $H_(n+1) (RR)$ to be the set of all functions from $RR$ to $H_n (RR)$. This set is given the pointwise topological and linear structure. In other words, a filter $F in FF(H_(n+1)(RR))$ converges to $f in H_(n+1)(RR)$ if and only if $F(x) = {A(x) mid(|) A in F}$ converges to $f(x)$ for all $x in RR$. It is not hard to see that this topology is compatible with the pointwise vector structure.
]

#def[
  Let $tilde(f) : RR^n -> RR$ be a function. Define
  $
    gamma(tilde(f))(x_1)(x_2)...(x_n) = tilde(f)(x_1, x_2, ..., x_n).
  $
  Then $gamma : "Hom"(RR^n, RR) -> H_n (RR)$ is clearly a bijection. The function $f = gamma(tilde(f))$ will be called the _curried version_ of $tilde(f)$.
]

= Continuous functions

#prop([see @bb, page 34])[
  Let $X,Y$ be topological spaces such that $X$ is locally compact and $Y$ is regular. On the set of continuous functions $CC(X,Y)$, consider the compact-open topology (see @fox). Then a filter $F in FF(CC(X,Y))$ converges to a function $f in CC(X,Y)$ if and only if $F(P) -> f(p)$ whenever $P -> p in X$. Here, the filter $F(P)$ is based on
  $
    {A(B) mid(|) A in F, B in P} = {{a(b) mid(|) a in A, b in B} mid(|) A in F, B in P}.
  $
  The convergence $F -> f$ so defined is called _continuous convergence._
] <top>

In what follows, we assume that $X$ is a locally compact topological space and $Y$ is a regular topological space.

#prop([see @bb, page 27])[
  If $Y$ is locally compact and $Z$ is another regular topological space, then the map
  $
    gamma : CC(X times Y, Z) -> CC(X, CC(Y, Z))
  $
  defined as $gamma(f)(x)(y) = f(x,y)$, is well-defined and is a homeomorphism.
] <convcurry>

#prop[
  Let $X$ be a locally compact topological space and let $Y$ be a Hausdorff topological space (i.e. every filter in $Y$ converges to at most one point). Then $CC(X,Y)$ is also a Hausdorff topological space.
] <haus>

#prop([see @bb, page 29])[
  Let $X$ be a locally compact space and $Y$ be a regular topological vector space, i.e. a set endowed with both topological and linear structures such that the operations $+ : Y times Y -> Y$ and $dot : RR times Y -> Y$ are continuous. Then $CC(X,Y)$ is also a topological vector space.
] <tvs>

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
  - If $C_n (RR)$ is defined, we set $C_(n+1) (RR) = CC(RR, C_n (RR))$. @top, @haus, and @tvs ensure that $C_(n+1)(RR)$ is a Hausdorff topological vector space, provided that $C_n (RR)$ is.
]

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

= Differentiable functions

#def[
  Let $n in NN_0$. The _space of curried differentiable functions_ $D_n (RR)$ is a Hausdorff topological vector space defined recursively as follows:
  - If $n = 0$, we set $D_0 (RR) = C_0 (RR) = RR$.
  - If the space $D_n (RR)$ is defined, we define $D_(n+1) (RR)$ as the subspace of $CC(RR, D_n (RR))$ consisting of such functions $f : RR -> D_n (RR)$, that there is $f' in C_(n+1)(RR)$ which satisfies
    $
      f(x_0 + h) = f(x_0) + h dot f'(x_0) + o(h) in C_n (RR)
    $
    for all $x_0 in RR$.
]

#prop[
  Let $n in NN_0$. Then the map
  $
    gamma : C^1 (RR^n) -> D_n (RR)
  $
  is well-defined and a homeomorphism. In particular, a function $f in C_n (RR)$ lies in $D_n (RR)$ if and only if its counterpart $tilde(f) = gamma^(-1)(f) : RR^n -> RR$ has continuous partial derivatives.
]
#pf[
  First let us show that $gamma$ is well-defined and bijective. 
]

#def[
  Fix $n in NN_0$. For all $m in NN$, the _space of curried $m$ times differentiable functions_ $D_n^m (RR)$ is defined recursively as follows:
  - If $m = 1$, we set $D_n^1 (RR) = D_n (RR)$.
  - If $D_n^m (RR)$ is defined, we set $D_n^(m+1)(RR)$ to be the space of all functions $f in D_n (RR)$ such that $f' in D_n^m (RR)$.
  Trivially, for all $n in NN_0$, we have
  $
    D_n^1 (RR) supset D_n^2 (RR) supset D_n^3 (RR) supset ... 
  $
]

#prop[
  Let $n,m in NN$. Then a function $f in C_n (RR)$ lies in the differentiability class $D_n^m (RR)$ if its counterpart $tilde(f) = gamma^(-1)(f) : RR^n -> RR$ lies in the class $C^m (RR)$.
]

#prop[
  Let $n, m in NN$, and $f in D_n^m (RR)$. Then for all $x in RR$, we have $f(x) in D_(n-1)^m (RR)$.
]
#pf[
  ...
]

#bibliography("bibliography.yml")
