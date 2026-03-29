#import "@local/common:0.0.0": *
#import "@preview/equate:0.3.1": equate
#import "@preview/commute:0.3.0": *

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

#set page("a4", margin: (top: 0.5in, bottom: 0.7in, right: 0.5in, left: 0.5in), numbering: "1")
#set text(size: 11pt, font: "TeX Gyre Schola")
#set heading(numbering: "1.1", hanging-indent: 10pt)
#show heading: it => {
  counter(heading).display()
  h(12pt)
  it.body
}

#set math.equation(numbering: "(1)", supplement: none)
#show: equate.with(sub-numbering: false, number-mode: "label")

#let st(cnt, class: []) = $stretch(->)_(#cnt)^(#class)$
#let nn(X) = $cal(N)(#X)$
#let SS = $cal(S)$
#let CC = $cal(C)$
#let FF = $cal(F)$
#let fr = [Fréchet]

#align(center)[
  #text(size: 22pt)[*Continuous Convergence and Curried Functional Spaces*]
  #v(.5in)
]

= Introduction <intro>

There are essentially two ways to represent a multivariable function. One is to complicate the domain, in which case we write $f : A times B -> C$, and the other is to complicate the codomain by writing $g : A -> C^B$, such that $g(a)$ is again a function that maps $B$ to $C$. In programming, the latter approach is called _partial application_ or _currying,_ and we will adopt this terminology here.\
Classical multivariable calculus is built on the former, "uncurried" approach to defining functions of multiple arguments, and in this paper we build the theory of real multivariable calculus based on curried function spaces.\
We will be using the topological language of _filters_ throughout the work, to simplify proofs. For the definition and properties of filters, see @filapp.

= Definitions of curried spaces

== General functions

First, we introduce the most inclusive spaces of curried functions, endowed with the topology of pointwise convergence.

#definition([pointwise convergence topology, see @bou2, page 277])[
  Let $X$ be a set, $Y$ a topological space, and denote by $SS(X,Y)$ the set of functions from $X$ to $Y$. For each $x in X$ and each open set $U subset Y$, let $V(x, U)$ be the set of all functions $f in SS(X,Y)$ such that $f(x) in U$. The collection
  $
    {V(x,U) mid(|) x in X, U subset Y}
  $
  forms a subbase of a topology on $SS(X,Y)$, called the _topology of pointwise convergence._ A filter $F in FF(SS(X,Y))$ will converge to a function $f in SS(X,Y)$ if and only if $F(x)$ converges to $f(x) in Y$ for all $x in X$.
]

#proposition([see @bou2, page 281])[
  Let $X$ be a set and $Y$ a Hausdorff topological space. Then $SS(X,Y)$ is also Hausdorff.
] <pwhaus>
// #proof[
//   Consider two functions $f, g in SS(X,Y)$ such that $f != g$. This implies that there is $x_0 in X$ such that $f(x_0) != g(x_0)$. Since $Y$ is Hausdorff, there are neighborhoods $U_f in.rev f(x_0)$ and $U_g in.rev g(x_0)$ such that $U_f inter U_g = diameter$. It then follows that $f in V(x_0, U_f)$, $g in V(x_0, U_g)$, and $V(x_0, U_f) inter V(x_0, U_g) = diameter$.
// ]

#definition[
  Let $n in NN_0 = {0, 1, 2, ...}$. The set $H_n (RR)$ of _curried $n$-variable functions_ is a topological vector space defined recursively as follows:
  - If $n = 0$, we set $H_0 (RR) = RR$;
  - If $H_n (RR)$ is defined, we let $H_(n+1) (RR)$ to be the set of all functions from $RR$ to $H_n (RR)$. This set is given the pointwise linear structure and the topology of pointwise convergence, such that a filter $F in FF(H_(n+1)(RR))$ converges to a function $f in H_(n+1)(RR)$ if and only if $F(x) -> f(x) in H_n (RR)$ for all $x in RR$. @pwhaus and @pwtvs ensure that $H_(n+1)(RR)$ is a Hausdorff topological vector space.
]

== Continuous functions

Next, we define the spaces $C_n (RR)$ of continuous curried functions. Since the continuity of a function depends on the topology of the codomain, and since curried spaces are defined inductively, we see that the choice of _topology_ on $C_n (RR)$ influences which functions are included in $C_(n+1)(RR)$. A natural choice is the _compact-open topology,_ since, if $CC(X,Y)$ is the space of continuous functions between $X$ and $Y$ endowed with this topology, one has
$
  CC(X times Y, Z) tilde.equiv CC(X, CC(Y,Z)).
$

#definition([compact-open topology, see @bou2, page 301])[
  Let $X$ and $Y$ be two topological spaces, and by $CC(X,Y)$ denote the set of all continuous functions from $X$ to $Y$. For each compact set $K subset X$ and each open set $U subset Y$, let $V(K,U)$ be the set of all functions $f in CC(X,Y)$ such that $f(K) subset U$. The collection
  $
  {V(K,U) mid(|) K subset X, U subset Y}
  $
  forms a subbase of a topology on $CC(X,Y)$, called the _compact-open_ topology.
]

#remark[
  Clearly, the topology of pointwise convergence on $CC(X,Y)$ is coarser than the compact-open topology.
]

#corollary[
  Let $X$ and $Y$ be topological spaces such that $Y$ is Hausdorff. Then $CC(X,Y)$ is Hausdorff.
] <cohaus>

We also have an equivalent definition of the compact-open topology in terms of filters:

#proposition([see @bb, page 34])[
  Let $X$ and $Y$ be topological spaces such that $X$ is locally compact and $Y$ is regular. Then a filter $F in FF(CC(X,Y))$ converges to a function $f in CC(X,Y)$ if and only if, for any filter $P in FF(X)$ converging to $p in X$, we have $F(P) -> f(p)$ in $Y$, where the filter $F(P)$ is based on
  $
    {A(B) mid(|) A in F, B in P} = {{a(b) mid(|) a in A, b in B} mid(|) A in F, B in P}.
  $
] <cofilter>

Finally, we give the definition of continuous functions:

#definition[
  Let $n in NN_0$. The set $C_n (RR)$ of _curried continuous $n$-variable functions_ is a Hausdorff topological vector space defined recursively as follows:
  - If $n = 0$, we set $C_0 (RR) = RR$;
  - If $C_n (RR)$ is defined, we set $C_(n+1) (RR) = CC(RR, C_n (RR))$, endowed with pointwise linear structure and the compact-open topology. @cohaus and @cotvs ensure that $C_(n+1)(RR)$ is a Hausdorff topological vector space.
]

#remark[
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

#lemma[
  Let $X, Y$ be topological spaces such that $X$ is locally compact. Then a sequence ${f_k}_(k in NN) subset CC(X,Y)$ converges to a function $f in CC(X,Y)$ if and only if $f_k (x_k) st(k -> oo) f(x)$ whenever $x_k st(k -> oo) x$ in $X$.
] <simul>
#proof[
  First, assume that $f_k -> f in CC(X,Y)$, and consider a sequence ${x_k}_(k = 1)^oo subset X$ converging to $x in X$. Let $U$ be a neighborhood of $f(x)$ in $Y$. Since $X$ is locally compact, the point $x in X$ has a compact neighborhood $K$. Hence, eventually as $k -> oo$, we have $x_k in K$ and $f_k in V(K,U)$, which means that eventually $f_k (x_k) in U$. Since $U$ was arbitrary, we conclude that $f_k (x_k) st(k -> oo) f(x)$.

  Conversely, suppose that $f_k (x_k) st(k -> oo) f(x)$ whenever $x_k st(k -> oo) x in X$. To prove that $f_k -> f in CC(X,Y)$, consider a neighborhood $V(K,U)$ of $f$, and assume that there is a subsequence ${f_(k_l)}_(l = 1)^oo$ such that $f_(k_l)(K) subset.not U$. That means that we can find a sequence ${x_l}_(l = 1)^oo subset K$ such that $f_(k_l)(x_l) in.not U$. By the compactness of $K$, we can choose a subsequence ${x_(l_j)}_(j = 1)^oo$ that converges to a point $x in K$. Moreover, since $f in V(K,U)$, we have $f(K) subset U$, and therefore $f(x) in U$, i.e. $U$ is a neighborhood of $f(x)$. However, we have $f_(k_(l_j))(x_(l_j)) in.not U$
  for all $j in NN$, a contradiction with the condition that $f_k (x_k) -> f(x)$ whenever $x_k -> x$.
]

#definition[
  A sequence ${f_k}_(k = 1)^oo$ of functions between topological spaces $X$ and $Y$ is said to converge _continuously_ to $f : X -> Y$ if, whenever $x_k -> x in X$, we have the convergence $f_k (x_k) -> f(x) in Y$.
]

#corollary[
  From the above lemma we conclude that if $n >= 1$, a sequence of functions ${f_k}_(k = 1)^oo$ in $C_n (RR)$ converges to $f in C_n (RR)$ if and only if it converges continuously.
]

== Differentiable functions

Finally, we define the spaces of curried differentiable functions.

#definition[
  Let $m in NN_0$ and $n in NN_0$. The set $D^m_n (RR)$ of _curried $m$ times differentiable functions_ is a topological space defined recursively as follows:
  - If $n = 0$, we set $D^m_0 (RR) = RR$ for all $m$, as usual;
  - If $m = 0$, we set $D^0_n (RR) = C_n (RR)$;
  - Let $m,n > 0$, and assume that both $D_(n-1)^m (RR)$ and $D_n^(m-1) (RR)$ are defined. Then we let $D^m_n (RR)$ be the set of all functions $f in CC(RR, D^m_(n-1)(RR))$ such that there is a function $f' in D^(m-1)_n (RR)$ which satisfies
    $
      (f(x + h) - f(x))/h st(h -> 0) f'(x) in H_(n-1) (RR)
    $
    for all $x in RR$, where *the convergence is taken in the space $H_(n-1) (RR)$*. Clearly, if $f, g in D^m_n (RR)$ and $alpha, beta in RR$, we have
    $
      (alpha f + beta g)' = alpha f' + beta g',
    $
    so in particular, $alpha f + beta g in D^m_n (RR)$.\
    We endow $D^m_n (RR)$ with the coarsest topology in which the maps
    $
      i : D^m_n (RR) &-> CC(RR, D^m_(n-1) (RR)), #h(3cm) d : D^m_n (RR) -> D^(m-1)_n (RR) #<maps>\
      f &|-> f #h(6.85cm) f |-> f'
    $
    are continuous. This topology will be called the _differential topology of order $m$._ @diffhaus and @difftvs ensure that $D_n^m (RR)$ is a Hausdorff topological space.
]

#lemma[
  For all $m,n in NN_0$, we have $D_n^(m+1) (RR) subset D_n^m$, and the inclusion map
  $
    j : D^(m+1)_n (RR) -> D^m_n (RR)
  $
  is continuous, meaning that the topology on $D^(m+1)_n (RR)$ is finer than the topology induced from $D^m_n (RR)$.
]
#proof[
  We prove by induction over $n$. Consider the following cases:
  + $n = 0$. Then we have $D_0^(m+1) (RR) = D_0^n (RR) = RR$, and the statement holds;
  + $m = 0$. Then we have
    $
      D_n^1 (RR) subset CC(RR, D_(n-1)^0 (RR)) = CC(RR, C_(n-1) (RR)) = C_n (RR) = D_n^0 (RR),
    $
    and the inclusion is continuous by the definition of differential topology.
  + $n, m > 0$, with the statement proven for $(m, n-1)$ and $(m-1, n)$. Let $f in D_n^(m+1) (RR)$. Then we have
    $
      f in CC(RR, D_(n-1)^(m+1) (RR)) subset CC(RR, D_(n-1)^m (RR)).
    $
    Moreover, since $f' in D_n^m (RR) subset D_n^(m-1) (RR)$, we see that $f in D_n^m (RR)$ by definition, so we have the inclusion $D_n^(m+1) (RR) subset D_n^m (RR)$. It only remains to show that the inclusion map $j : D_n^(m+1) (RR) -> D_n^m (RR)$ is continuous. This is equivalent to showing that the maps $i circ j$ and $d circ j$ are continuous, which is evident from the following commutative diagrams:
    #centering(shallow: false)[
      #let s1 = 1
      #let s2 = 1
      #let ll = 10pt
      #let pd = 1em
      #let np = (40pt, 40pt)
      #show: columns.with(2)
      #commutative-diagram(
        padding: pd, node-padding: np,
        node((0,0), $D_n^(m+1)(RR)$, "00"),
        node((0,s1), $D_n^m (RR)$, "01"),
        node((s2,0), $CC(RR, D_(n-1)^(m+1)(RR))$, "10"),
        node((s2,s1), $CC(RR, D_(n-1)^m (RR))$, "11"),
        arr("00", "01", $j$, label-pos: ll, "inj"),
        arr("00", "10", $i$, label-pos: -ll, "inj"),
        arr("01", "11", $i$, label-pos: ll, "inj"),
        arr("10", "11", $j$, label-pos: -ll, "inj"),
      )
      #colbreak()
      #commutative-diagram(
        padding: pd, node-padding: np,
        node((0,0), $D_n^(m+1) (RR)$, "00"),
        node((0,s1), $D_n^m (RR)$, "01"),
        node((s2,0), $D_n^m (RR)$, "10"),
        node((s2,s1), $D_n^(m-1)(RR)$, "11"),
        arr("00", "01", $j$, label-pos: ll, "inj"),
        arr("00", "10", $d$, label-pos: -ll),
        arr("01", "11", $d$, label-pos: ll),
        arr("10", "11", $j$, label-pos: -ll, "inj"),
      )
    ]
]

#corollary[
  We have a chain of subspaces with each topology finer than the previous one:
  $
    C_n (RR) = D_n^0 (RR) <--^j D_n^1 (RR) <--^j D_n^2 (RR) <--^j D_n^3 (RR) <--^j ...
  $
]

#corollary[
  For all $n, m in NN_0$, the topological space $D_n^m (RR)$ is Hausdorff.
] <diffhaus>
#proof[
  Since $C_n (RR)$ is Hausdorff and $i : D_n^m (RR) -> C_n (RR)$ is continuous and injective, we see that $D_n (RR)$ is also Hausdorff.
]

#definition[
  Let $n in NN_0$. We define the space $D_n^oo (RR)$ of _curried infinitely differentiable_ functions as follows:
  $
    D_n^oo (RR) = inter.big_(m = 0)^oo D_n^m (RR).
  $
  The topology on $D_n^oo (RR)$ is the initial topology with respect to the family of inclusion maps ${i_m}_(m = 0)^oo$, where $i_m : D_n^oo -> D_n^m (RR)$.
]

#lemma[
  For every $n in NN_0$, the space $D_n^oo$ is a #fr space.
] <doofrechet>
#proof[
  A trivial exercise.
]

= Correspondence with uncurried functions

Any function from $RR^n -> RR$ can be rewritten as an element of $H_n (RR)$, and vice versa. Naturally, one might ask whether the spaces $C_n (RR)$ and $D_n^m (RR)$ correspond similarly to continuous and continuously differentiable, respectively, functions from $RR^n$ to $RR$. The answer to this question is yes.

#definition[
  Let $tilde(f) : RR^n -> RR$ be a function. Define
  $
    gamma(tilde(f))(x_1)(x_2)...(x_n) = tilde(f)(x_1, x_2, ..., x_n).
  $
  Then $gamma : "Hom"(RR^n, RR) -> H_n (RR)$ is clearly a bijection. The function $f = gamma(tilde(f))$ will be called the _curry_ of $tilde(f)$.
]

#lemma[
  Let $n in NN$. If $"Hom"(RR^n, RR)$ is given the topology of pointwise convergence together with the pointwise linear structure, then $gamma : "Hom"(RR^n, RR) -> H_n (RR)$ becomes a linear homeomorphism of topological vector spaces.
] <pwccurry>
#proof[
  We easily see by induction that a filter $F in FF(H_n (RR))$ converges to $f in H_n (RR)$ if and only if $F(x_1)(x_2)...(x_n) -> f(x_1)(x_2)...(x_n) in RR$ for any points $x_1, ..., x_n in RR$. But this is equivalent to $gamma^(-1)(F) -> gamma^(-1)(f)$ in $"Hom"(RR^n, RR)$, so we see that $gamma$ is a homeomorphism.
]

Now, let us consider the spaces $C_n (RR)$ of continuous functions.

#proposition([see @bou2, page 302])[
  Let $X, Y, Z$ be topological spaces such that $X$ is Hausdorff and $Y$ is locally compact. Then the map
  $
    gamma : CC(X times Y, Z) -> CC(X, CC(Y, Z))
  $
  defined as $gamma(f)(x)(y) = f(x,y)$, is well-defined and is a homeomorphism.
] <curry>

#corollary[
  Let $n in NN_0$. Then the map
  $
    gamma : CC(RR^n, RR) -> C_n (RR)
  $
  defined by $gamma(tilde(f))(x_1)(x_2)...(x_n) = tilde(f)(x_1, ..., x_n)$, is well-defined and is a homeomorphism.
] <cogamma>
#proof[
  If $n = 0$, the statement is trivial. Assume it is proven for $C_n (RR)$. By @curry, we have
  $
    CC(RR^(n+1), RR) = CC(RR times RR^n, RR) tilde.equiv CC(RR, CC(RR^n, RR)) tilde.equiv CC(RR, C_n (RR)) = C_(n+1)(RR),
  $
  q.e.d.
]

A similar result holds for the spaces $D_n^m (RR)$ which are in a natural bijection with the spaces $C^m (RR^n)$.

#theorem[
  Let $m,n in NN$. A curried function $f in H_n (RR)$ lies in the class $D_n^m (RR)$ if and only if its counterpart $tilde(f) : RR^n -> RR$ has continuous partial derivatives on $RR^n$, of all orders up to $m$. Moreover, for each $1 <= i_1 <= i_2 <= ... <= i_m <= n$, we have
  $
    &(partial^m tilde(f))/(partial x_(i_1) partial x_(i_2) ... partial x_(i_m))(x_1, x_2, ..., x_n)\
    = &f(x_1)...(x_(i_1 - 1))'(x_i_1)...(x_(i_2 - 1))'(x_i_2)...(x_(i_m - 1))'(x_i_m)...(x_n). #<difftrans>
  $
] <diffgamma>
#proof[
  If $n = 0$ or $m = 0$, the statement is trivial. Now let $n,m > 0$ and assume the statement proven for $(m,n-1)$ and $(m-1,n)$.\

  First, let $f in D_n^m (RR)$. We immediately see that $f in D_n^(m-1) (RR)$, and so, by the induction hypothesis, partial derivatives or order up to $m-1$ exist and are continuous on $RR^n$. Now, consider some $1 <= i_1 <= i_2 <= ..., <= i_m <= n$. It is not hard to see by definition that (@difftrans) holds. To show that the partial derivative with respect to $x_i_1, ..., x_i_m$ is continuous, consider $(h_1, h_2, ..., h_n) -> 0 in RR^n$, and a point $(x_1, ..., x_n) in RR^n$. By the continuity of $f$ and the definition of the differential topology, we have
  $
    f(x_1 + h_1) &st(h_1 -> 0) f(x_1) in D_(n-1)^m (RR),\
    &dots.v\
    f(x_1 + h_1)...(x_(i_1 - 1) + h_(i_1-1))' &st(h_1\, ...\, h_(i_1 - 1) -> 0) f(x_1)...(x_(i_1 - 1))' in D_(n - i_1 + 1)^(m-1) (RR),\
    &dots.v\
    &f(x_1 + h_1)...(x_(i_1 - 1) + h_(i_1-1))'...(x_(i_m - 1) + h_(i_m - 1))...(x_n + h_n)\
    st(h_1\, h_2\, ...\, h_n -> 0) &f(x_1)...(x_(i_1 - 1))'...(x_(i_m-1))'...(x_n) in D_0^0 (RR) = RR,\
  $
  so the partial derivative
  $
    (partial^m tilde(f))/(partial x_i_1 partial x_i_2 ... partial x_i_m)
  $
  is continuous on $RR^n$. Note that so far we have only proven the existence and continuity of partial derivatives with non-decreasing indices $i_1, ..., i_m$. However, as stated in @rud2 (pp. 235-236), the order of partial differentiation does not matter, as long as one of the partial derivatives is shown to be continuous.\

  Conversely, suppose $f in H_n (RR)$ is such that $tilde(f) : RR^n -> RR$ lies in the class $C^m (RR^n)$. To show that $f in D_n^m (RR)$, we follow three steps:
  + For all $x_1 in RR$, we have $f(x_1) in D_(n-1)^m (RR)$. This is provided by the induction hypothesis, since the restriction of a $C^m$ function on a hyperplane is also a $C^m$ function.
  + The function $f : RR -> D_(n-1)^m (RR)$ is continuous. To show this, consider a sequence ${x_k^((1))}_(k in NN) subset RR$ converging to $x_0^((1)) in RR$. We aim to prove that $f(x_k^((1))) -> f(x_0^((1)))$ in $D_(n-1)^m (RR)$. This is equivalent to showing that
    $
      f(x_k^((1))) -> f(x_k^((1))) in CC(RR, D_(n-2)^m (RR)) #h(10pt) "and" #h(10pt) f(x_k^((1)))' -> f(x_0^((1)))' in D_(n-1)^(m-1) (RR).
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
  + Finally, we need to find $f' in D_n^(m-1) (RR)$ such that
    $
      (f(x + h) - f(x))/h st(h -> 0) f'(x) in H_(n-1)(RR)
    $ <conv>
    for all $x in RR$. Indeed, following (@difftrans), let us define $f' := gamma(partial tilde(f)\/partial x_1)$. We immediately see by the induction hypothesis that $f'$ so defined lies in $D_n^(m-1) (RR)$. To see that (@conv) holds, consider $x_1, ..., x_n in RR$ and write
    $
      f'(x_1)(x_2)...(x_n) &= (partial tilde(f))/(partial x_1)(x_1, ..., x_n)\
      &= lim_(h -> 0) (tilde(f)(x_1 + h, x_2, ..., x_n) - tilde(f)(x_1, ..., x_n))/h\
      &= (lim_(h -> 0) (f(x_1 + h) - f(x_1))/h)(x_2)...(x_n),
    $
    and we are done.
]

= Completeness and metrizability

In this section, we will establish some strong properties of the spaces $C_n (RR)$ and $D_n^m (RR)$, namely local convexity, metrizability and completeness.

#definition[
  A topological vector space $X$ is called _metrizable_ if its topology is compatible with an invariant metric $d$, i.e. such that $d(x + y, x + z) = d(y,z)$ for all $x,y,z in X$.
]

#definition[
  Let $X$ be a topological vector space, and let ${x_k}_(k = 1)^oo subset X$ be a sequence. This sequence is called a _Cauchy sequence_ if, for any neighborhood $U$ of zero, there is $N in NN$ such that for all $k,l >= N$, we have $x_k - x_l in U$. Clearly, if $X$ is metrizable, this definition corresponds to the metric definition of a Cauchy sequence.\
  If every Cauchy sequence in $X$ has a limit in $X$, we call $X$ a _sequentially complete_ topological vector space.
]

#definition[
  A topological vector space is called a _#fr space_ if it is locally convex, metrizable, and sequentially complete. In other words, if its topology is compatible with a complete invariant metric.
]

A very convenient criterion of metrizability is the existence of a countable local base:

#proposition([see @rud, page 19])[
  A topological vector space $X$ is metrizable if and only if it admits a countable local base of neighborhoods of $0$.
] <coumetr>

Now, let us first consider the general spaces $H_n (RR)$.

#theorem[
  For all $n in NN_0$, the space $H_n$ is locally convex and sequentially complete, but not metrizable for $n > 0$.
]
#proof[
  If $n = 0$, we have $H_0 (RR) = RR$, which is clearly locally convex, sequentially complete and metrizable.

  Now, let $n > 0$ and assume that $H_(n-1)(RR)$ is locally convex and sequentially complete. Consider a Cauchy sequence ${f_k}_(k = 1)^oo subset H_n (RR)$. It is easy to see by the definition of the pointwise convergence topology, that for all $x in RR$, the sequence ${f_k (x)}_(k = 1)^oo subset H_(n-1)(RR)$ is Cauchy, hence it has a limit which we denote by $f(x)$. We have therefore constructed a function $f in H_n (RR)$ with $f_k st(k -> oo) f$, and we can conclude that $H_n (RR)$ is complete.\

  Next, we show that $H_n (RR)$ is locally convex. It suffices to prove that any neighborhood of the form $V(x, U)$ contains a convex neighborhood $V'$ of zero. Indeed, since $H_(n-1)(RR)$ is locally convex, let $U' subset U$ be a convex neighborhood of zero in $H_(n-1)(RR)$. Then we have $0 in V(x, U') subset V(x, U)$, and $V(x, U')$ is clearly convex.

  Finally, to show that $H_n (RR)$ is *not* metrizable, it suffices to show that no countable local base exists in $H_n (RR)$. To this end, assume the contrary, i.e. let ${V_j}_(j = 1)^oo$ be a countable local base in $H_n (RR)$. Since every set $V_j$ contains a neighborhood of zero of the form
  $
    inter.big_(l = 1)^N_j V(x_l^j, U_l^j),
  $
  where $x_l^j in RR$ and $U_l^j$ are neighborhoods of zero in $H_(n-1)(RR)$, by uniting all these $V(x_l^j, U_l^j)$ into one family we obtain a countable local subbase ${V(x_i, U_i)}_(i = 1)^oo$ in $H_n (RR)$. In particular, it follows that a sequence of functions ${f_k}_(k = 1)^oo subset H_n (RR)$ converges to $0$ if and only if for all $i in NN$, eventually $f_k in V(x_i, U_i)$. However, we can easily choose $phi in H_(n-1)(RR)$ such that $phi != 0$, and then define
  $
    f_k (x) = cases(
      0\,#h(6pt)&"if" x = x_i "for some" i\,,
      phi\, &"otherwise".
    )
  $
  For all $i,k in NN$, we have $f_k (x_i) = 0 in U_i$, so $f_k in V(x_i, U_i)$. However, clearly ${f_k}_(k = 1)^oo$ does not converge to $0$. A contradiction.
]

Next, we consider the spaces $C_n (RR)$ of continuous functions, which turn out to be both complete and metrizable.

#theorem[
  Suppose that $X$ is a locally compact and hemicompact topological space (that is, $X$ is the union of countably many its compact subsets), and let $Y$ be a #fr space. Then the space $CC(X, Y)$ is also a #fr space.
] <fr2fr>
#proof[
  First of all, we need to show that $CC(X,Y)$ is metrizable. Since $Y$ is metrizable, by @coumetr it admits a countable basis ${U_n}_(n = 1)^oo$ of neighborhoods of $0$. Moreover, since $X$ is hemicompact, we have
  $
    X = union.big_(m = 1)^oo K_m,
  $
  where all $K_m$ are compact. It is clear to see that the family
  $
    {V(K_m, U_n) mid(|) m,n in NN}
  $
  forms a countable basis of neighborhoods of $0$ in $CC(X,Y)$. Hence, by @coumetr the space $CC(X,Y)$ is metrizable.\

  Next, we prove that $CC(X,Y)$ is locally convex. Let $m,n in NN$. We need to find a convex neighborhood of zero inside $V(K_m, U_n)$. Since $Y$ is locally convex, we have a convex neighborhood $U' subset U_n$ of zero. Now simply take $V' = V(K_m, U')$, and observe that $V' subset V(K_m, U_n)$ and $V'$ is convex.

  It remains to show that $CC(X,Y)$ is complete. To this end, consider a Cauchy sequence ${f_k}_(k = 1)^oo$ in $CC(X,Y)$. This means that for all $n,m in NN$, there is $N in NN$ such that
  $
    k,l >= N ==> f_k - f_l in V(K_m, U_n).
  $
  Now, consider a point $x in X$. By choosing $m_0$ such that $x in K_(m_0)$, we see that for all $n in NN$, eventually
  $
    f_k - f_l in V(K_(m_0), U_n) ==> f_k (x) - f_l (x) in U_n.
  $
  This means that the sequence ${f_k (x)}_(k = 1)^oo$ is Cauchy in $Y$, and so it converges to some point $f(x) in Y$. We now need to show that $f$ is continuous and $f_k -> f$ in $CC(X,Y)$.\
  Consider $n,m in NN$. Since $Y$ is a topological vector space, it is _regular_ in the sense that every neighborhood $U$ of $0$ contains the closure $overline(U')$ of some other neighborhood $U'$ of $0$. Hence, we can find $n' in NN$ such that $overline(U_n') subset U_n$. Now, as $k,l -> oo$, eventually we have
  $
    (f_k - f_l)(K_m) subset U_n'.
  $
  Taking any $x in K_m$, we have
  $
    f_k (x) - f_l (x) = (f_k - f_l)(x) in U_n' stretch(=>)_(l -> oo) f_k (x) - f(x) in overline(U_n') subset U_n.
  $
  This means that
  $
    (f_k - f)(K_m) subset U_n
  $ <lim1>
  eventually as $k -> oo$. Now, to show that $f$ is continuous, consider $x in X$ and a neighborhood $U$ of $0 in Y$. Since $X$ is locally compact, there is $m_0$ such that $K_(m_0)$ is a neighborhood of $x$. Moreover, there is $n_0 in NN$ such that $U_(n_0) + U_(n_0) + U_(n_0) subset U$. Finally, by (@lim1) there is $k_0 in NN$ such that $(f_(k_0) - f)(K_(m_0)) subset U_(n_0)$. Now, as $y -> x$, we have $y in K_(m_0)$, and
  $
    f(y) - f(x) = [f(y) - f_k (y)] + [f_k (y) - f_k (x)] + [f_k (x) - f(x)] in U_(n_0) + U_(n_0) + U_(n_0) subset U.
  $
  Hence, we conclude that $f$ is continuous, and (@lim1) implies that for all $m,n in NN$, we have $f_k - f in V(K_m, U_n)$ eventually as $k -> oo$, which means that $f_k -> f$ in $C(X,Y)$, as desired.
]

#corollary[
  For all $n in NN_0$, the space $C_n (RR)$ is a #fr space.
]
#proof[
  If $n = 0$, the statement clearly holds. Now, assuming that $C_(n-1)(RR)$ is a #fr space, we easily conclude by @fr2fr that $C_n (RR)$ is also a #fr space.
]

Finally, we examine the spaces $D_n^m (RR)$ of differentiable functions. To show that these spaces are #fr, we need some preliminary results.

#definition[
  A sequence of functions $f_k : X -> Y$ between topological vector spaces $X$ and $Y$ is said to converge _uniformly_ to a function $f : X -> Y$ on a subset $E subset X$ if, for any neighborhood $U$ of $0 in Y$, we have $f_k (E) subset U$ eventually as $k -> oo$.\
]

#lemma[
  Let $X$ and $Y$ be topological vector spaces and let $f_k -> f$ in the space $CC(X,Y)$. Then $f_k$ converges uniformly to $f$ on all compact subsets of $X$.
] <cont2un>
#proof[
  Let $K subset X$ be compact and let $U$ be a neighborhood of $0 in Y$. Since $f_k -> f in CC(X,Y)$, we have $f_k - f in V(K,U)$ eventually as $k -> oo$. This is to say that eventually $(f_k - f)(K) subset U$, implying that ${f_k}_(k = 1)^oo$ converges to $f$ uniformly on $K$.
]

#theorem[
  For all $m,n in NN_0$, the space $D_n^m (RR)$ is a #fr space.
]
#proof[
  If either $m = 0$ or $n = 0$, then the statement is either trivial or proven before. Suppose that $m, n > 0$, and that the spaces $D_n^(m-1)(RR)$ and $D_(n-1)^m (RR)$ are #fr spaces. By @fr2fr we see that the space $CC(RR, D_(n-1)^m (RR))$ is also #fr.\
  First, we have to show that $D_n^m (RR)$ is metrizable. Its topology is generated by sets of the form $i^(-1)(V) inter d^(-1)(W)$, where $V$ and $W$ are open sets in $CC(RR, D_(n-1)^m (RR))$ and $D_n^(m-1) (RR)$ respectively. By the induction hypothesis, we know that both of these spaces are metrizable, and so have countable local bases:
  $
    {0 in V_j subset CC(RR, D_(n-1)^m (RR)) mid(|) j in NN}, #h(2em) {0 in W_k subset D_n^(m-1) (RR) mid(|) k in NN}.
  $
  We shall show that the family ${i^(-1)(V_j) inter d^(-1)(W_k)}_(j,k = 1)^oo$ forms a local base in $D_n^m (RR)$. Indeed, let $U$ be a neighborhood of zero in $D_n^m (RR)$. Then we have
  $
    U supset i^(-1)(V) inter d^(-1)(W) supset i^(-1)(V_j) inter d^(-1)(W_k) in.rev 0
  $
  for some open sets $V subset CC(RR, D_(n-1)^m (RR)), W subset D_n^(m-1)(RR)$ and some $j,k in NN$.\

  Second, we must show that $D_n^m (RR)$ is locally convex. Consider a neighborhood $U$ of $0 in D_n^m (RR)$. We can assume without loss of generality that $U = i^(-1)(V) inter d^(-1)(W)$, where $V$ and $W$ are neighborhoods of zero in $CC(RR, D_(n-1)^m (RR))$ and $D_n^(m-1) (RR)$, respectively. Since both of these spaces are #fr, we have convex neighborhoods $V' subset V$ and $W' subset W$. Lastly, since both maps $i, d$ are linear, we see that the set
  $
    0 in U' = i^(-1)(V') inter d^(-1)(W') subset U
  $
  is convex. Therefore, the space $D_n^m (RR)$ is locally convex.

  Third, we need to prove that all Cauchy sequences in $D_n^m (RR)$ have a limit.
  To this end, let ${f_k}_(k = 1)^oo subset D_n^m (RR)$ be a Cauchy sequence.
  Then, clearly, the sequences ${f_k}_(n = 1)^oo subset CC(RR, D_(n-1)^m (RR))$ and ${f'_k}_(k = 1)^oo subset D_n^(m-1) (RR)$ are Cauchy, meaning that we have
  $
    f_k st(k -> oo) f in CC(RR, D_(n-1)^m (RR)), #h(2em) f'_k st(k -> oo) g in D_n^(m-1) (RR).
  $
  We must now show that $f in D_n^m (RR)$ with $f' = g$. To this end, let $x_0^((2)), x_0^((3)), ..., x_0^((n)) in RR$ and define the auxiliary functions
  $
    phi_k (x) &= f_k (x)(x_0^((2)))...(x_0^((n))),\
    phi(x) &= f (x)(x_0^((2)))...(x_0^((n))),\
    psi(x) &= g (x)(x_0^((2)))...(x_0^((n))).\
  $
  We immediately observe that $phi_k st(k -> oo) phi$ pointwise on $RR$ Now, let $[a,b] subset RR$. Since $tilde(f'_k) -> tilde(g)$ in the space $CC(RR^n, RR)$, we see that $tilde(f'_k)$ converges to $tilde(g)$ _uniformly_ on the compact set
  $
    [a,b] times {x_0^((2))} times {x_0^((2))} times ... times {x_0^((n))} subset RR^n.
  $
  This implies that we have a uniform convergence $phi'_k -> psi$ on $[a,b]$. Therefore, the function $phi$ is differentiable on $(a,b)$ with $phi' = psi$. Since the interval $[a,b] subset RR$ was arbitrary, we conclude that $phi' = g$ on $RR$. In other words, for all $x_0 in RR$ we have the pointwise limit
  $
    lim_(x -> x_0) (f(x) - f(x_0))/(x - x_0) = g(x_0).
  $
  Since $f in CC(RR, D_(n-1)^m (RR))$ and $g in D_n^(m-1) (RR)$, we conclude that $f in D_n^m (RR)$, and so
  $
    cases(
      reverse: #true,
      gap: #5pt,
      f_k -> f in CC(RR, D_(n-1)^m (RR)),
      f'_k -> f' in D_n^(m-1) (RR)
    ) ==> f_k -> f in D_n^m (RR).
  $
  Therefore, the space $D_n^m (RR)$ is complete, and hence a #fr space.
]

#bibliography("bibliography.yml")

#counter(heading).update(0)
#set heading(numbering: "A.1  ", supplement: "Appendix")

#let th-numbering = "A.1"

#let definition = plainstyle("Definition", numbering: th-numbering, refnumbering: th-numbering)
#let notation = plainstyle("Notation", numbering: th-numbering, refnumbering: th-numbering)
#let example = plainstyle("Example", numbering: th-numbering, refnumbering: th-numbering)
#let exercise = plainstyle("Exercise", numbering: th-numbering, refnumbering: th-numbering)
#let note = plainstyle("Note", numbering: th-numbering, refnumbering: th-numbering)
#let remark = plainstyle("Remark", numbering: th-numbering, refnumbering: th-numbering)

#let theorem = statestyle("Theorem", numbering: th-numbering, refnumbering: th-numbering)
#let lemma = statestyle("Lemma", numbering: th-numbering, refnumbering: th-numbering)
#let proposition = statestyle("Proposition", numbering: th-numbering, refnumbering: th-numbering)
#let statement = statestyle("Statement", numbering: th-numbering, refnumbering: th-numbering)
#let problem = statestyle("Problem", numbering: th-numbering, refnumbering: th-numbering)
#let corollary = statestyle("Corollary", numbering: th-numbering, refnumbering: th-numbering)

= The language of filters <filapp>

#definition[
  Let $X$ be a set. A _filter_ on $X$ is a non-empty set $F subset 2^X$ which is closed under supersets and finite intersections, and does not contain the empty set. The set of all filters on $X$ will be denoted by $FF(X)$.
]

#definition[
  Let $X$ be a set. A family $cal(B) subset 2^X$ is called a _filter base_ if it does not contain the empty set and is closed under finite intersection. The filter $[cal(B)]$ _generated_ by $cal(B)$ is defined as the collection of all supersets of sets from $cal(B)$.\
  If $cal(B) = {{x}}$ where $x in X$, the filter $[x] = [{{x}}]$ is called the _universal filter_ of $x$.\
  If $f : X -> Y$ is a map and $F in FF(X)$ is a filter on $X$, then ${f(A) mid(|) A in F}$ is a filter base that generates the _image filter_ denoted $f(F)$.
]

#definition[
  Let $X$ be a topological space. Then we say that a filter $F$ on $X$ _converges_ to a point $x in X$, and write $F -> x$, if it contains all open neighborhoods of $x$.
]

#remark[
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

#lemma([see @bou1, page 74])[
  Let $X$ be a set and $f_i : X -> Y_i$ be a family of maps, where $Y_i$ are topological spaces. Let $X$ be endowed with the coarsest topology such that $f_i$ is continuous for each $i$. Then a filter $F in FF(X)$ converges to $x in X$ if and only if $f_i (F)$ converges to $f_i (x)$ for all $i$.
]

// = The topology of pointwise convergence <pwcapp>

// #lemma[
//   Let $X$ be a set and $Y$ a topological space. Then a filter $F in FF(SS(X,Y))$ converges to a function $f in SS(X,Y)$ if and only if, for any $x in X$, the filter $F(x) = [{A(x) mid(|) A in F}]$ converges to $f(x) in Y$.
// ]
// #proof[
//   First, let $F -> f in SS(X,Y)$, and consider a point $x in X$. To show that $F(x) -> f(x) in Y$, let $U$ be a neighborhood of $f(x)$. Then, since $F -> f$, we see that $V(x, U) in F$. But this implies $U = V(x,U)(x) in F(x)$, and so we conclude that $F(x) -> f(x)$.\
//   Conversely, assume that $F(x) -> f(x)$ for all $x in X$. To show that $F$ converges to $f$, it suffices to show that $V(x, U) in F$ whenever $f in V(x, U)$. Indeed, if $f in V(x,U)$, we have $f(x) in U$, and so $U in F(x)$, meaning that $U supset A(x)$ for some $A in F$, and so $V(x, U) supset V(x, A(x)) supset A in F$, and we are done.
// ]

// = The compact-open topology <coapp>

= Continuity of linear operations

#lemma[
  Let $X$ be a set and let $Y$ be a real topological vector space. Then $SS(X,Y)$ is also a real topological vector space with respect to the topology of pointwise convergence and the pointwise linear structure.
] <pwtvs>
#proof[
  We need to show that the maps $+ : SS(X,Y) times SS(X,Y) -> SS(X,Y)$ and $dot : RR times SS(X,Y) -> SS(X,Y)$ are continuous.\
  To begin, consider two filters $F_1, F_2 in FF(SS(X,Y))$, converging to $f_1$ and $f_2$ respectively. To show that $F_1 + F_2$ converges to $f_1 + f_2$, consider $x in X$. We have
  $
    (F_1 + F_2)(x) &= [{(A + B)(x) mid(|) A in F_1, B in F_2}]\
    &= [{A(x) + B(x) mid(|) A in F_1, B in F_2}]\ 
    &= F_1 (x) + F_2 (x) -> f_1 (x) + f_2 (x) = (f_1 + f_2)(x).
  $
  This shows that the addition operation is continuous. Scalar multiplication is continuous by a similar argument.
]

#lemma[
  Let $X$ be a topological space and $Y$ a real topological vector space. Then $CC(X,Y)$ is also a real topological vector space with respect to the pointwise linear structure and the compact-open topology.
] <cotvs>
#proof[
  We will show that the map $+ : CC(X,Y) times CC(X,Y) -> CC(X,Y)$ is continuous. Let $F_1, F_2 in FF(CC(X,Y))$ converge to $f_1 in CC(X,Y)$ and $f_2 in CC(X,Y)$ respectively. For any filter $P in FF(X)$ converging to $p in X$, we have
  $
    (F_1 + F_2)(P) &= [{(A_1 + A_2)(B) mid(|) A_i in F_i, B in P}]\
    &supset [{A_1 (B_1) + A_2 (B_2) mid(|) A_i in F_i, B_i in P}]\
    &= F_1 (P) + F_2 (P) -> f_1 (p) + f_2 (p) = (f_1 + f_2)(p).
  $
  The continuity of scalar multiplication is proven similarly.
]

#lemma[
  For all $m,n in NN_0$, the pointwise linear structure is compatible with the topology on $D_n^m (RR)$, making $D_n^m (RR)$ a topological vector space.
] <difftvs>
#proof[
  We prove by induction over $n$ and $m$. If $n = 0$, we have $D_0 (RR) = RR$ with the usual topology and linear structure. If $m = 0$, we have $D_n^0 (RR) = C_n (RR)$, which is a TVS. Suppose now that $m, n > 0$. We need to establish the continuity of the following two maps:
  $
    + : D_n^m (RR) times D_n^m (RR) -> D_n^m (RR), #h(2cm) dot : RR times D_n^m (RR) -> D_n^m (RR).
  $
  In turn, by the definition of the differential topology, this task is equivalent to proving that the maps $i circ (+), d circ (+), i circ (dot), d circ (dot)$ are continuous, where the maps $i$ and $d$ are defined in (@maps).\
  To this end, note that we have commutative diagrams
  #centering(shallow: false)[
    #let s1 = 2
    #let s2 = 1
    #let ll = 10pt
    #let pd = 1em
    #let np = (40pt, 40pt)
    #commutative-diagram(
      padding: pd, node-padding: np,
      node((0,0), $D_n^m (RR) times D_n^m (RR)$, "00"),
      node((0,s1), $D_n^m (RR)$, "01"),
      node((s2,0), $CC(RR, D_(n-1)^m (RR)) times CC(RR, D_(n-1)^m (RR))$, "10"),
      node((s2,s1), $CC(RR, D_(n-1)^m (RR))$, "11"),
      arr("00", "01", $(+)$, label-pos: ll),
      arr("00", "10", $i times i$, label-pos: -1.6*ll, "inj"),
      arr("01", "11", $i$, label-pos: 0.8*ll, "inj"),
      arr("10", "11", $(+)$, label-pos: -ll),
    )
    #v(1em)
    #commutative-diagram(
      padding: pd, node-padding: np,
      node((0,0), $D_n^m (RR) times D_n^m (RR)$, "00"),
      node((0,s1), $D_n^m (RR)$, "01"),
      node((s2,0), $D_n^(m-1) (RR) times D_n^(m-1) (RR)$, "10"),
      node((s2,s1), $D_n^(m-1) (RR)$, "11"),
      arr("00", "01", $(+)$, label-pos: ll),
      arr("00", "10", $d times d$, label-pos: -1.8*ll),
      arr("01", "11", $d$, label-pos: 0.8*ll),
      arr("10", "11", $(+)$, label-pos: -ll),
    )
    #v(1em)
    #commutative-diagram(
      padding: pd, node-padding: np,
      node((0,0), $RR times D_n^m (RR)$, "00"),
      node((0,s1), $D_n^m (RR)$, "01"),
      node((s2,0), $RR times CC(RR, D_(n-1)^m (RR))$, "10"),
      node((s2,s1), $CC(RR, D_(n-1)^m (RR))$, "11"),
      arr("00", "01", $(dot)$, label-pos: ll),
      arr("00", "10", $"id" times i$, label-pos: -2*ll, "inj"),
      arr("01", "11", $i$, label-pos: 0.8*ll, "inj"),
      arr("10", "11", $(dot)$, label-pos: -ll),
    )
    #v(1em)
    #commutative-diagram(
      padding: pd, node-padding: np,
      node((0,0), $RR times D_n^m (RR)$, "00"),
      node((0,s1), $D_n^m (RR)$, "01"),
      node((s2,0), $RR times D_n^(m-1) (RR)$, "10"),
      node((s2,s1), $D_n^(m-1) (RR)$, "11"),
      arr("00", "01", $(dot)$, label-pos: ll),
      arr("00", "10", $"id" times d$, label-pos: -2*ll),
      arr("01", "11", $d$, label-pos: 0.8*ll),
      arr("10", "11", $(dot)$, label-pos: -ll),
    )
  ]
  Since the down-then-right path in each diagram is continuous, the right-then-down paths are continuous as well, and we are done.
]

// #lemma[
//   For every $n in NN_0$, the space $H_n (RR)$ is locally convex.
// ]
// #proof[
//   We employ induction over $n$. If $n = 0$, the statement is clear. Suppose that the space $H_(n-1) (RR)$ is locally compact. It is then easy to see that $V(0, U)$ is a convex neighborhood of $0$ in $H_n (RR)$, where $U$ is the convex neighborhood of $0 in H_(n-1) (RR)$ that exists by the induction hypothesis.
// ]

// = Continuous curried functions


// #lemma[
//   For every $n in NN_0$, the space $C_n (RR)$ is locally convex.
// ]
// #proof[
//   An easy proof by induction over $n$, similar to the case of $H_n (RR)$.
// ]
//
// Next, we show that the spaces $C_n (RR)$ 
