// #def[
//   Let $n in NN$.
//   A curried function $f in H_n (RR)$ is called _differentiable_ if for all $x_0 in RR$ we have
//   - $f(x_0) in H_(n-1)(RR)$ is differentiable, if $n >= 2$;
//   - There exists a continuous function $f'(x_0) in C_(n-1)(RR)$ such that
//     $
//       f(x_0 + h) = f(x_0) + h dot f'(x_0) + r(h),
//     $
//     where $r(h) in C_(n-1)(RR)$ is a function such that $r(h)\/h -> 0$ in $C_(n-1) (RR)$ as $h -> 0$. Equivalently, we may write
//     $
//       f'(x_0) = lim_(h -> 0) (f(x_0 + h) - f(x_0))/h in C_(n-1)(RR).
//     $
// ]
//
// #prop[
//   Let $n in NN$. Then a curried function $f in H_n (RR)$ is differentiable if and only if its counterpart $tilde(f) = gamma^(-1)(f) : RR^n -> RR$ is differentiable everywhere on $RR^n$.
// ]
// #pf[
//   #let hh = h(3pt)
//   First, consider a differentiable function $f in H_n (RR)$. We aim to show that $tilde(f) : RR^n -> RR$ is differentiable everywhere. Fix a point $x = (x_1, x_2, ..., x_n) in RR^n$ and consider a vector $h = (h_1, h_2, ..., h_n) in RR^n$. By the differentiability of $f,#hh f(x_1),#hh f(x_1)(x_2)$ and so on, we may repeatedly expand
//   $
//     f(x_1 + h_1) = &f(x_1) + h_1 dot f'(x_1) + r_1 (h_1),\
//     f(x_1 + h_1)(x_2 + h_2) = &f(x_1)(x_2 + h_2) + h_1 dot f'(x_1)(x_2 + h_2) + r_1 (h_1)(x_2 + h_2)\
//     = &f(x_1)(x_2)\
//     &op(+) h_1 dot f'(x_1)(x_2 + h_2) + h_2 dot f(x_1)'(x_2)\
//     &op(+) r_1 (h_1)(x_2 + h_2) + r_2 (h_2),\
//     // = &f(x_1)(x_2) + h_1 dot f'(x_1)(x_2 + h_2) + h_2 dot f(x_1)'(x_2) + o(abs((h_1, h_2))).\
//   $
//   where $r_1 (h_1) in C_(n-1)(RR)$ and $r_2 (h_2) in C_(n-2)(RR)$.
//   // $
//   //   abs(o(h_1)(x_2 + h_2))/abs((h_1,h_2)) <= abs(o(h_1)/h_1 (x_2 + h_2)) -> 0.
//   // $
//   We continue the expansion until we obtain
//   $
//     &f(x_1 + h_1)(x_2 + h_2)...(x_n + h_n)\
//     &= f(x_1)(x_2)...(x_n)\
//     &cases(
//       reverse: #true,
//       delim: "[",
//       op(+) h_1 dot f'(x_1)(x_2 + h_2)...(x_n + h_n),
//       op(+) h_2 dot f(x_1)'(x_2)(x_3 + h_3)...(x_n + h_n),
//       op(+) h_3 dot f(x_1)(x_2)'(x_3)(x_4 + h_4)...(x_n + h_n)#hh,
//       #h(3pt) dots.v,
//       op(+) h_n dot f(x_1)(x_2)...(x_(n-1))'(x_n),
//     ) #hh (A)\
//     &cases(
//       delim: "[",
//       reverse: #true,
//       op(+) r_1 (h_1)(x_2 + h_2)(x_3 + h_3)...(x_n + h_n)#hh,
//       op(+) r_2 (h_2)(x_3 + h_3)...(x_n + h_n),
//       #h(3pt) dots.v,
//       op(+) r_(n-1) (h_(n-1))(x_n + h_n),
//       op(+) r_n (h_n).,
//     ) (B)\
//   $
//   Observe that all functions $f'(x_1),#hh f(x_1)'(x_2),#hh f(x_1)(x_2)'(x_3)$ that occur in $(A)$, are continuous by the definition of differentiability, and so when $h -> 0$, we have for instance
//   $
//     f'(x_1)(x_2 + h_2)...(x_n - h_n) - f'(x_1)(x_2)...(x_n) -> 0.
//   $
//   This implies that
//   $
//     &h_1 dot (f'(x_1)(x_2 + h_2)...(x_n - h_n) - f'(x_1)(x_2)...(x_n)) = o(abs(h)),\
//     &h_2 dot (f(x_1)'(x_2)(x_3 + h_3)...(x_n - h_n) - f(x_1)'(x_2)...(x_n)) = o(abs(h)),\
//     &#h(3pt)dots.v\
//     &h_n dot (f(x_1)...(x_(n-1))'(x_n) - f(x_1)...(x_(n-1))'(x_n)) = o(abs(h)).
//   $
//   Now, consider the convergence $r_1 (h_1)\/h_1 st(h_1 -> 0) 0$. This convergence occurs in the space $C_(n-1)(RR)$, which means that as $h -> 0$, we have $h_i -> 0$ for all $1 <= i <= n$ and
//   $
//     abs((r_1 (h_1)(x_2 + h_2)...(x_n + h_n))/(abs(h))) <= abs((r_1 (h_1))/h_1 (x_2 + h_2)...(x_n + h_n)) st(#h(5pt) h_1\, h_2\, ...\, h_n -> 0 #h(5pt)) 0.
//   $
//   In other words, we see that $r_1 (h_1)(x_2 + h_2)...(x_n + h_n) = o(abs(h))$, and similarly all remaining terms in $(B)$ are $o(abs(h))$. Finally, combining these observations yields
//   $
//     tilde(f)(x + h) = &f(x_1 + h_1)(x_2 + h_2)...(x_n + h_n)\
//     = &f(x_1)(x_2)...(x_n)\
//     &cases(
//       reverse: #true,
//       delim: "[",
//       op(+) h_1 dot f'(x_1)...(x_n),
//       op(+) h_2 dot f(x_1)'(x_2)...(x_n),
//       op(+) h_3 dot f(x_1)(x_2)'(x_3)...(x_n)#hh,
//       #h(3pt) dots.v,
//       op(+) h_n dot f(x_1)...(x_(n-1))'(x_n),
//     ) #hh L(h)\
//     &op(+) o(abs(h))\
//     = &tilde(f)(x) + L(h) + o(abs(h)),
//   $
//   where $L : RR^n -> RR$ is linear since it has the form $L(h) = sum_(k = 1)^n c_k h_k$. This allows us to conclude that $tilde(f)$ is differentiable at $x$.\
//
//   To show the reverse implication, we conduct an induction over $n$. If $n = 1$ and $f in H_1 (RR)$, its differentiability is clearly equivalent to the usual definition. Assume that the implication holds for $n-1$, and consider a function $f in H_n (RR)$ such that $tilde(f) : RR^n -> RR$ is differentiable everywhere on $RR^n$.\
//   Let $x_1 in RR$. First of all, since a restriction of a differentiable function is differentiable, we see that the function
//   $
//     f(x_1) = gamma((x_2, ..., x_n) |-> tilde(f)(x_1, x_2, ..., x_n)) in H_(n-1)(RR)
//   $
//   is differentiable by the induction hypothesis. It then remains to show that there is $f'(x_1) in C_(n-1)(RR)$ and $r_1 (h_1) in C_(n-1)(RR)$ for all $h_1 in RR$ such that $r_1 (h_1)\/h_1 st(h_1 -> 0) 0$ and
//   $
//     f(x_1 + h_1) = f(x_1) + h_1 dot f'(x_1) + r_1 (h_1).
//   $
//   Being differentiable, $tilde(f)$ has partial derivatives everywhere, and so we can define
//   $
//     f'(x_1) = gamma((partial tilde(f))/(partial x_1))(x_1) in H_(n-1) (RR).
//   $
//   For variable $y_2, y_3, ..., y_n in RR$ and $h_1 in RR$, we have
//   $
//     tilde(f)(x_1 + h_1, y_2, ..., y_n) &= tilde(f)(x_1, y_2, ..., y_n) + (d_((x_1, y_2, ..., y_n)) tilde(f))(h_1, 0, ..., 0) + r (h_1, y_2, ..., y_n)\
//     &= f(x_1)(y_2)...(y_n) + h_1 dot f'(x_1)(y_2)...(y_n) + r (h_1, y_2, ..., y_n),
//   $
//   where $r(h_1, y_2, ..., y_n) = o(h_1)$. We then define $r_1 (h_1) = gamma(r)(h_1)$. Hence, by abstracting over $y_2, ..., y_n$, we obtain
//   $
//     f(x_1 + h_1) = f(x_1) + h_1 dot f'(x_1) + r_1 (h_1).
//   $
//   It remains to show that $f'(x_1)$ and $r_1 (h_1)$ are continuous and that $r_1 (h_1)\/h_1 -> 0$ as $h_1 -> 0$.
// ]
//
// #prop[
//   If $f in H_n (RR)$ is differentiable, then $f$ is continuous.
// ]
// #pf[
//   // If $n = 1$, then $f : RR -> RR$ is differentiable in the usual sense, and so $f$ is continuous.\
//   // Suppose that the statement is proven for $n-1$, and consider a differentiable function $f in H_n (RR)$. First of all, for all $x in RR$ we know that $f(x) in H_(n-1)(RR)$ is differentiable, and hence continuous. It remains to show that $f$ is a continuous map from $RR -> C_(n-1)(RR)$. Let $x_k -> x_0 in RR$. Then, letting $h_k = x_k - x_0$, we can write
//   // $
//   //   f(x_k) = f(x_0 + h_k) = f(x_0) + h_k dot f'(x_0) + r(h_k),
//   // $
//   // where $r(h_k) in C_(n-1)(RR)$ are such that $r(h_k)\/h_k st(k -> oo) 0$. Since $f'(x_0)$ is continuous, we have
//   // $
//   //   h_k dot f'(x_0) + r(h_k) st(k -> oo) 0 in C_(n-1)(RR),
//   // $
//   // so $f(x_k) -> f(x_0)$, which means that $f$ is continuous.
//   If $f$ is differentiable, then $tilde(f) : RR^n -> RR$ is differentiable, then $tilde(f)$ is continuous, then $f$ is continuous.
// ]

// #prop[
//   A curried function $f in H_n (RR)$ is differentiable at $(x_1, x_2, ..., x_n) in RR^n$ if and only if $tilde(f) = gamma^(-1)(f)$ has all partial derivatives at $(x_1, x_2, ..., x_n) in RR^n$.
// ] <diff>
// #pf[
//   We prove by induction over $n$. If $n = 1$, the statement is trivial, so assume $n >= 2$ and the statement proven for $1, 2, ..., n-1$.\
//   Suppose that $f in H_n$ is differentiable. Then for each $i >= 2$, we have
//   $
//     (partial tilde(f))/(partial x_i) (x_1, x_2, ..., x_n) &= lim_(h -> 0) (tilde(f)(x_1, ..., x_(i-1), x_i + h, x_(i+1), ..., x_n) - tilde(f)(x_1, ..., x_n))/h\
//     &= (partial gamma^(-1)(f(x_1)(x_2)...(x_(i-1))))/(partial x_i)(x_i, x_(i+1), ..., x_n),
//   $ <down>
//   which exists by the induction hypothesis, since $f(x_1)...(x_i) in H_(n-i) (RR)$ is differentiable.\
//   It remains to show that $(partial tilde(f))/(partial x_1)$ exists. But by the definition of $f'(x_1)$, we have
//   $
//     f'(x_1) = lim_(h -> 0) (f(x_1 + h) - f(x_1))/h.
//   $ <fp>
//   Since the limit is taken in $H_n (RR)$, by applying (@fp) to $x_2, x_3, ..., x_n$, we get
//   $
//     (partial tilde(f))/(partial x_1)(x_1, x_2, ..., x_n) = f'(x_1)(x_2)...(x_n).
//   $
//   Now suppose that $tilde(f) : RR^n -> RR$ has all partial derivatives at $(x_1, ..., x_n)$. By (@down), we see that $tilde(f(x_1)) : RR^(n-1) -> RR$ has all partial derivatives at $(x_2, x_3, ..., x_n)$, and so by the induction hypothesis $f(x_1)$ is differentiable. Finally, we set $f'(x_1) := gamma((partial tilde(f))/(partial x_1))(x_1)$, and easily see that (@fp) holds for $f'(x_1)$ so defined. Therefore $f$ is differentiable.
// ]

// #def[
//   A curried function $f in H_n (RR)$ is called _continuously differentiable_ if $f$ is differentiable everywhere, and the maps $f', x |-> f(x)'$ are continuous.
// ]

// #prop[
//   A curried function $f in H_n (RR)$ is continuously differentiable if and only if $tilde(f) = gamma^(-1)(f)$ has continuous partial derivatives everywhere on $RR^n$.
// ]
// #pf[
//   The base case $n = 1$ is trivial, so assume the statement proven for $1, 2, ..., n-1$. We again follow two steps.\
//   First suppose that $f in H_n (RR)$ is continuously differentiable. By @diff we see that $tilde(f)$ has partial derivatives everywhere on $RR^n$, so it remains to show these derivatives are continuous. With respect to $x_1$, we have
//   $
//     (partial tilde(f))/(partial x_1) = gamma^(-1)(f')
//   $
//   which is continuous since $f'$ is continuous. To show the continuity of $(partial tilde(f))/(partial x_2)$, consider a sequence $x^((k)) = (x_1^((k)), x_2^((k)), ..., x_n^((k))) in RR^n$, converging to a point $x = (x_1, ..., x_n)$. By the continuity of the map $t |-> f(t)'$, we have $f(x_1^((k)))' -> f(x_1)'$ in $C_(n-1)(RR)$, which implies
//   $
//     (partial tilde(f))/(partial x_2) (x_1^((k)), x_2^((k)), ..., x_n^((k))) = f(x_1^((k)))'(x_2^((k)))...(x_n^((k))) st(k -> oo) f(x_1)'(x_2)...(x_n) = (partial tilde(f))/(partial x_2)(x_1, ..., x_n),
//   $
//   so $(partial tilde(f))/(partial x_2)$ is continuous.
// ]

// #def[
//   Let $n in NN_0$. The _space of curried differentiable functions_ $D_n (RR)$ is a Hausdorff topological vector space defined recursively as follows:
//   - If $n = 0$, we set $D_0 (RR) = C_0 (RR) = RR$.
//   - If the space $D_n (RR)$ is defined, we define $D_(n+1) (RR)$ as the subspace of $CC(RR, D_n (RR))$ consisting of such functions $f : RR -> D_n (RR)$, that there is $f' in C_(n+1)(RR)$ which satisfies
//     $
//       f(x_0 + h) = f(x_0) + h dot f'(x_0) + o(h) in C_n (RR)
//     $
//     for all $x_0 in RR$.
// ]
//
// #prop[
//   Let $n in NN_0$. Then the map
//   $
//     gamma : C^1 (RR^n) -> D_n (RR)
//   $
//   is well-defined and a homeomorphism. In particular, a function $f in C_n (RR)$ lies in $D_n (RR)$ if and only if its counterpart $tilde(f) = gamma^(-1)(f) : RR^n -> RR$ has continuous partial derivatives.
// ]
// #pf[
//   First let us show that $gamma$ is well-defined and bijective. 
// ]
//
// #def[
//   Fix $n in NN_0$. For all $m in NN$, the _space of curried $m$ times differentiable functions_ $D_n^m (RR)$ is defined recursively as follows:
//   - If $m = 1$, we set $D_n^1 (RR) = D_n (RR)$.
//   - If $D_n^m (RR)$ is defined, we set $D_n^(m+1)(RR)$ to be the space of all functions $f in D_n (RR)$ such that $f' in D_n^m (RR)$.
//   Trivially, for all $n in NN_0$, we have
//   $
//     D_n^1 (RR) supset D_n^2 (RR) supset D_n^3 (RR) supset ... 
//   $
// ]
//
// #prop[
//   Let $n,m in NN$. Then a function $f in C_n (RR)$ lies in the differentiability class $D_n^m (RR)$ if its counterpart $tilde(f) = gamma^(-1)(f) : RR^n -> RR$ lies in the class $C^m (RR)$.
// ]
//
// #prop[
//   Let $n, m in NN$, and $f in D_n^m (RR)$. Then for all $x in RR$, we have $f(x) in D_(n-1)^m (RR)$.
// ]
// #pf[
//   ...
// ]


// #def[
//   A filter $F$ on $X$ is called an _ultrafilter_ if is not properly contained in any other filter. A standard application of Zorn's lemma shows that every filter in contained in at least one ultrafilter @bou. Moreover, for any filter $F in FF(X)$ we have
//   $
//     F = inter.big {G mid(|) G "is an ultrafilter and" F subset G}.
//   $
// ]

// #def[
//   One may try to decouple the notion of convergent filters from topology. Let $X$ be a set with a relation $op(->) subset FF(X) times X$. Then $(X, ->)$ is called a _convergence space_ if
//   - For all $x in X$, we have $[x] -> x$;
//   - If $F -> x$ and $G -> x$, then $F inter G -> x$;
//   - If $F -> x$ and $F subset G$, then $G -> x$.
// ]
//
// #def[
//   A map $f : X -> Y$ between convergence spaces is said to be _continuous_ if $f(F) -> f(x) in Y$ whenever $F -> x in X$.
// ]
//
// #def[
//   Let $X, Y$ be two convergence spaces. Then the product $X times Y$ is endowed with the following convergence structure: a filter $F in FF(X times Y)$ converges to $(x,y) in X times Y$ if and only if $p_X (F) -> x in X$ and $p_Y (F) -> y in Y$.
// ] <cprod>
//
// #def([see @bb, pages 25-26])[
//   Let $X, Y$ be convergence spaces. By $CC(X,Y)$ denote the set of all continuous functions from $X$ to $Y$. Then $CC(X,Y)$ can be endowed with a convergence structure as follows. For a filter $F in FF(CC(X,Y))$, we say that $F -> f in CC(X,Y)$
// if and only if $F(P) -> f(p)$ whenever $P -> p in X$.
// Here, the filter $F(P)$ is based on
//   $
//     {A(B) mid(|) A in F, B in P} = {{a(b) mid(|) a in A, b in B} mid(|) A in F, B in P}.
//   $
//   The resulting convergence structure on $CC(X,Y)$ is called the structure of _continuous convergence._
// ] <cxydef>
//
// #rem[
//   Continuous convergence on $CC(X,Y)$ is the coarsest convergence structure that makes the _evaluation mapping_
//   $
//     omega : CC(X,Y) times X -> Y
//   $
//   continuous. Here, the product $CC(X,Y) times X$ is endowed with the product convergence structure as per @cprod.
// ]

// #prop([see @bb, page 27])[
//   Let $X, Y, Z$ be convergence spaces. Then the map
//   $
//     gamma : CC(X times Y, Z) -> CC(X, CC(Y, Z))
//   $
//   defined as $gamma(f)(x)(y) = f(x,y)$, is well-defined and is a homeomorphism.
// ] <convcurry>

// #prop([see @bb, page 34])[
//   Let $X, Y$ be topological spaces such that $X$ is locally compact and $Y$ is regular. Then the convergence space $CC(X,Y)$ is topologized by the compact-open topology (see @bou2, page 301). That is, the convergence relation arising from this topology coincides precisely with the convergence structure given in @cxydef.
// ] <top>

// #cor[
//   If $X$ is a locally compact topological space and $Y$ is a regular topological vector space, then $CC(X,Y)$ is a topological vector space.
// ] <cor1>
