#import "@local/common:0.0.0": *
#import "@local/theorem-shorthands-en:0.0.0": *
#import "@preview/equate:0.3.1": equate
#show: theorem

#set page("a4", margin: 0.5in)
#set text(font: "TeX Gyre Schola")
#set heading(numbering: "1.")

#set math.equation(numbering: "(1)", supplement: none)
#show: equate.with(sub-numbering: false, number-mode: "label")

#let st(cnt, class: []) = $stretch(->)_(#cnt)^(#class)$
#let nn(X) = $cal(N)(#X)$
#let CC = $cal(C)$

#align(center)[
  #text(size: 24pt)[Synchronous Convergence and Applications]
]

= Preliminary definitions

#def[
  A set $I$ together with a relation $<=$ is said to be _directed_ by $<=$ if the following properties hold:
  - *Reflexivity:* $i <= i$ for all $i in I$;
  - *Transitivity:* If $i_1 <= i_2$ and $i_2 <= i_3$, then $i_1 <= i_3$;
  - *Upper bound property:* For all $i_1, i_2 in I$, there is $i in I$ such that $i_1 <= i$ and $i_2 <= i$.
]

#def[
  Let $I, J$ be two directed sets. A map $sigma : J -> I$ is said to be _directed_ if for any $i_0 in I$ there is $j_0 in J$ such that $j >= j_0$ implies $sigma(j) >= i_0$.
]

#def[
  Let $X$ be a set and let $I$ be a directed set. A function $I -> X$ is called a _net_ in $X$, denoted by $(x_i)_(i in I)$. The set of all nets in $X$ (with varying directed sets) will be denoted by $nn(X)$.
]

#def[
  Let $X$ be a topological space, and consider a net $(x_i)_(i in I)$ in $X$. We say that $(x_i)_(i in I)$ _converges_ to $x in X$ and write $x_i st(i in I) x$, if for any neighborhood $U$ of $x$, there is $i_0 in I$ such that $i >= i_0$ implies $x_i in U$. In other words, $x_i$ is _eventually_ in any neighborhood of $x$.
] <topconv>

#def[
  Let $(x_i)_(i in I)$ be a net in a set $X$. If $sigma : J -> I$ is a directed map, then the net $(x_sigma(j))_(j in J)$ is called a _subnet_ of $(x_i)_(i in I)$.
]

#def[
  Let $X$ be a set together with a family $CC subset nn(X) times X$. Then $(X, CC)$ is called a _convergence space_ if the following conditions are satisfied:
  - For any $x in X$ and any directed set $I$, we have $((x)_(i in I), x) in CC$. In other words, any constant net $CC-$converges to the constant;
  - If $((x_i)_(i in I), x_0) in CC$, then $((x_sigma(j))_(j in J), x_0) in CC$ for any subnet $(x_sigma(j))_(j in J)$ of $(x_i)_(i in I)$.

  The condition $((x_i)_(i in I), x_0) in CC$ may be denoted by $x_i st(i in I, class: CC) x_0$ or just $x_i st(i in I) x_0$.
]

#rem[
  Any topological space $X$ automatically receives a convergence space structure as per @topconv.
]

#def[
  A function $f : X -> Y$ between two convergence spaces is said to be _continuous_ if for any net $(x_i)_(i in I)$ converging to $x$ in $X$, the net $(f(x_i))_(i in I)$ converges to $f(x)$ in $Y$.
]

#def[
  Let $X$ be a set together with a family $CC subset nn(X) times X$. Then the family $CC$ is called a _convergence class_ if the following hold:
  - $(X, CC)$ is a convergence space;
  - Let $x in X$. If every subnet of $(x_i)_(i in I) subset X$ has a subnet that $CC$-converges to $x$, then $x_i st(i in I, class: CC) x$.
  - Consider a directed set $I$. For all $i in I$, let $J_i$ be also a directed set and consider a net $(x^i_j)_(j in J_i)$ that $CC$-converges to $x^i in X$. Assume also that $x^i st(i in I, class: CC) x in X$. Denote $F := I times product_(i in I) J_i$. The set $J$ is directed by the pointwise order inherited from $I$ and $J_i$'s. We then require that the following convergence must hold:
    $
      x^i_(f(i)) st((i, f) in F, class: CC) x.
    $
]

#th([J. L. Kelley, see @kelley])[
  Let $X$ be a set with a convergence class $CC$. For a set $A subset X$, define $overline(A)$ to be the set of all $x in X$ such that there is a net $(x_i)_(i in I) subset A$ that $CC$-converges to $x$. Then map $A |-> overline(A)$ is a closure operator that endows $X$ with a topology in which a net $(x_i)_(i in I) subset X$ converges to $x in X$ iff it $CC$-converges to $x$.
]

= The topology of synchronous convergence

#th[
  Let $X$ and $Y$ be two convergence spaces, and let $CC = CC(X,Y) subset Y^X$ be the family of all continuous maps from $X$ to $Y$. For a directed set $I$, a net $(f_i)_(i in I) subset CC$, and a point $f in CC$, we say that $f_i$ converges to $f$ if and only if for every directed set $J$ with a monotone final map $sigma : J -> I$, and any net $(x_j)_(j in J) subset X$, we have
  $
    f_sigma(j)(x_j) stretch(->)_(j in J) f(x) in Y.
  $
  We claim that the set $cal(S)$ consisting of pairs $((f_i)_(i in I), f)$ such that $f_i stretch(->)_(i in I) f$ as defined above, is a convergence class on $CC$, and subsequently provides a topology on $CC$, called the topology of *semi-uniform convergence.*\
]
#pf[
  We first need to verify four axioms that a convergence class must satisfy:
  + Let $I$ be a directed set, and let $f in CC$. Since $f$ is continuous, for any directed set $J$ and any net $(x_j)_(j in J) subset X$ that converges to $x in X$, we have $f(x_j) stretch(->)_(j in J) f(x) in Y$. Therefore the net $(f)_(i in I)$ converges to $f$ in $CC$.
  + We need to show that any subnet of a convergent net converges to the same point. Let $(f_i)_(i in I) subset CC$ be a net that converges to $f in CC$, and let $J$ be a directed set with $sigma : J -> I$. To show that the subnet $(f_sigma(j))_(j in J)$ converges to $f$, consider another directed set $K$, mapped to $J$ via $tau : K -> J$, and a net $(x_k)_(k in K) subset X$ that converges to $x in X$. Since the map $sigma circ tau : K -> I$ is monotone and final, by the definition of convergence we see that
    $
      f_(sigma(tau(k)))(x_k) stretch(->)_(k in K) f(x),
    $
    which means that $f_sigma(j) stretch(->)_(j in J) f$ in $CC$, as desired.
  + Let $(f_i)_(i in I) subset CC$ be a net and assume that every subnet of $(f_i)_(i in I)$ has a subnet that converges to $f in CC$. We need to show that the net $(f_i)_(i in I)$ itself converges to $f$. To that end, let $J$ be a directed set with a map $sigma : J -> I$, together with a net $(x_j)_(j in J) subset X$ that converges to $x in X$. Assume that the net $(f_sigma(j) (x_j))_(j in J)$ does *not* converge to $f(x)$ in $Y$. That means that there is a neighborhood $U$ of $f(x)$ and a subnet $(f_(sigma(tau(k))) (x_tau(k)))_(k in K)$, indexed by a directed set $K$ with $tau : K -> J$, such that $f_sigma(tau(k)) (x_tau(k)) in.not U$ for all $k in K$.\
    At the same time, defining $alpha : K -> I$ by $alpha = sigma circ tau$, we see that $(f_(alpha(k)))_(k in K)$ is a subnet of $(f_i)_(i in I)$. Therefore, this subnet itself has a subnet that converges to $f$, i.e. there is a directed set $L$ with a map $beta : L -> K$, such that $f_alpha(beta(l)) stretch(->)_(l in L) f in CC$. In particular, this implies that
    $
      f_sigma(tau(beta(l))) (x_(tau(beta(l)))) stretch(->)_(l in L) f(x).
    $
    But this is contradictory, since $f_sigma(tau(beta(l)))(x_tau(beta(l))) in.not U$ for all $l in L$.
  + Finally, we need to show the diagonal property. Let $(f_i)_(i in I) subset CC$ be a net converging to $f in CC$. For every $i in I$, consider also a directed set $J_i$ and a net $(f'_((i, j)))_(j in J_i) subset CC$ that converges to $f_i$. Let
    $
      K := I times product_(i in I) J_i,
      #h(1cm) I times J := {(i,j) hs mid(|) hs i in I aa j in J_i},
    $
    with the preorder on $K$ defined pointwise, and consider $R : K -> I times J$ defined by $R(i, alpha) = (i, alpha(i))$. We then need to show that the net
    $
      (f'_(R(i, alpha)))_((i,alpha) in K) subset CC
    $
    converges to $f$. To that end, consider a directed set $L$ with $tau : L -> K$ and a net $(x_l)_(l in L) subset X$ converging to $x in X$. We need to show the convergence
    $
      f'_R(tau(l)) (x_l) stretch(->)_(l in L) f(x) in Y.
    $
    Since the above convergence is topological, we can show it in the usual way. Let $U$ be a neighborhood of $f(x)$ in $Y$. We seek $l_0 in L$ such that
    $
      forall l >= l_0 wh f'_R(tau(l)) (x_l) in U.
    $
    Consider the map $eta : L -> I$ defined by $eta(l) = i$, where $(i,alpha) = tau(l)$. Clearly, $eta$ is a monotone final map, so by the definition of convergence, $f_i stretch(->)_(i in I) f$ implies that
    $
      f_eta(l) (x_l) stretch(->)_(l in L) f(x) in Y.
    $
    Hence, there is $l_0 in L$ such that for all $l >= l_0$, we have $f_eta(l) (x_l) in U$. Now, for any $l$, we have the convergence
    $
      f'_((eta(l), j)) stretch(->)_(j in J_eta(l)) f_eta(l) in CC.
    $
    Applying the definition of convergence for the constant net $(x_l)_(j in J_eta(l)) subset X$, we see that
    $
      f'_((eta(l), j))(x_l) stretch(->)_(j in J_eta(l)) f_eta(l)(x_l) in Y.
    $
    Therefore, for all $l >= l_0$, there is $j_0^l in J_eta(l)$ such that for all $j >= j_0^l$, we have $f'_((eta(l), j))(x_l) in U$. Next, we define $alpha_0 in product_(i in I) J_i$ as follows:
    $
      alpha_0 (i) := cases(
        j_0^l\,#hs "if" i = eta(l) "with" l >= l_0\,#v(15pt),
        "any" j in J_i\,#hs "otherwise".
      )
    $
    We then have $(eta(l_0), alpha_0) in K$, and since $tau : L -> K$ is final, there is $l_1 in L$ such that $l_1 >= l_0$ and $tau(l_1) >= (eta(l_0), alpha_0)$.\
    Now, consider any $l >= l_1$, with $tau(l) = (i, alpha)$. Since $tau(l) >= tau(l_1) >= (eta(l_0), alpha_0)$, we see that $alpha >= alpha_0$, and so $alpha(i) >= alpha_0 (i)$ for all $i in I$. Since $l >= l_0$ and $alpha(eta(l)) >= alpha_0 (eta(l)) = j_0^l$, we have
    $
      f'_R(tau(l)) (x_l) = f'_((eta(l), alpha(eta(l)))) (x_l) in U.
    $
    Since the neighbourhood $U$ was arbitrary, this implies the convergence
    $
      f'_R(tau(l)) (x_l) stretch(->)_(l in L) f(x) in Y,
    $
    as desired.

  This shows that our notion of convergence on $CC$ is a convergence class, and hence the closure operator defined by
  $
    overline(E) := {f in CC hs mid(|) hs exists#hh (f_i)_(i in I) subset E st f_i stretch(->)_(i in I) f}
  $
  endows $CC$ with a topology in which convergence coincides with the one defined by $cal(S)$.
]

#prop[
  Let $X$ and $Y$ be topological spaces and assume that $X$ is first countable. Construct the topology on $CC = CC(X,Y)$ as above. Then a sequence ${f_k}_(k = 1)^oo subset CC$ will converge to $f in CC$ if and only if $f_k (x_k) -> f(x)$ in $Y$ whenever $x_k -> x$ in $X$.
] <seq>
#pf[
  Consider a sequence ${f_k}_(k = 1)^oo subset CC$. Suppose that it converges to a point $f in CC$. Note that this sequence is a net with $I = NN$. Taking $J = I = NN$ and $sigma = "id"$, we see that for any sequence ${x_k}_(k = 1)^oo subset X$ converging to $x in X$, we have
  $
    f_k (x_k) stretch(->)_(k -> oo) f(x).
  $ <seqconv>
  Conversely, suppose that $f_k (x_k) -> f(x)$ whenever $x_k -> x in X$. Let us first see that for any subsequence ${f_(k_l)}_(l = 1)^oo$ and any sequence $x_l -> x in X$, we have $f_(k_l)(x_l) -> f(x) in Y$. Indeed, given such sequences, for any $k in NN$ we define $alpha(k)$ to be the minimum of all $l in NN$ such that $k <= k_l$. Then the sequence ${x_(alpha(k))}_(k = 1)^oo$ converges to $x$, because if $x_l in V in.rev x$ for all $l >= l_0$, then for all $k >= k_(l_0)$, we have $alpha(k) >= alpha(k_(l_0)) = l_0$, and so $x_alpha(k) in V$.\
  Now, since $alpha(k_l) = l$ for all $l in NN$, the sequence ${f_(k_l) (x_l)}_(l = 1)^oo$ is a subsequence of ${f_k (x_(alpha(k)))}_(k = 1)^oo$. And since the latter converges to $f(x)$ by (@seqconv), so does the former.

  Finally, we show that $f_k stretch(->)_(k -> oo) f in CC$. Let $J$ be a directed set with a monotone final map $sigma : J -> NN$, and let $(x_j)_(j in J) subset X$ be a net that converges to $x in X$. We need to show that the net $(f_sigma(j)(x_j))_(j in J)$ converges to $f(x)$. Assume the contrary. Then we have a neighborhood $U$ of $f(x)$ and a subnet $(f_sigma(tau(l)) (x_tau(l)))$, with $tau : L -> J$, such that
  $
    forall l in L wh f_sigma(tau(l)) (x_tau(l)) in.not U.
  $ <stayaway>
  Since $X$ is first countable, since the net $(x_tau(l))_(l in L)$ converges to $x$, we can find a sequence ${l_i}_(i = 1)^oo$ such that the sequence ${x_tau(l_i)}_(i = 1)^oo$ converges to $x$. Furthermore, by ensuring that $sigma(tau(l_(i+1))) > sigma(tau(l_i))$, we can define $k_i := sigma(tau(l_i))$ and obtain a subsequence ${f_(k_i)}_(i = 1)^oo$ of ${f_k}_(k = 1)^oo$. As shown before, we then have
  $
    f_sigma(tau(l_i)) (x_tau(l_i)) stretch(->)_(i -> oo) f(x),
  $
  which contradicts (@stayaway). It then follows that $f_k stretch(->)_(k -> oo) f$, as desired.
]

#prop[
  If $X$ is a topological space and $Y$ is a TVS, then the space $CC(X,Y)$, with the topology of semi-uniform convergence and pointwise linear structure, is also a TVS.
] #pf[
  Follows easily from the definition of the topology on $CC(X,Y)$ and the fact that $Y$ is a TVS.
]

#def[
  Let $X$ be a first countable topological vector space, and let $n in NN_0$.

  The _curried function set_ $H_n (X)$ is defined as follows:
  - If $n = 0$, we set $H_0 (X) := X$;
  - If $H_n (X)$ is defined, we define $H_(n+1) (X)$ to be the set of all functions from $X$ to $H_n (X)$.

  The _curried continuous space_ $C_n (X)$ is a TVS, defined recursively:
  - If $n = 0$, we set $C_0 (X) := X$;
  - If $C_n (X)$ is defined, we set $C_(n+1) (X) := CC(X, C_n (X))$, with pointwise linear structure and the topology of semi-uniform convergence.
]

#rem[
  Any function $f in C_n (X)$ naturally corresponds to a multivariable function $tilde(f) : X^n -> X$:
  $
    tilde(f)(x_1, x_2, ..., x_n) = f(x_1)(x_2)...(x_n).
  $
]

#lm[
  For all $n in NN$, a function $f in H_n (X)$ lies in $C_n (X)$ if and only if the corresponding function $tilde(f) : X^n -> X$ is continuous.
] #pf[
  First assume that $f in C_n (X)$. To show that $tilde(f)$ is continuous, consider a sequence $x_k^((n)) -> x_0^((n)) = (x_0^1, x_0^2, ..., x_0^n) in X^n$. Since $f$ is continuous, we see that $f(x_k^1) -> f(x_0^1)$. If $n = 1$, we are done. Otherwise, the convergence $f(x_k^1) -> f(x_0^1)$ occurs in the topology of semi-uniform convergence, and so by @seq we have
  $
    f(x_k^1)(x_k^2) -> f(x_0^1)(x_0^2).
  $
  Repeating this argument as needed, we obtain
  $
    f(x_k^1)(x_2^1)...(x_k^n) -> f(x_0^1)(x_0^2)...(x_0^n),
  $
  which is to say that $tilde(f)(x_k^((n))) -> tilde(f)(x_0^((n)))$, as desired.\

  We will prove the converse by induction.
  - If $n = 1$, then the statement is trivial.
  - Suppose the statement is proven for $C_n (X)$. Consider $f in H_(n+1) (X)$ such that $tilde(f) : X^(n+1) -> X$ is continuous. By the induction hypothesis, we know that $f(x) in C_n (X)$ for all $x in X$, so $f$ is a function from $X$ to $C_n (X)$. It remains to show that $f$ is continuous. This is done in the same way as the first part of our proof.
]

#bibliography("bibliography.yml")
