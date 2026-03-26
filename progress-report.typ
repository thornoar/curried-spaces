#import "@local/templates:0.0.0": *
#import "@local/common:0.0.0": *

#show: assignment-title-rule(
  title: [SCIE2500 Progress Report: Curried Functional Spaces],
  due: [Fri, Mar 27],
  header: [Curried Functional Spaces #h(1fr) SCIE2500 Progress Report],
  ext1: [Supervisor: JIN, Tianling],
  // ext2: [#total-words],
  fontsize: 14pt,
)

#set heading(numbering: "1.")

= Introduction

The study of real-valued multivariable functions is traditionally done by expanding the domain from $RR$ to $RR^n$. However, there is an alternative way to represent a function of many arguments, primarily used in a field of mathematical logic called _lambda calculus._ @barend This involves treating a function $f : RR^n -> RR$ as a single-variable function that receives a real number $x_1 in RR$ and produces _another function_ $f_(x_1) : RR^(n-1) -> RR$, now of $n-1$ arguments. In other words, we are "partially applying" the function $f$ to the argument $x_1$. Continuing this process, we obtain what is called the _curry_ of the function $f$, denoted $gamma(f)$:
$
  gamma(f) : RR -> (RR -> (RR -> ... -> (RR -> RR) ... ))
$
Both these representations are equivalent in the sense that the correspondence $f <-> gamma(f)$ constitutes a bijective map. A natural question arising from this observation, is whether this equivalence stretches over continuity and differentiability, and whether one can obtain non-trivial results about a multivariable function by studying its curry.

= Survey of the literature
#set enum(numbering: "(1)")
The study of curried functions naturally brings us to the field of functional analysis, since it involves inductively building spaces of functions whose codomain is again a space of functions. A number of fundamental works are instrumental here:
+ N. Bourbaki, _General Topology, Part II,_ 1966. @bou2
  This textbook deals (among all else) with topologies on various sets of functions $f : X -> Y$, where $X$ and $Y$ are topological spaces. Of particular interest are the _topology of pointwise convergence_ which facilitates the general curried function space $H_n (RR)$, and the _compact-open topology_ which serves as the basis for the spaces $C_n (RR)$ of continuous curried functions.

+ W. Rudin, _Functional Analysis,_ 1991. @rud
  This work introduces the theory of topological vector spaces which are central in functional analysis. In particular, it builds the toolkit for effectively working with neighborhoods of zero, and also provides more advanced results concerning metrizability and completeness.
  W. Rudin's book also contains a discussion of _generalized functions_ which may be related to our topic of interest.

+ R. Beattie amd H.-P. Butzmann, _Convergence Structure and Applications to Functional Analysis,_ 2002. @bb
  In this monograph, the authors develop the theory of _convergence structure,_ which is a generalization of topology (in the sense that every topological space naturally induces a convergence structure). Although this book does not directly contribute to the study of curried functions, it provides some useful results about the compact-open topology, specifically its reformulation into the language of filters and convergence.

+ N. Bourbaki, _General Topology, Part I,_ 1966. @bou1
  We use this textbook since it gives an introduction to filters in a topological space and contains many fundamental results about filters. Having these results makes it easier to prove that the spaces of curried multivariable functions are in fact topological vector spaces.

What pertains to literature directly studying curried functions in the setting of multivariable calculus, we are not aware of any such literature.

= Research methodology

Our study is focused on three families of spaces: $H_n (RR)$ (general curried functions), $C_n (RR)$ (continuous curried functions), and $D_n^m (RR)$ (continuously $m$-times differentiable functions). All of these spaces are Hausdorff, locally convex topological vector spaces that are defined by induction on $n$ and $m$. We then proceed to apply results from functional analysis to these spaces, to yield statements about regular multivariable functions.

= Main results
#let fr = [Fréchet]

So far, we have shown that

+ The following isomorphisms take place: #h(1fr)
  $
    H_n (RR) tilde.equiv_"Top" "Hom"_"Set" (RR^n, RR), #h(1em) C_n (RR) tilde.equiv_"Top" CC(RR^n, RR), #h(1em) D_n^m (RR) tilde.equiv_"Set" C^m (RR^n),
  $
  i.e. we extend the equivalence $f <-> gamma(f)$ to continuous and differentiable functions.

+ We have studied the properties of the spaces $H_n (RR)$, $C_n (RR)$, and $D_n^m (RR)$. All of them are Hausdorff, complete, locally convex topological vector spaces.
  Moreover, the spaces $C_n (RR)$ and $D_n^m (RR)$ are metrizable, which turns them into #fr spaces. This is especially valuable since #fr spaces are known to hold many strong properties.

The "disadvantage" of curried functions is a somewhat narrower scope: only one variable can be consumed at a time. On the other hand, they allow us to consider multivariable functions as functions of a single variable, therefore reducing complexity in certain applications.

= Further research directions

Now that we have established the basic properties of the curried function spaces, it remains to explore problems in multivariable calculus and find out whether they can be more easily solved by means of currying functions.

Potential tools include the Banach-Steinhaus and Hahn-Banach theorems, the open mapping and closed graph theorems, and other results from functional analysis.

#bibliography("bibliography.yml", style: "american-medical-association")
