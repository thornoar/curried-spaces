#import "@local/templates:0.0.0": *
#import "@local/common:0.0.0": *

#show: assignment-title-rule(
  title: [Progress Report: Curried Functional Spaces],
  due: [Fri, Mar 27],
  header: [Curried Functional Spaces #h(1fr) Progress Report],
  ext1: [Supervisor: JIN, Tianling],
  ext2: [#total-words],
  fontsize: 14pt,
)

#set heading(numbering: "1.")

= Abstract

The study of real-valued multivariable functions is traditionally done by expanding the domain from $RR$ to $RR^n$. However, there is an alternative way to represent a function of many arguments, primarily used in a field of mathematical logic called _lambda calculus._ @barend This involves treating a function $f : RR^n -> RR$ as a single-variable function that receives a real number $x_1 in RR$ and produces _another function_ $f_(x_1) : RR^(n-1) -> RR$, now of $n-1$ arguments. In other words, we are "partially applying" the function $f$ to the argument $x_1$. Continuing this process, we obtain what is called the _curry_ of the function $f$, denoted $gamma(f)$:
$
  gamma(f) : RR -> (RR -> (RR -> ... -> (RR -> RR) ... ))
$
Both these representations are equivalent in the sense that the correspondence $f <-> gamma(f)$ constitutes a bijective map. A natural question arising from this observation, is whether this equivalence stretches over continuity and differentiability, and whether one can obtain non-trivial results about a multivariable function by studying its curry.

= Survey of the literature
#set enum(numbering: "(1)")
The study of curried functions naturally brings us to the field of functional analysis, since it involves inductively building spaces of functions whose codomain is again a space of functions. A number of fundamental works are instrumental here:
+ N. Bourbaki, _General Topology, Part II,_ 1966.
  This textbook deals (among all else) with topologies on various sets of functions $f : X -> Y$, where $X$ and $Y$ are topological spaces. Of particular interest are the _topology of pointwise convergence_ which facilitates the general curried function space $H_n (RR)$, and the _compact-open topology_ which serves as the basis for the spaces $C_n (RR)$ of continuous curried functions.

+ W. Rudin, _Functional Analysis,_ 1991.
  This work introduces the theory of topological vector spaces which are central in functional analysis. In particular, it builds the toolkit for effectively working with neighborhoods of zero, and also provides more advanced results concerning metrizability and completeness.

+ 

#bibliography("bibliography.yml", style: "american-medical-association")
