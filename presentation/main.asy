import smoothmanifold;
config.drawing.fill = false;
config.drawing.drawnow = true;
config.drawing.drawnow = true;
config.arrow.mar = 0.03;
config.arrow.currentbar = DeferredBar(10, true, false);
config.drawing.subsetfill = new pen[] {gray(0.85)};
config.system.repeatlabels = true;

usepackage("tgschola");
usepackage("amsmath");
usepackage("graphicx");
usepackage("setspace");
usepackage("xcolor", "dvipsnames");

pair p1, p2, p3, p4;
picture tmp;

int count = 0;
string sbul() {
    count += 1;
    return "{" + (string)count + ".}\hspace{8pt}";
}

orientation = Landscape;
defaultpen(1pt);
import slide;
pagenumberpen = invisible;

// // real ratio = pageheight/pagewidth;
// real ratio = 1;
// path circ(pair c, real r) {
//     return shift(c) * xscale(ratio) * circle((0,0), r);
// }

real mar = 0.05;

pair top = (0,0.65);
pair bot = (0,-1 + 2*mar);
pair lft = (-whr + mar, 0);
pair rgt = (whr - mar, 0);

pair tl = top + lft;
pair tr = top + rgt;
pair bl = bot + lft;
pair br = bot + rgt;

real st = .05;
pair vs = (0, st);
pair hs = (st, 0);

pair textst = top + lft - 0*vs + 2 * hs;

void drawline(picture pic = currentpicture) {
    draw(pic, (lft.x + st, p1.y) -- (rgt.x - st, p1.y));
}

titlepage(
    "Curried Functional Spaces",
    "Roman Maksimovich\\ Supervisor: JIN, Tianling",
    institution = "Hong Kong University of Science and Technology",
    date = "\today"
);

// ---

title("Premise", position = (0,1));
picture pr1, pr2;
dpar nodepar = nodepar();
draw(pr1, (top + vs) -- (bot + vs));
label(pr1, Label("Multivariable functions", position = top + lft / 2));
label(pr1, Label("$\mathbb{R}^n \to \mathbb{R}$", position = top + lft / 2 - 2.5 * vs));
label(pr2, Label("Curried functions", position = top + rgt / 2));
label(pr2, Label("$\mathbb{R} \to (\mathbb{R} \to (\dots (\mathbb{R} \to \mathbb{R})))$", position = top + rgt / 2 - 2.65 * vs));
smooth args = smooth(convexpaths[3]).scale(0.2).shift(top + lft/2 - 9 * vs);
draw(pr1, args);
label(pr1, "$x_1$", (-.72,.12));
label(pr1, "$x_2$", (-.63,.23));
label(pr1, "$x_3$", (-.53,.1));
smooth output = node("$f(x_1, x_2, x_3)$", size = .08).shift((-.6,-.4));
draw(pr1, output, dspec = nodepar);
drawarrow(pr1, args, output);
pair c1 = (.17,-.55);
pair d1 = (1.1,.17);
pair c2 = (.48, c1.y + mar);
pair d2 = d1 - (mar, mar);
smooth arg1 = smooth(convexpaths[0]).scale(0.08).shift((.25,.32)).setlabel("$x_1$", 0, 0);
smooth f1 = smooth(contour = box(c1, d1));
smooth arg2 = smooth(convexpaths[2]).scale(0.08).shift((.29, .09)).setlabel("$x_2$", 0, 0);
smooth f2 = smooth(contour = box(c2, d2));
smooth arg3 = smooth(convexpaths[0]).scale(0.08).shift((.61, .0)).setlabel("$x_3$", 0, 0);
draw(pr2, arg1);
draw(pr2, f1);
draw(pr2, arg2);
draw(pr2, f2);
draw(pr2, arg3);
draw(pr2, output.shift(((c2.x + d2.x)/2 - output.center.x, 0)), dspec = nodepar);
drawarrow(pr2, arg1, f1, curve = -.4, help = false);
drawarrow(pr2, arg2, f2, points = new pair[]{(.32,-.1), (.325,-.15), (.35,- .21)}, help = false);
drawarrow(pr2, arg3, output, curve = -.2);
label(pr1, Label("Multivariate calculus"), (bot + lft/2 + 3*vs));
label(pr2, Label("$\lambda$-calculus,"), (bot + rgt/2 + 4*vs));
label(pr2, Label("functional programming"), (bot + rgt/2 + 2*vs));
add(pr1);
add(pr2);

// ---

title("Premise");
add(pr2);
label(Label("Multivariate calculus"), (bot + lft/2 + 3*vs), red);
draw(top -- bot, red);
draw((0,0){(-1,0)} .. (-.5,-.2) .. {(0,-1)}(bot + lft/2 + 4.5*vs), red, arrow = Arrow(SimpleHead), L = Label("?", position = MidPoint, align = Relative(E)));

// ---

config.arrow.currentbar = null;
title("Continuous Functions");
p1 = textst;
p1 += vs;
label(tmp, minipage("
$C_n (\mathbb{R})$ --- the space of continuous $n$-ary curried functions:
\begin{enumerate}
    \item $C_0 (\mathbb{R}) := \mathbb{R}$
    \item $C_{n+1} (\mathbb{R}) := \{ f \colon \mathbb{R} \to C_n (\mathbb{R}) \mid f \text{ is continuous} \}$
\end{enumerate}
", width = 22cm), p1, align = (1,-1));
p1 -= 7*vs;
add(tmp);

// ---

title("Continuous Functions");
add(tmp);
draw((.145,.33) -- (.55,.33), red);
p2 = (-.15,-.4);
draw(p2{(-1,0)} .. (-.17,-.1) .. {(0,1)}(.3475,.33), red);
label("what is the topology on $C_n (\mathbb{R})$?", p2, red, align = (1,0));

// ---

title("Continuous Functions");
add(tmp);
draw((-.3,.32) -- (-.09,.32));
p2 = (-1.06,.04);
draw(p2{(-1,.3)} .. (-1.15,.12) .. (-1.0,.23) .. {(0,1)}(-.195,.32));
label("compact-open topology: $C_n (\mathbb{R}) = \mathcal{C}(\mathbb{R}, C_{n-1}(\mathbb{R}))$", p2, align = (1,0));
p1 -= 8 * vs;
drawline();
p1 -= 1.5 * vs;
smooth xspace =
    smooth(box(bot + lft + (2*st,st), (-5*st, p1.y)))
    .setlabel("$X$", dir = dir(137), align = 1.5*S)
    .addsubset(convexpaths[2], scale = .75, unit = true, shift = (.1,.1), rotate = 60)
    .setlabel(0, "$K$", dir(210));
xspace.subsets[0].layer = 1;
smooth yspace =
    smooth(box((5*st, bot.y + st), (rgt.x - 2*st, p1.y)))
    .setlabel("$Y$", dir = dir(43), align = 1.5*S)
    .addsubset(convexpaths[0], scale = .75, unit = true, shift = (.0, .0))
    .addsubset(convexpaths[6], scale = .41, unit = true, shift = (-.15, .15))
    .setlabel(0, "$U$", dir = dir(139))
    .setlabel(1, "$f(K)$", dir = dir(-50));
draw(xspace);
draw(yspace, dpar(subsetcontourpens = new pen[] {dashed, currentpen}));
p1 = (0, -.28);
drawarrow(xspace, yspace, bar = null, curve = -.2);
label("$f$", p1); p1 -= 1.8*vs;
label("\rotatebox[origin=c]{-90}{$\in$}", p1); p1 -= 1.8*vs;
label("$V(K, U)$", p1); p1 -= 1.6*vs;
label("\rotatebox[origin=c]{-90}{$\subset$}", p1); p1 -= 1.8*vs;
label("$\mathcal{C}(X, Y)$", p1); p1 -= 1.8*vs;

// ---

title("Topological Vector Spaces");
erase(tmp);
p1 = textst;
label(tmp, "\textbf{Remark:} If $f_1, f_2 \in C_n (\mathbb{R})$, then $\alpha f_1 + \beta f_2 \in C_n (\mathbb{R}).$", p1, align = (1,0));
p1 -= 2*vs;
add(tmp);

// ---

title("Topological Vector Spaces");
drawline(tmp); p1 -= 1*vs;
label(
    tmp,
    minipage(
        "\textbf{Definition:} $X$ is a {\color{green} TVS} $\Leftrightarrow$
        $X$ has {\color{Dandelion} topological}
        \emph{and} {\color{blue} vector} structure,
        and they are \emph{compatible}:
        \begin{enumerate}
            \item $(+) \colon X \times X \to X$ is continuous;
            \item $(\cdot) \colon \mathbb{R} \times X \to X$ is continuous.
        \end{enumerate}",
        width = 20cm
    ),
    p1, align = (1,-1));
p2 = (0,-.5);
dot(tmp, "$0$", p2, align = S);
smooth u0 =
    smooth(convexpaths[0], scale = .25, shift = p2 + (.0,.1))
    .setlabel("$U - x$", dir(80));
smooth v0 =
    smooth(convexpaths[5], scale = .25, shift = p2 + (.05, -.07))
    // .rotate(90)
    .setlabel("$V - y$", dir(220));
config.drawing.drawnow = false;
config.drawing.gaplength = 0.03;
draw(tmp, u0);
draw(tmp, v0, dpar(smoothoverlap = false));
pair x = (-.8,-.5), y = (.8,-.2);
smooth ux = u0.copy().shift(x - p2).setlabel("$U$", dir(120));
dot(tmp, "$x$", x, align = W);
draw(tmp, ux);
smooth vy = v0.copy().shift(y - p2).setlabel("$V$", dir(60));
dot(tmp, "$y$", y, align = E);
draw(tmp, vy);
drawarrow(tmp, ux, u0, curve = -.3, L = Label("$-x$", position = MidPoint, align = Relative(W)));
drawarrow(tmp, vy, v0, curve = -.45, L = Label("$-y$", position = MidPoint, align = Relative(W)));
drawarrow(tmp, start = p2, finish = x, arrow = DeferredArrow(SimpleHead), beginmargin = .02);
drawarrow(tmp, start = p2, finish = y, arrow = DeferredArrow(SimpleHead), beginmargin = .02);
add(tmp);

// ---

title("Properties of Topological Vector Spaces");
erase(tmp);
label(tmp, "Metrizability", top + 2/3 * lft);
label(tmp, "Local convexity", top);
label(tmp, "Completeness", top + 2/3 * rgt);
pair x1 = (-.35, .24);
real r1 = .13;
pair x2 = (-.11,.34);
real r2 = .09;
smooth metr =
    smooth(concavepaths[5], scale = .28, shift = (-.3, .3))
    .addsubset(circle(x1, r1))
    .addsubset(circle(x2, r2))
    .addelement(x1)
    .addelement(x2)
    .move(shift = (-.58,-.21))
    ;
draw(tmp, metr, dpar(fillsubsets = true, subsetcontourpens = new pen[]{dashed}));
real m = .005;
draw(tmp, shift(metr.elements[0].pos) * (m * dir(40)  -- (r1) * dir(40)), arrow = Arrows(TeXHead), L = Label("$\varepsilon$", align = Relative(0.6*W)));
draw(tmp, shift(metr.elements[1].pos) * (m * dir(-20) -- (r2) * dir(-20)), arrow = Arrows(TeXHead));
p2 = (-.02,.30);
smooth conc =
    smooth(concavepaths[0])
    .scale(.3).rotate(180)
    .shift(p2 + (.04,-.13))
    .setlabel("$\forall U$", dir(205), 2.5*S)
    .addsubset(convexpaths[3], unit = true, scale = .5, shift = (-.08, .29))
    .setlabel(0, "$\exists V$", dir(-50))
    ;
draw(tmp, conc, dpar(contourpen = red, subsetcontourpens = new pen[] {currentpen}));
dot(tmp, p2, L = Label("$0$", align = E));
srand(2);
pair incirc(pair ctr, real rad) {
    return ctr + 2/3 * rad * unitrand() * dir(360 * unitrand());
}
pair c = (.76,.19);
pair p = c;
real r = .52;
real[] rs = {.3, .22, .14, .08, .04};
pen cp = gray(.8);
for (real rp : rs) {
    for (int i = 0; i < 40; ++i) {
        dot(tmp, p, cp);
        p = incirc(c, r);
    }
    cp = (.6 * cp + .4 * black);
    c = p;
    r = rp;
    filldraw(tmp, circle(c, r), fillpen = opacity(.2), drawpen = blue);
}
dot(tmp, c, cyan);
p1 = bot + 2/3 * lft + 3 * vs;
label(tmp, "Fr\'echet space", p1);
p2 = p1 + 2*vs;
draw(tmp, p2{(0,1)} .. {(0,1)}(top + 2/3 * lft - 17*vs));
draw(tmp, p2{(0,1)} .. {(0,1)}(top - 17*vs));
draw(tmp, p2{(0,1)} .. {(0,1)}(top + 2/3 * rgt - 17*vs));
add(tmp);

// ---

title("Properties of Topological Vector Spaces");
add(tmp);
draw((bot - 1*hs + 3*vs) -- (p1 + 6.5*hs), L = Label("Curried function spaces $C_n (\mathbb{R})$", position = BeginPoint, align = 2*E), arrow = Arrow(SimpleHead), red);

// ---

title("Continuous Functions");
p1 = textst+.5*vs;
p1 += vs;
label(minipage("
$C_n (\mathbb{R})$ --- the space of continuous $n$-ary curried functions:
\begin{enumerate}
    \item $C_0 (\mathbb{R}) := \mathbb{R}$;
    \item $C_{n+1} (\mathbb{R}) := \mathcal{C}(\mathbb{R}, C_n (\mathbb{R}))$, with the compact-open topology.
\end{enumerate}
", width = 23cm), p1, align = (1,-1));
p1 -= 9*vs;
drawline();
p1 -= 1*vs;
label(minipage("
\textbf{Results:} for all $n \in \mathbb{N}$,
\begin{enumerate}
    \item $C_n (\mathbb{R})$ is a Hausdorff topological vector space;
    \item There is an isomorphism $\gamma \colon \mathcal{C}(\mathbb{R}^n, \mathbb{R}) \leftrightarrow C_n (\mathbb{R})$;
    \item $C_n (\mathbb{R})$ is a Fr\'echet space.
\end{enumerate}
", width = 22cm), p1, align = (1,-1));
p1 -= 11.5*vs;
drawline();
p1 -= 1*vs;
label(minipage("
$\Rightarrow$ Theorems from functional analysis apply:
\begin{enumerate}
    \item Uniform boundedness principle;
    \item Open mapping theorem;
    \item \dots
\end{enumerate}
", width = 22cm), p1, align = (1,-1));

// ---

title("Differentiable functions");
erase(tmp);
p1 = textst+.5*vs;
label(tmp, minipage("
% \onehalfspacing
\baselineskip=1.2\baselineskip
$D^{{\color{blue} m}}_{\color{red} n} (\mathbb{R})$ --- the space of ${\color{red} n}$-ary ${\color{blue} m}$ times differentiable functions:
\begin{enumerate}
    \item $D_0^m (\mathbb{R}) := \mathbb{R}$;
    \item $D_n^0 (\mathbb{R}) := C_n (\mathbb{R})$;
    \item If $n,m > 0$, then $D_n^m (\mathbb{R})$ consists
        of all such\\ $f \in \mathcal{C}(\mathbb{R}, D_{n-1}^m (\mathbb{R}))$,
        that there is $f' \in D_n^{m-1}(\mathbb{R})$ with
\end{enumerate}
    $$
        \frac{f(x + h) - f(x)}{h} \underset{h \to 0}{\longrightarrow} f'(x).
    $$
", width = 23cm), p1, align = (1,-1));
add(tmp);

// ---

title("Differentiable functions");
add(tmp);
p2 = (-.1,-.6);
draw(p2{(-1,0)} .. (-.2,-.3) .. {(1,1)} (.09,-.17), arrow = Arrow(SimpleHead), red, L = Label("pointwise convergence!", position = BeginPoint, align = 1.5*E));
label(minipage("
$$
    f_k \underset{k \to \infty}\longrightarrow f \Leftrightarrow f_k (x_1)\dots (x_n) \underset{k \to \infty}\longrightarrow f(x_1)\dots (x_n)
$$
", width = 15cm), p2 + 9 * hs, align = (0,-1));

// ---

title("Differentiable functions");
add(tmp);
p1 = textst - 19.3*vs;
drawline();
p1 -= 1*vs;
label(minipage("
The topology on $D_n^m$ is \emph{coarsest} such that the maps
\begin{align*}
    i \colon D_n^m (\mathbb{R}) &\to \mathcal{C}(\mathbb{R}, & D_{n-1}^m(\mathbb{R})), \hspace{2cm} d \colon D_n^m (\mathbb{R}) &\to D_n^{m-1}(\mathbb{R})\\
    f &\mapsto f & f &\mapsto f'
\end{align*}
are continuous. In particular, $f_k \to f \Rightarrow f'_k \to f'$.
", width = 22cm), p1, align = (1,-1));

// ---

title("Differentiable functions");
p1 = textst+.5*vs;
label(minipage("
$D^{{\color{blue} m}}_{\color{red} n} (\mathbb{R})$ --- the space of ${\color{red} n}$-ary ${\color{blue} m}$ times differentiable functions:
", width = 23cm), p1, align = (1,-1));
p1 -= 3.5*vs;
drawline();
p1 -= 1*vs;
label(minipage("
\textbf{Results:} for all $m,n \in \mathbb{N}$,
\begin{enumerate}
    \item $D_n^m (\mathbb{R})$ is a Hausdorff topological vector space;
    \item The inclusion map $j \colon D_n^{m+1}(\mathbb{R}) \to D_n^m (\mathbb{R})$ is continuous;
    \item There is an isomorphism $\gamma \colon C^m (\mathbb{R}^n) \leftrightarrow D_n^m (\mathbb{R})$, given by
        $$
            \gamma\left(\tilde{f}\right)(x_1)(x_2)\dots (x_n) = \tilde{f}(x_1, x_2, \dots, x_n).
        $$
    \item $D_n^m (\mathbb{R})$ is a Fr\'echet space.
\end{enumerate}
", width = 22cm), p1, align = (1,-1));

// ---

title("Future directions");
p1 = textst;
label(minipage("
\baselineskip=1.2\baselineskip
\begin{enumerate}
    \item Apply results from functional analysis to derive facts about $C_n (\mathbb{R})$ and $D_n^m (\mathbb{R})$;
    \item Study complex curried functions, $C_n (\mathbb{C})$ and $D_n^m (\mathbb{C})$;
    \item Define Riemann integrals on $C_n (\mathbb{R})$;
    \item Prove analogs of the Inverse/Implicit function theorems.
\end{enumerate}
", width = 23cm), p1, align = (1,-1));

// ---

title("References");
p1 = textst;
label(minipage("
\baselineskip=1.2\baselineskip
\begin{enumerate}
    \item[{[1]}]\ N. Bourbaki, \emph{General Topology, Part I.} 1966
    \item[{[2]}]\ N. Bourbaki, \emph{General Topology, Part II.} 1966
    \item[{[3]}] \ R. Beattie and H.-P. Butzmann, \emph{Convergence Structures and Applications to Functional Analysis.} 2002
    \item[{[4]}]\ W. Rudin, \emph{Principles of Mathematical Analysis.} 1976
    \item[{[5]}]\ W. Rudin, \emph{Functional Analysis.} 1976
\end{enumerate}
", width = 23cm), p1, align = (1,-1));

// drawgrid();
