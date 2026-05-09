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
// size(pagewidth,pageheight,keepAspect = true);
// tinv=inverse(fixedscaling((-pagewidth/pageheight,-1),(pagewidth/pageheight,1),currentpen));
pagenumberpen = invisible;

real ratio = pageheight/pagewidth;
path circ(pair c, real r) {
    return shift(c) * xscale(ratio) * circle((0,0), r);
}

pair top = (0,0.65);
pair bot = (0,-0.9);
pair lft = (-0.95, 0);
pair rgt = (0.95, 0);

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
    "Roman Maksimovich",
    institution = "Hong Kong University of Science and Technology",
    date = "\today"
);

// FIRST SLIDE

title("Premise", position = (0,1));
picture pr1, pr2;
dpar nodepar = nodepar();
draw(pr1, top -- bot);
label(pr1, Label("Multivariable functions", position = top + lft / 2));
label(pr1, Label("$\mathbb{R}^n \to \mathbb{R}$", position = top + lft / 2 - 2.5 * vs));
label(pr2, Label("Curried functions", position = top + rgt / 2));
label(pr2, Label("$\mathbb{R} \to (\mathbb{R} \to (\dots (\mathbb{R} \to \mathbb{R})))$", position = top + rgt / 2 - 2.65 * vs));
smooth args = smooth(convexpaths[3]).scale(0.2).shift(top + lft/2 - 9 * vs);
draw(pr1, args);
label(pr1, "$x_1$", (-.58,.13));
label(pr1, "$x_2$", (-.45,.25));
label(pr1, "$x_3$", (-.37,.1));
smooth output = node("$f(x_1, x_2, x_3)$", size = .08).shift((-.5,-.4));
draw(pr1, output, dspec = nodepar);
drawarrow(pr1, args, output);
// draw(pr, box(bot + 6 * vs + 2 * hs, top + rgt - 2 * hs - 4.5 * vs));
smooth arg1 = smooth(convexpaths[0]).scale(0.08).shift((.23,.3)).setlabel("$x_1$", 0, 0);
smooth f1 = smooth(contour = box((.14, -.55), (.81, .17)));
smooth arg2 = smooth(convexpaths[2]).scale(0.08).shift((.22, .11)).setlabel("$x_2$", 0, 0);
smooth f2 = smooth(contour = box((.37, -.50), (.77, .12)));
smooth arg3 = smooth(convexpaths[0]).scale(0.08).shift((.48, .0)).setlabel("$x_3$", 0, 0);
draw(pr2, arg1);
draw(pr2, f1);
draw(pr2, arg2);
draw(pr2, f2);
draw(pr2, arg3);
draw(pr2, output.shift(-output.center + (.57,-.4)), dspec = nodepar);
// drawgrid(pr);
drawarrow(pr2, arg1, f1, points = new pair[]{(.34,.3), (.41, .29), (.45,.25)}, help = false);
drawarrow(pr2, arg2, f2, points = new pair[]{(.255,-.1), (.26,-.15), (.29,- .21)}, help = false);
drawarrow(pr2, arg3, output, curve = -.2);
label(pr1, Label("Multivariate calculus"), (bot + lft/2 + 3*vs));
label(pr2, Label("$\lambda$-calculus,"), (bot + rgt/2 + 4*vs));
label(pr2, Label("functional programming"), (bot + rgt/2 + 2*vs));
add(pr1);
add(pr2);

// SECOND SLIDE

title("Premise");
add(pr2);
label(Label("Multivariate calculus"), (bot + lft/2 + 3*vs), red);
draw(top -- bot, red);
draw((0,0){(-1,0)} .. (-.5,-.2) .. {(0,-1)}(bot + lft/2 + 5*vs), red, arrow = Arrow(SimpleHead), L = Label("?", position = MidPoint, align = Relative(E)));

// THIRD SLIDE

config.arrow.currentbar = null;
title("Continuous Functions");
p1 = textst;
label(tmp, "$C_n (\mathbb{R})$ --- the space of continuous $n$-ary curried functions", p1, align = (1,0));
p1 -= 3*vs;
label(tmp, sbul() + "$C_0 (\mathbb{R}) := \mathbb{R}$", p1, align = (1,0));
p1 -= 3*vs;
label(tmp, sbul() + "$C_{n+1} (\mathbb{R}) := \{ f \colon \mathbb{R} \to C_n (\mathbb{R}) \mid f \text{ is continuous} \}$", p1, align = (1,0));
add(tmp);

// FOURTH SLIDE

title("Continuous Functions");
add(tmp);
draw((.14,.31) -- (.46,.31), red);
p2 = (-.15,-.4);
// dot(p1);
draw(p2{(-1,0)} .. (-.17,-.1) .. {(0,1)}(.3,.31), red, arrow = BeginArrow(SimpleHead));
label("what is the topology on $C_n (\mathbb{R})$?", p2, red, align = (1,0));

// FIFTH SLIDE

title("Continuous Functions");
add(tmp);
draw((-.2,.3) -- (-.02,.3));
p2 = (-.7,.04);
draw(p2{(-1,.3)} .. (-.75,.13) .. (-.3,.14) .. {(0,1)}(-.11,.3), arrow = BeginArrow(SimpleHead));
label("compact-open topology: $C_n (\mathbb{R}) = \mathcal{C}(\mathbb{R}, C_{n-1}(\mathbb{R}))$", p2, align = (1,0));
p1 -= 8 * vs;
// draw((lft.x + st, p1.y) -- (rgt.x - st, p1.y));
drawline();
p1 -= 1.5 * vs;
smooth xspace =
    smooth(box(bot + lft + (2*st,st), (-5*st, p1.y)))
    .setlabel("$X$", dir = dir(126), align = 1.5*S)
    .addsubset(convexpaths[2], scale = .7, unit = true, shift = (.1,.1))
    .setlabel(0, "$K$");
xspace.subsets[0].layer = 1;
smooth yspace =
    smooth(box((5*st, bot.y + st), (rgt.x - 2*st, p1.y)))
    .setlabel("$Y$", dir = dir(55), align = 1.5*S)
    .addsubset(convexpaths[0], scale = .8, unit = true, shift = (.0, .0))
    .addsubset(convexpaths[6], scale = .45, unit = true, shift = (-.15, .15))
    .setlabel(0, "$U$", dir = dir(130))
    .setlabel(1, "$f(K)$", dir = dir(-50));
draw(xspace);
draw(yspace, dpar(subsetcontourpens = new pen[] {dashed, currentpen}));
p1 = (0, -.34);
drawarrow(xspace, yspace, bar = null, curve = -.2);
label("$f$", p1); p1 -= 1.8*vs;
label("\rotatebox[origin=c]{-90}{$\in$}", p1); p1 -= 1.8*vs;
label("$V(K, U)$", p1); p1 -= 1.6*vs;
label("\rotatebox[origin=c]{-90}{$\subset$}", p1); p1 -= 1.8*vs;
label("$\mathcal{C}(X, Y)$", p1); p1 -= 1.8*vs;

// SIXTH SLIDE

title("Topological Vector Spaces");
erase(tmp);
p1 = textst;
label(tmp, "\textbf{Remark:} If $f_1, f_2 \in C_n (\mathbb{R})$, then $\alpha f_1 + \beta f_2 \in C_n (\mathbb{R})$", p1, align = (1,0));
p1 -= 2*vs;
add(tmp);

// SEVENTH SLIDE

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
p2 = (0,-.45);
dot(tmp, "$0$", p2, align = W);
smooth u0 =
    smooth(convexpaths[0], scale = .2, shift = p2 + (.0,.1))
    .setlabel("$U - x$", dir(80));
smooth v0 =
    smooth(convexpaths[5], scale = .2, shift = p2 + (.05, -.07))
    // .rotate(90)
    .setlabel("$V - y$", dir(220));
config.drawing.drawnow = false;
config.drawing.gaplength = 0.03;
draw(tmp, u0);
draw(tmp, v0, dpar(smoothoverlap = false));
pair x = (-.6,-.5), y = (.6,-.4);
smooth ux = u0.copy().shift(x - p2).setlabel("$U$", dir(120));
dot(tmp, "$x$", x, align = W);
draw(tmp, ux);
smooth vy = v0.copy().shift(y - p2).setlabel("$V$", dir(60));
dot(tmp, "$y$", y, align = W);
draw(tmp, vy);
drawarrow(tmp, ux, u0, curve = -.4, L = Label("$-x$", position = MidPoint, align = Relative(W)));
drawarrow(tmp, vy, v0, curve = -.4, L = Label("$-y$", position = MidPoint, align = Relative(W)));
add(tmp);

// EIGHTH SLIDE

title("Properties of Topological Vector Spaces");
erase(tmp);
label(tmp, "Metrizability", top + 2/3 * lft);
label(tmp, "Local convexity", top);
label(tmp, "", top);
pair x1 = (-.34, .3);
real r1 = .15;
pair x2 = (-.11,.34);
real r2 = .09;
smooth metr =
    smooth(concavepaths[5], scale = .25, shift = (-.3, .3))
    .addsubset(circ(x1, r1))
    .addsubset(circ(x2, r2))
    .addelement(x1)
    .addelement(x2)
    .move(shift = (-.35,-.18))
    ;
draw(tmp, metr);
draw(tmp, shift(metr.elements[0].pos) * xscale(ratio) * ((0,0) -- r1 * dir(40)), arrow = Arrows(TeXHead));
draw(tmp, shift(metr.elements[1].pos) * xscale(ratio) * ((0,0) -- r2 * dir(110)), arrow = Arrows(TeXHead));

smooth conc =
    smooth(concavepaths[6]);
add(tmp);

// drawgrid();
