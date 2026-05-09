import smoothmanifold;
config.drawing.fill = false;
config.drawing.drawnow = true;
config.drawing.drawnow = true;
config.arrow.mar = 0.03;
config.arrow.currentbar = DeferredBar(10, true, false);
// config.help.drawgrid = true;

orientation = Landscape;
defaultpen(1pt);
import slide;

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

// pagewidth = 16 * (pageheight / 9);
// size(pagewidth,pageheight,IgnoreAspect);

// pagewidth = settings.paperwidth;
// pageheight = settings.paperheight;
// size(pagewidth,pageheight,IgnoreAspect);

// usersetting();

usepackage("tgschola");
usepackage("amsmath");
usepackage("graphicx");

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
// draw(pr, (top + lft - 2.5 * vs) -- (top + rgt - 2.5 * vs));
// draw(pr, (top + lft) -- (top + rgt));
label(pr2, Label("$\mathbb{R} \to (\mathbb{R} \to (\dots (\mathbb{R} \to \mathbb{R})))$", position = top + rgt / 2 - 2.65 * vs));
// draw(pr, box(lft + bot + 6 * vs + 2 * hs, top - 2 * hs - 4.5 * vs));
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
draw((0,0){(-1,0)} .. (-.5,-.2) .. {(0,-1)}(bot + lft/2 + 5*vs), red, arrow = Arrow(SimpleHead));

// THIRD SLIDE

title("Continuous Functions");
pair st = top + lft - 2*vs + 2 * hs;
label("$C_n (\mathbb{R})$ --- the space of continuous curried functions", st, align = (1,0));
st -= 3*vs;
label("$\bullet$ $C_0 (\mathbb{R})$ --- the space of continuous curried functions", st, align = (1,0));
