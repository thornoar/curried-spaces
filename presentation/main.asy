import smoothmanifold;

orientation = Landscape;
defaultpen(1pt);
import slide;

pair top = (0,0.65);
pair bot = (0,-0.9);
pair lft = (-0.9, 0);
pair rgt = (0.9, 0);

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

title("Premise", position = (0,1));

picture pr;
draw(pr, top -- bot);
label(pr, Label("Multivariable functions", position = top + lft / 2));
label(pr, Label("$\mathbb{R}^n \to \mathbb{R}$", position = top + lft / 2 - 2.5 * vs));
label(pr, Label("Curried functions", position = top + rgt / 2));
label(pr, Label("$\mathbb{R} \to (\mathbb{R} \to (\dots (\mathbb{R} \to \mathbb{R})))$", position = top + rgt / 2 - 2.5 * vs));


add(pr);
