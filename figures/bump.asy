import graph;
settings.outformat = "pdf";
size(15cm, 3cm, keepAspect = false);
defaultpen(fontsize(11pt));

real f (real x) {
    if (abs(x) < 1) {
        return exp(1/(abs(x)^2 - 1));
    } else {
        return 0;
    }
}

draw((-5,0) -- (5,0), arrow = Arrow(SimpleHead));
draw((0,-.2) -- (0,.7), arrow = Arrow(SimpleHead));

draw(graph(f, -4, 4, n = 100), red);

dot((0,0), L = Label("$0$", align = (-1,-1)));
dot((0,f(0)), L = Label("$e^{-1}$", align = (1,1)));
dot((1,0), L = Label("$1$", align = (0,-1)));
dot((-1,0), L = Label("$-1$", align = (0,-1)));
