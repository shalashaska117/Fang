% generative case 146
include('ax.ax').
cnf(h2,axiom,f(g("o2","o1")) != f(g(a,"o2")) | ~r(b)).
cnf(h1,axiom,X = f(b) | b != g(X,a)).
