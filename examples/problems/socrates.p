% Every human is mortal and Socrates is human, so Socrates is mortal.
fof(humans_are_mortal,axiom,! [X] : (human(X) => mortal(X))).
fof(socrates_is_human,axiom,human(socrates)).
fof(socrates_is_mortal,conjecture,mortal(socrates)).
