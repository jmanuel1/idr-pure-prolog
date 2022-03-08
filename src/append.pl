my_append(nil, Ys, Ys).
my_append(cons(X, Xs), Ys, cons(X, Rec)) :- my_append(Xs, Ys, Rec).
