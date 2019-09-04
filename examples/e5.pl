lookup(N, V1, A) :- member(pair(N, V2), A), !, V1 = V2.

evaluate(t(), true, _).
evaluate(f(), false, _).
evaluate(varE(N), V, A) :- lookup(N, V, A).
evaluate(andE(E1, E2), true, A) :- evaluate(E1, true, A), evaluate(E2, true, A).
evaluate(andE(E, _), false, A) :- evaluate(E, false, A).
evaluate(andE(_, E), false, A) :- evaluate(E, false, A).
evaluate(orE(E, _), true, A) :- evaluate(E, true, A).
evaluate(orE(_, E), true, A) :- evaluate(E, true, A).
evaluate(orE(E1, E2), false, _) :- evaluate(E1, false, A), evaluate(E2, false, A).
evaluate(notE(E), true, A) :- evaluate(E, false, A).
evaluate(notE(E), false, A) :- evaluate(E, true, A).

sat(E) :- evaluate(E, true, _), !.
