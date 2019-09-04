nqueens(N, Qs) :- nqueens_partial(N, N, Qs).

nqueens_partial(H, W, [Q | Qs]) :-
    H > 0,
    W1 is (W - 1), between(0, W1, Q),
    H1 is (H - 1), nqueens_partial(H1, W, Qs),
    safe(0, Q, Qs).
nqueens_partial(0, _, []).

safe(R, C, [Q | Qs]) :-
    C =\= Q,
    R1 is (R + 1), D is (abs(C - Q)), R1 \= D,
    safe(R1, C, Qs).
safe(_, _, []).
