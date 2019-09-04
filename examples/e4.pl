power(_, 0, 1).
power(B, E, R) :- E1 is (E - 1), power(B, E1, R1), R is (B * R1), !.

simplified(negative(E), value(N)) :- simplified(E, value(N1)), !, N is (-N1).
simplified(negative(E1), E2) :- simplified(E1, negative(E2)), !.
simplified(negative(E1), negative(E2)) :- !, simplified(E1, E2).

simplified(add(E1, E2), value(N)) :- simplified(E1, value(N1)), simplified(E2, value(N2)), !, N is (N1 + N2).
simplified(add(E1, E2), E3) :- simplified(E1, value(0)), simplified(E2, E3), !.
simplified(add(E1, E2), E3) :- simplified(E2, value(0)), simplified(E1, E3), !.
simplified(add(E1, E2), subtract(E3, E4)) :- simplified(E1, E3), simplified(E2, negative(E4)), !.
simplified(add(E1, E2), add(E3, E4)) :- !, simplified(E1, E3), simplified(E2, E4).

simplified(subtract(E1, E2), value(N)) :- simplified(E1, value(N1)), simplified(E2, value(N2)), !, N is (N1 - N2).
simplified(subtract(E1, E2), add(E3, E4)) :- simplified(E1, E3), simplified(E2, negative(E4)), !.
simplified(subtract(E1, E2), subtract(E3, E4)) :- !, simplified(E1, E3), simplified(E2, E4).

simplified(multiply(E1, E2), value(N)) :- simplified(E1, value(N1)), simplified(E2, value(N2)), !, N is (N1 * N2).
simplified(multiply(E, _), value(0)) :- simplified(E, value(0)), !.
simplified(multiply(_, E), value(0)) :- simplified(E, value(0)), !.
simplified(multiply(E1, E2), E3) :- simplified(E1, value(1)), simplified(E2, E3), !.
simplified(multiply(E1, E2), E3) :- simplified(E2, value(1)), simplified(E1, E3), !.
simplified(multiply(E1, E2), negative(E3)) :- simplified(E1, value(-1)), simplified(E2, E3), !.
simplified(multiply(E1, E2), negative(E3)) :- simplified(E2, value(-1)), simplified(E1, E3), !.
simplified(multiply(E1, E2), multiply(E3, E4)) :- simplified(E1, negative(E3)), simplified(E2, negative(E4)), !.
simplified(multiply(E1, E2), negative(multiply(E3, E4))) :- simplified(E1, negative(E3)), simplified(E2, E4), !.
simplified(multiply(E1, E2), negative(multiply(E3, E4))) :- simplified(E1, E3), simplified(E2, negative(E4)), !.
simplified(multiply(E1, E2), multiply(E3, E4)) :- !, simplified(E1, E3), simplified(E2, E4).

simplified(divide(E1, E2), value(N)) :- simplified(E1, value(N1)), simplified(E2, value(N2)), 0 is (mod(N1, N2)), !, N is (N1 / N2).
simplified(divide(E1, E2), E3) :- simplified(E1, E3), simplified(E2, value(1)), !.
simplified(divide(E1, E2), negative(E3)) :- simplified(E1, E3), simplified(E2, value(-1)), !.
simplified(divide(E, _), value(0)) :- simplified(E, value(0)), !.
simplified(divide(E1, E2), divide(E3, E4)) :- simplified(E1, negative(E3)), simplified(E2, negative(E4)), !.
simplified(divide(E1, E2), negative(divide(E3, E4))) :- simplified(E1, negative(E3)), simplified(E2, E4), !.
simplified(divide(E1, E2), negative(divide(E3, E4))) :- simplified(E1, E3), simplified(E2, negative(E4)), !.
simplified(divide(E1, E2), divide(E3, value(0))) :- simplified(E1, E3), simplified(E2, value(0)), !. % Don't simplify division by 0
simplified(divide(E1, E2), divide(E3, E4)) :- !, simplified(E1, E3), simplified(E2, E4).

simplified(exponent(E1, E2), value(N)) :- simplified(E1, value(N1)), simplified(E2, value(N2)), !, power(N1, N2, N).
simplified(exponent(_, E), value(1)) :- simplified(E, value(0)), !.
simplified(exponent(E1, E2), exponent(E3, value(N))) :- simplified(E1, negative(E3)), simplified(E2, value(N)), 0 is (mod(N, 2)), !.  % Exponent is even
simplified(exponent(E1, E2), negative(exponent(E3, value(N)))) :- simplified(E1, negative(E3)), simplified(E2, value(N)), 1 is (mod(N, 2)), !. % Exponent is odd
simplified(exponent(E1, E2), E3) :- simplified(E1, E3), simplified(E2, value(1)), !.
simplified(exponent(E1, E2), E3) :- simplified(E1, B), simplified(E2, logrithm(B, E3)), !.
simplified(exponent(E1, E2), exponent(E3, E4)) :- !, simplified(E1, E3), simplified(E2, E4).

simplified(logrithm(E1, E2), value(1)) :- simplified(E1, B), simplified(E2, B), !.
simplified(logrithm(E1, E2), E3) :- simplified(E1, B), simplified(E2, exponent(B, E3)), !.
simplified(logrithm(E1, E2), logrithm(E3, E4)) :- !, simplified(E1, E3), simplified(E2, E4).

simplified(E, E).

constant(value(_), _).
constant(e(), _).
constant(variable(V1), V2) :- dif(V1, V2).
constant(negative(E), V) :- constant(E, V).
constant(add(E1, E2), V) :- constant(E1, V), constant(E2, V).
constant(subtract(E1, E2), V) :- constant(E1, V), constant(E2, V).
constant(multiply(E1, E2), V) :- constant(E1, V), constant(E2, V).
constant(divide(E1, E2), V) :- constant(E1, V), constant(E2, V).
constant(exponent(E1, E2), V) :- constant(E1, V), constant(E2, V).
constant(logrithm(E1, E2), V) :- constant(E1, V), constant(E2, V).

d(value(_), _, value(0)) :- !.
d(variable(X), X, value(1)) :- !.
d(variable(_), _, value(0)) :- !. % Partial derivative
d(negative(U), X, negative(DU)) :- d(U, X, DU).
d(add(U, V), X, add(DU, DV)) :- !, d(U, X, DU), d(V, X, DV).
d(subtract(U, V), X, subtract(DU, DV)) :- !, d(U, X, DU), d(V, X, DV).
d(multiply(U, V), X, add(multiply(U, DV), multiply(V, DU))) :- !, d(U, X, DU), d(V, X, DV).
d(divide(U, V), X, divide(subtract(multiply(V, DU), multiply(U, DV)), exponent(V, value(2)))) :- !, d(U, X, DU), d(V, X, DV).
d(exponent(U, V), X, multiply(V, multiply(DU, exponent(U, subtract(V, value(1)))))) :- constant(V, X), !, d(U, X, DU).
d(exponent(U, V), X, multiply(DV, multiply(logrithm(e(), U), exponent(U, V)))) :- constant(U, X), !, d(V, X, DV).
d(logrithm(U, V), X, divide(DV, multiply(logrithm(e(), U), V))) :- constant(U, X), !, d(V, X, DV).
