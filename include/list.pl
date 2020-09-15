append([], A, A).
append([H | A], B, [H | C]) :- append(A, B, C).

reverse([], []).
reverse([H | A], B) :- reverse(A, C), append(C, [H], B).

length([], 0).
length([_ | T], N1) :- length(T, N2), N1 is (N2 + 1u).

member(A, [A | _]).
member(A, [_ | T]) :- member(A, T).

select(H, [H | T], T).
select(A, [H | T1], [H | T2]) :- select(A, T1, T2).

subset([], []).
subset([H | T1], [H | T2]) :- subset(T1, T2).
subset(T1, [_ | T2]) :- subset(T1, T2).

nth([X | _], 0, X).
nth([_ | T], N, X) :- nth(T, N1, X), N1 is (N - 1u).

sort([X | L1], L3) :- sort<a, cmp>(L1, L2), insert<a, cmp>(X, L2, L3).
sort([], []).

insert(X, [H | T], [X, H | T]) :- (cmp(X, H)) =< 0 .
insert(X, [H | T1], [H | T2]) :- (cmp(X, H)) > 0, insert<a, cmp>(X, T1, T2).
insert(X, [], [X]).
