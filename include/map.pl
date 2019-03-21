emptyMap(Empty()).

mapContains(Node(K1, V, L, R), K2, V) :- (cmp(K1, K2)) =:= 0, !.
mapContains(Node(K1, _, L, R), K2, V) :- (cmp(K1, K2)) > 0, !, mapContains(L, K2, V).
mapContains(Node(K1, _, L, R), K2, V) :- (cmp(K1, K2)) < 0, !, mapContains(R, K2, V).

mapInsert(Empty(), K, V, Node(K, V, Empty(), Empty())) :- !.
mapInsert(Node(K1, V1, L, R), K2, V2, Node(K1, V2, L, R)) :- (cmp(K1, K2)) =:= 0, !.
mapInsert(Node(K1, V1, L, R), K2, V2, Node(K1, V1, M, R)) :- (cmp(K1, K2)) > 0, !, mapInsert(L, K2, V2, M).
mapInsert(Node(K1, V1, L, R), K2, V2, Node(K1, V1, L, M)) :- (cmp(K1, K2)) < 0, !, mapInsert(R, K2, V2, M).

mapDelete(Node(K1, _, Empty(), R), K2, R) :- (cmp(K1, K2)) =:= 0, !.
mapDelete(Node(K1, _, L, R), K2, Node(MK, MV, ML, R)) :- (cmp(K1, K2)) =:= 0, mapSelectMax(L, MK, MV, ML), !.
mapDelete(Node(K1, V, L, R), K2, Node(K1, V, M, R)) :- (cmp(K1, K2)) > 0, !, mapDelete(L, K2, M).
mapDelete(Node(K1, V, L, R), K2, Node(K1, V, L, M)) :- (cmp(K1, K2)) < 0, !, mapDelete(R, K2, M).

mapSelectMin(Node(K, V, Empty(), R), K, V, R) :- !.
mapSelectMin(Node(K1, V1, L1, R), K2, V2, Node(K1, V1, L2, R)) :- mapSelectMin(L1, K2, V2, L2).

mapSelectMax(Node(K, V, L, Empty()), K, V, L) :- !.
mapSelectMax(Node(K1, V1, L, R1), K2, V2, Node(K1, V1, L, R2)) :- mapSelectMax(R1, K2, V2, R2).

mapKeys(Node(K, V, L, R), [K | KS], V) :- !, mapKeys(L, LKS, V), mapKeys(R, RKS, V), append(LKS, RKS, KS).
mapKeys(Node(_, _, L, R), KS, V) :- mapKeys(L, LKS, V), mapKeys(R, RKS, V), append(LKS, RKS, KS).
mapKeys(Empty(), [], _).
