emptyMap(Empty()).

mapContains(Node(K1, V, L, R), K2, V) :- (cmp(K1, K2)) =:= 0, !.
mapContains(Node(K1, _, L, R), K2, V) :- (cmp(K1, K2)) > 0, !, mapContains(R, K2, V).
mapContains(Node(K1, _, L, R), K2, V) :- (cmp(K1, K2)) < 0, !, mapContains(L, K2, V).

mapInsert(Empty(), K, V, Node(K, V, Empty(), Empty())) :- !.
mapInsert(Node(K1, V1, L, R), K2, V2, Node(K, V2, L, R)) :- (cmp(K1, K2)) =:= 0, !.
mapInsert(Node(K1, V1, L, R), K2, V2, Node(K1, V1, M, R)) :- (cmp(K1, K2)) < 0, !, mapInsert(L, K2, V2, M).
mapInsert(Node(K1, V1, L, R), K2, V2, Node(K1, V1, L, M)) :- (cmp(K1, K2)) > 0, !, mapInsert(R, K2, V2, M).

mapMerge(Empty(), M, M).
mapMerge(M, Empty(), M).
mapMerge(Node(K1, V, L1, R1), Node(K2, _, L2, R2), Node(K1, V, M1, M2)) :- (cmp(K1, K2)) =:= 0, !, mapMerge(L1, L2, M1), mapMerge(R1, R2, M2).
mapMerge(Node(K1, V, L, R), M1, Node(K1, V, L, M2)) :- M1 = Node(K2, _, _, _), (cmp(K1, K2)) < 0, !, mapMerge(M1, R, M2).
mapMerge(Node(K1, V, L, R), M1, Node(K1, V, M2, R)) :- M1 = Node(K2, _, _, _), (cmp(K1, K2)) > 0, !, mapMerge(M1, L, M2).

mapDelete(Node(K1, _, L, R), K2, M) :- (cmp(K1, K2)) =:= 0, !, mapMerge(L, R, M).
mapDelete(Node(K1, V, L, R), K2, Node(K1, V, M, R)) :- (cmp(K1, K2)) < 0, !, mapDelete(L, K2, M).
mapDelete(Node(K1, V, L, R), K2, Node(K1, V, L, M)) :- (cmp(K1, K2)) > 0, !, mapDelete(R, K2, M).

mapKeys(Node(K, V, L, R), [K | KS], V) :- !, mapKeys(L, LKS, V), mapKeys(R, RKS, V), append(LKS, RKS, KS).
mapKeys(Node(_, _, L, R), KS, V) :- mapKeys(L, LKS, V), mapKeys(R, RKS, V), append(LKS, RKS, KS).
mapKeys(Empty(), [], _).
