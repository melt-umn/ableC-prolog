#include <unification.xh>
#include <stdbool.h>

template<a>
datatype Tree {
  node(Tree<a> ?left, Tree<a> ?right);
  leaf(a ?val);
};

prolog {
  subtree<a>(Tree<a> ?, Tree<a> ?);
  subtree(T, T).
  subtree(node(T1, _), T2) :- subtree(T1, T2).
  subtree(node(_, T1), T2) :- subtree(T1, T2).
  
  commonSubtree<a>(Tree<a> ?, Tree<a> ?, Tree<a> ?);
  commonSubtree(T1, T2, T3) :- subtree(T1, T3), subtree(T2, T3).
  
  isleaf<a>(Tree<a> ?tree, a ?val);
  isleaf(T, V) :- subtree(T, leaf(V)).
}

int main() {
  Tree<float> ?t1 =
    term<Tree<float> ?>(alloca) {
      node(leaf(3.3), node(leaf(1.1), leaf(2.2)))
    };
  Tree<float> ?t2 =
    term<Tree<float> ?>(alloca) {
      // Term contains a free variable A
      node(node(leaf(1.1), leaf(A)), leaf(2.2))
    };
  
  bool res =
    query T1 is t1, T2 is t2, commonSubtree(T1, T2, S), isleaf(S, L) {
      printf("%g\n", value(L)); // Demand the value of L
      return false; // "Fail", keep asking for more values
    };
}
