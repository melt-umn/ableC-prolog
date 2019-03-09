#include <unification.xh>
#include <stdbool.h>

template<typename a>
datatype Tree {
  node(Tree<a> ?left, Tree<a> ?right);
  leaf(a ?val);
  foo(int);
};

prolog {
  subtree<typename a>(Tree<a> ?, Tree<a> ?);
  subtree(T, T).
  subtree(node(T1, _), T2) :- subtree<a, a>(T1, T2). // Wrong number of type arguments to subtree
  subtree(node(_, T1), T2) :- subtree<a>(T1, T2, 0). // Wrong number of arguments to subtree
  
  commonSubtree<typename a>(Tree<a> ?, Tree<a> ?, Tree<a> ?);
  commonSubtree(T1, T2, T3) :- subtree(T1, T3), subtree(T2, T3).
  
  isleaf<typename a>(Tree<a> ?tree, a ?val);
}

prolog {
  isleaf(T, V) :- subtree(T, leaf(V)). // Rule seperated from predicate declaration
}

int main() {
  Tree<float> ?t1 =
    term<Tree<float> ?>(foobar) { // Undefined allocator
      baz(leaf(3.3), node(leaf(1.1), leaf(2.2))) // Undefined constructor
    };
  Tree<float> ?t2 =
    term<Tree<float> ?>(printf) { // Wrong allocator type
      node(node(leaf(1), foo(A)), leaf("hello")) // Wrong types to constructors
    };
  
  bool res =
    query T1 is t1, commonSubtree(T1, T2, S), isleaf<long>(S, L) { // Wrong type to isleaf
      printf("%g\n", value<float>(L)); // Wrong type to value
      return 3.14; // Wrong return type
    };
}
