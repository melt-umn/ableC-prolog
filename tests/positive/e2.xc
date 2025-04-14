#include <unification.xh>
#include <string.xh>
#include <stdbool.h>

template<typename a>
datatype Tree {
  node(Tree<a> ?left, Tree<a> ?right);
  leaf(a ?val);
};

prolog {
  subtree<typename a>(Tree<a> ?tree1, Tree<a> ?tree2);
  subtree(T, T).
  subtree(node(T1, _), T2) :- subtree(T1, T2).
  subtree(node(_, T1), T2) :- subtree(T1, T2).
  
  isleaf<typename a>(Tree<a> ?tree, a ?val);
  isleaf(T, V) :- subtree(T, leaf(V)).

  numleaves<typename a>(Tree<a> ?tree, a ?val, unsigned ?count);
  numleaves(node(T1, T2), V, C) :- numleaves(T1, V, C1), numleaves(T2, V, C2), C is (C1 + C2).
  numleaves(leaf(V), V, 1u) :- !.
  numleaves(leaf(_), _, 0u).
}

template<typename a>
unsigned count_leaves(Tree<a> ?tree, a val) {
  unsigned count = 0, *count_p = &count;
  query isleaf((tree), (val)) {
    (*count_p)++;
    return false;
  };
  return count;
}

int main() {
  allocate_using stack;
  Tree<int> ?tree = term<Tree<int> ?> {
    node(node(node(leaf(1), leaf(2)), leaf(2)), node(leaf(3), leaf(2)))
  };
  printf("tree: %s\n", show(tree).text);
  if (show(tree) != "node(node(node(leaf(1), leaf(2)), leaf(2)), node(leaf(3), leaf(2)))")
    return 1;
  
  unsigned count = 0, *p_count = &count;
  query subtree((tree), A) {
    allocate_using stack;
    printf("subtree(tree, A): %s\n", show(A).text);
    (*p_count)++;
    return false;
  };
  if (count != 9) return 2;
  
  bool result = query subtree((tree), node(A, leaf(2))) {
    allocate_using stack;
    printf("subtree(tree, node(A, leaf(2))): %s\n", show(A).text);
    return true; // Stop after the first one
  };
  if (!result) return 3;

  count = count_leaves(tree, 2);
  printf("count_leaves(tree, 2): %u\n", count);
  if (count != 3) return 4;

  count = 0;
  query numleaves((tree), 2, C) {
    allocate_using stack;
    printf("numleaves(tree, 2, C): %d\n", value(C));
    (*p_count)++;
    return false; // Should only be 1 result
  };
  if (count != 1) return 5;
  
  printf("tree: %s\n", show(tree).text);
}
