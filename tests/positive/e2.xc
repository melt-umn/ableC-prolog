#include <unification.xh>
#include <stdbool.h>

template<a>
datatype Tree {
  node(Tree<a> ?left, Tree<a> ?right);
  leaf(a ?val);
};

prolog {
  subtree<a>(Tree<a> ?tree1, Tree<a> ?tree2);
  subtree(T, T).
  subtree(node(T1, _), T2) :- subtree(T1, T2).
  subtree(node(_, T1), T2) :- subtree(T1, T2).
  
  isleaf<a>(Tree<a> ?tree, a ?val);
  isleaf(T, V) :- subtree(T, leaf(V)).

  numleaves<a>(Tree<a> ?tree, a ?val, unsigned ?count);
  numleaves(node(T1, T2), V, C) :- numleaves(T1, V, C1), numleaves(T2, V, C2), C is (C1 + C2).
  numleaves(leaf(V), V, 1u) :- !.
  numleaves(leaf(_), _, 0u).
}

template<a>
unsigned count_leaves(Tree<a> ?tree, a val) {
  unsigned count = 0, *count_p = &count;
  query T is tree, V is val, isleaf(T, V) {
    (*count_p)++;
    return false;
  };
  return count;
}

int main() {
  Tree<int> ?tree = term<Tree<int> ?>(GC_malloc) {
    node(node(node(leaf(1), leaf(2)), leaf(2)), node(leaf(3), leaf(2)))
  };
  printf("tree: %s\n", show(tree).text);
  if (show(tree) != "node(node(node(leaf(1), leaf(2)), leaf(2)), node(leaf(3), leaf(2)))")
    return 1;
  
  unsigned count = 0, *p_count = &count;
  query T is tree, subtree(T, A) {
    printf("subtree(tree, A): %s\n", show(A).text);
    (*p_count)++;
    return false;
  };
  if (count != 9) return 2;
  
  bool result = query T is tree, subtree(T, node(A, leaf(2))) {
    printf("subtree(tree, node(A, leaf(2))): %s\n", show(A).text);
    return true; // Stop after the first one
  };
  if (!result) return 3;

  count = count_leaves(tree, 2);
  printf("count_leaves(tree, 2): %u\n", count);
  if (count != 3) return 4;

  count = 0;
  query T is tree, numleaves(T, 2, C) {
    printf("numleaves(tree, 2, C): %d\n", value(C));
    (*p_count)++;
    return false; // Should only be 1 result
  };
  if (count != 1) return 5;
  
  printf("tree: %s\n", show(tree).text);
}
