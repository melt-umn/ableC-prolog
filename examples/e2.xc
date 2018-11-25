#include <unification.xh>
#include <stdbool.h>

template<a>
datatype Tree {
  node(inst Tree<a> ?left, inst Tree<a> ?right);
  leaf(a ?val);
};

prolog {
  subtree<a>(inst Tree<a> ?tree1, inst Tree<a> ?tree2);
  subtree(T, T).
  subtree(node(T1, _), T2) :- subtree<a>(T1, T2).
  subtree(node(_, T1), T2) :- subtree<a>(T1, T2).
  
  isleaf<a>(inst Tree<a> ?tree, a ?val);
  isleaf(T, V) :- subtree<a>(T, leaf(V)).

  numleaves<a>(inst Tree<a> ?tree, a ?val, unsigned ?count);
  numleaves(node(T1, T2), V, C) :- numleaves<a>(T1, V, C1), numleaves<a>(T2, V, C2), C is (C1 + C2).
  numleaves(leaf(V), V, 1u).
  numleaves(leaf(_), _, 0u).
}

template<a>
unsigned count_leaves(inst Tree<a> ?tree, a val) {
  unsigned count = 0, *count_p = &count;
  query T is tree, V is val, isleaf<a>(T, V) {
    (*count_p)++;
    return false;
  };
  return count;
}

int main() {
  inst Tree<int> ?tree = term<inst Tree<int>>(GC_malloc) {
    node(node(node(leaf(1), leaf(2)), leaf(2)), node(leaf(3), leaf(2)))
  };
  printf("tree: %s\n", show(tree).text);
  
  query T is tree, subtree<int>(T, A) {
    printf("subtree(tree, A): %s\n", show(A).text);
    return false;
  };
  
  query T is tree, subtree<int>(T, node(A, leaf(2))) {
    printf("subtree(tree, node(A, leaf(2))): %s\n", show(A).text);
    return true; // Stop after the first one
  };

  unsigned count = inst count_leaves<int>(tree, 2);
  printf("count_leaves(tree, 2): %u\n", count);
  
  query T is tree, numleaves<int>(T, 2, C) {
    printf("numleaves(tree, 2, C): %d\n", inst value<unsigned>(C));
    return false; // Should only be 1 result
  };
  
  printf("tree: %s\n", show(tree).text);
}
