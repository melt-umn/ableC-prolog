#include <unification.xh>
#include <list.xh>
#include <prolog_utils.xh>
#include <stdbool.h>

int main() {
  list<int> ?l1 = newlist(malloc)[1, 2, 3];
  list<int> ?l2 = newlist(malloc)[4, 5, 6];
  list<int> ?l3 = append_list(malloc, l1, l2);
  list<int> ?l4 = term<list<int> ?>(alloca){ [1, 2, 3 | [4 | A]] };
  
  printf("%s\n", show(head(l3)).text);
  printf("%s\n", show(tail(l3)).text);
  printf("%s\n", show(l4).text);
  
  bool res = unify(l3, l4);
  printf("%d\n", res);
  
  delete_list(free, l1);
  delete_list(free, l3);
  printf("\n");
  
  query append(X, [Y | Z], [1, 2, 3]) {
    printf("X: %s\n", show(X).text);
    printf("Y: %s\n", show(Y).text);
    printf("Z: %s\n", show(Z).text);
    printf("\n");
    return false;
  };
  printf("\n");
  
  query length([1, 2, 3, 4], N) {
    printf("N: %s\n", show(N).text);
    printf("\n");
    return false;
  };
  
  query reverse([1, 2, 3, 4], L) {
    printf("L: %s\n", show(L).text);
    printf("\n");
    return false;
  };

  query between(1, 10, N) {
    printf("%s\n", show(N).text);
    return false;
  };
}
