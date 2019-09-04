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
  if (!res) return 1;
  
  delete_list(free, l1);
  delete_list(free, l3);
  printf("\n");
  
  unsigned count = 0, *p_count = &count;
  query append(X, [Y | Z], [1, 2, 3]) {
    printf("X: %s\n", show(X).text);
    printf("Y: %s\n", show(Y).text);
    printf("Z: %s\n", show(Z).text);
    printf("\n");
    (*p_count)++;
    return false;
  };
  printf("\n");
  if (count != 3) return 2;

  count = 0;
  int result = 0, *p_result = &result;
  query length([1, 2, 3, 4], N) {
    printf("N: %s\n", show(N).text);
    printf("\n");
    match (N) {
      freevar -> { *p_result = -1; }
      ?&n -> { *p_result = n; }
    }
    (*p_count)++;
    return false;
  };
  if (count != 1) return 3;
  if (result != 4) return 4;

  count = 0;
  query between(1, 10, N) {
    printf("%s\n", show(N).text);
    (*p_count)++;
    return false;
  };
  if (count != 10) return 5;

  count = 0;
  query subset(L, [1, 2, 3, 4]) {
    printf("%s\n", show(L).text);
    (*p_count)++;
    return false;
  };
  if (count != 16) return 6;

  return 0;
}
