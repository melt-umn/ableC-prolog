#include <unification.xh>
#include <list.xh>
#include <stdbool.h>

int main() {
  list<int> ?l1 = newlist<int>(malloc)[1, 2, 3];
  list<int> ?l2 = newlist<int>(malloc)[4, 5, 6];
  list<int> ?l3 = inst append_list<int>(malloc, l1, l2);
  list<int> ?l4 = term<list<int>>(alloca){ [1, 2, 3 | [4 | A]] };
  
  printf("%s\n", show(inst head<int>(l3)).text);
  printf("%s\n", show(inst tail<int>(l3)).text);
  printf("%s\n", show(l4).text);

  bool res = unify(l3, l4);
  printf("%d\n", res);
  
  inst delete_list<int>(free, l1);
  inst delete_list<int>(free, l3);
  printf("\n");
  
  query append<int>(X, [Y | Z], [1, 2, 3]) {
    printf("X: %s\n", show(X).text);
    printf("Y: %s\n", show(Y).text);
    printf("Z: %s\n", show(Z).text);
    printf("\n");
    return false;
  };
  printf("\n");
  
  query length<int>([1, 2, 3, 4], N) {
    printf("N: %s\n", show(N).text);
    printf("\n");
    return false;
  };
}
