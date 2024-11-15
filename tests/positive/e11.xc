#include <unification.xh>
#include <list.xh>
#include <string.xh>
#include <stdbool.h>

int main() {
  allocate_using heap;
  list<const char *?> l = term<list<const char *?>> { ["ac", "ab", "ccc", "z", "x", "y"] };
  return query L1 is l, sort<const char *, strcmp>(L1, L2) {
    allocate_using stack;
    printf("%s\n", show(L2).text);
    return false;
  };
}
