#include <unification.xh>
#include <list.xh>
#include <stdbool.h>

int main() {
  list<const char *?> l = term<list<const char *?>>(malloc){ ["ac", "ab", "ccc", "z", "x", "y"] };
  return query L1 is l, sort<const char *, strcmp>(L1, L2) {
    printf("%s\n", show(L2).text);
    return false;
  };
}
