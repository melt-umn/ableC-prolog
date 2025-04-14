#include <unification.xh>
#include <list.xh>
#include <string.xh>
#include <stdbool.h>

int main() {
  allocate_using heap;
  list<const char *?> l = term<list<const char *?>> { ["ac", "ab", "ccc", "z", "x", "y"] };
  return query sort<const char *, strcmp>((l), L2) {
    allocate_using stack;
    printf("%s\n", show(L2).text);
    return false;
  };
}
