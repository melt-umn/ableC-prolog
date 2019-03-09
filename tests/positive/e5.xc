#include <unification.xh>
#include <list.xh>
#include <stdbool.h>

prolog {
  less<typename a, int (*cmp)(a, a)>(a ?x, a ?y);
  less(X, Y) :- (cmp(X, Y)) < 0 .
}

int main() {
  list<const char *?> l = term<list<const char *?>>(malloc){ ["aaa", "bbb", "ccc"] };
  return query L is l, member(A, L), member(B, L), less<const char *, strcmp>(A, B) {
    printf("%s < %s\n", value(A), value(B));
    return false;
  };
}

