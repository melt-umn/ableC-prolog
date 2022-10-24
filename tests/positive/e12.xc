#include <unification.xh>

prolog {
  foo(int x);
  foo(X) :- X > 7, !, foo(2).
  foo(2).
  foo(4).
}

int main() {
  if (!query foo(100) {}) {
    return 1;
  }
}
