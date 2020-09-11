#include <unification.xh>

prolog {
  foo(int? x, int? y);
  foo(A, A).
}

int main() {
  int i = 42;
  query I is i, foo(I, i) {};
}
