#include <unification.xh>

prolog {
  foo(const int x); // x is const
  foo(0).
  foo(N) :- N1 is (N - 1), foo(N1).
}

int main() {
  query foo(42) {};
}
