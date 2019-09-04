#include <unification.xh>

prolog {
  foo<typename a>(a? x, a? y, int z);
  foo(A, A, 1).
}

int main() {
  query foo(N, N, 1), N is 2 {};
}
