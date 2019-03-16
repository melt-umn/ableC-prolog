#include <unification.xh>

// Performance test
prolog {
  foo(int?);
}

int main() {
  query foo(1), foo(1), foo(1), foo(1), foo(1), foo(1), foo(1), foo(1), foo(1), foo(1), foo(1), foo(1) {};
}
