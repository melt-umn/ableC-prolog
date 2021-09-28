#include <unification.xh>

// Compiler performance test
prolog {
  foo(int?);
}

int main() {
  query foo(1), foo(1), foo(1), foo(1), foo(1), foo(1), foo(1), foo(1), foo(1), foo(1), foo(1), foo(1) {};
}
