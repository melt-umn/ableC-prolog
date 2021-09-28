#include <unification.xh>
#include <stdbool.h>

prolog {
  a(int);
  a(42).
}

int main() {
  query a(A) {}; // A is free where a value is demanded
}
