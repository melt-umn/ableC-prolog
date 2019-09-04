#include <unification.xh>
#include <stdbool.h>

prolog {
  a(int ?);
  a(_).
}

int main() {
  query a(A), B is (A + 1) {}; // B is free in "is" goal
}
