#include <unification.xh>
#include <prolog_utils.xh>

prolog {
  foo(int ?);
  foo(X).

  bar(int ?);
  bar(42).
}

int main() {
  if (!query var<int>(X) {}) {
    return 1;
  }
  if (query X is 42, var(X) {}) {
    return 2;
  }
  if (query nonvar<int>(X) {}) {
    return 3;
  }
  if (!query X is 42, nonvar(X) {}) {
    return 4;
  }
  if (!query foo(X), var(X) {}) {
    return 5;
  }
  if (query bar(X), var(X) {}) {
    return 6;
  }
  if (query foo(X), nonvar(X) {}) {
    return 7;
  }
  if (!query bar(X), nonvar(X) {}) {
    return 8;
  }
}
