#include <unification.xh>

enum Foo { a, b };
typedef enum Foo Foo;

prolog {
  f(Foo ?, Foo?, Foo?);
  f(b, b, b) :- f(a, a, a).
  f(a, a, b).
  f(b, a, a).
  f(a, a, a).
}

int main() {
  if (!query f(a, a, a) {}) {
    return 1;
  }
  if (!query f(b, b, b) {}) {
    return 2;
  }
  if (!query f(b, a, a) {}) {
    return 3;
  }
  if (query f(b, a, b) {}) {
    return 4;
  }
  if (!query f(b, X, X) {}) {
    return 5;
  }
  if (!query f(X, Y, Y), X =\= Y {}) {
    return 6;
  }
}
