#include <unification.xh>
#include <stdbool.h>

prolog {
  a(int ?, int ?);
  b(int ?);
  c(int ?);
  
  a(X, Y) :- b(X), !, c(Y).
    
  b(1).
  b(2).
  b(3).

  c(1).
  c(2).
  c(3).
}

int main() {
  query a(X, Y) {
    printf("%d %d\n", inst value<int>(X), inst value<int>(Y));
    return false;
  };
}
