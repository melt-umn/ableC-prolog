#include <unification.xh>
#include <stdbool.h>

prolog {
  a(int ?);
  b(int ?);
  
  a(X) :- \+ b(X).
  
  b(3).
}

int main() {
  return query 3 = X, a(X) {
    printf("%d\n", inst value<int>(X));
    return false;
  };
}

