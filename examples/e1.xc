#include <unification.xh>
#include <stdbool.h>

datatype IntList {
  cons(int ?head, datatype IntList ?tail);
  nil();
};

prolog {
  append(datatype IntList ?, datatype IntList ?, datatype IntList ?);
  append(nil(), A, A).
  append(cons(N, A), B, cons(N, C)) :- append(A, B, C).
}

int main() {
  query append(X, cons(Y, Z), cons(1, cons(2, cons(3, nil())))) {
    printf("X: %s\n", show(X).text);
    printf("Y: %s\n", show(Y).text);
    printf("Z: %s\n", show(Z).text);
    printf("\n");
    return false;
  };
}
