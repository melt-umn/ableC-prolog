#include <unification.xh>
#include <stdbool.h>

datatype IntList {
  cons(int ?head, datatype IntList ?tail);
  nil();
};

prolog {
  appendIntList(datatype IntList ?, datatype IntList ?, datatype IntList ?);
  appendIntList(nil(), A, A).
  appendIntList(cons(N, A), B, cons(N, C)) :- appendIntList(A, B, C).
}

int main() {
  unsigned count = 0, *p_count = &count;
  query appendIntList(X, cons(Y, Z), cons(1, cons(2, cons(3, nil())))) {
    printf("X: %s\n", show(X).text);
    printf("Y: %s\n", show(Y).text);
    printf("Z: %s\n", show(Z).text);
    printf("\n");
    (*p_count)++;
    return false;
  };
  return count != 3;
}
