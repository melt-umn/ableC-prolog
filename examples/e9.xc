#include <unification.xh>
#include <stdbool.h>

prolog {
  a(int ?);

  a(0) :- initially { printf("Before base\n"); }, finally { printf("After base\n"); }.
  a(5) :- initially { printf("Before cut\n"); }, finally { printf("After cut\n"); },
                                                                                                      !, a(3).
  a(N) :- initially { printf("Before - %d\n", N); }, finally { printf("After - %d\n", N); },
      N > 0, N1 is (N - 1), a(N1).
  a(N) :- initially { printf("Before / %d\n", N); }, finally { printf("After / %d\n", N); },
      N > 0, N1 is (N / 2), a(N1).
}

int main() {
  query a(7) {
    printf("Done\n");
    return false;
  };
  printf("\n\n");
  query a(5) {
    printf("Done\n");
    return false;
  };
  printf("\n\n");
  query a(-1) {
    printf("Done\n");
    return false;
  };
}
