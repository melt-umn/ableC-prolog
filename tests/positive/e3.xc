#include <unification.xh>
#include <stdbool.h>

prolog {
  a(int ?, int ?);
  b(int ?);
  c(int ?);
  
  a(0, 0).
  a(X, Y) :- b(X), !, c(Y).
  a(4, 5).
    
  b(1).
  b(2).
  b(3).

  c(1).
  c(2).
  c(3).
}

int main() {
  int expected[][2] =
    {{0, 0},
     {1, 1},
     {1, 2},
     {1, 3}};
  int result[10][2];
  int i[1] = {0};
  query a(X, Y) {
    printf("%d %d\n", value<int>(X), value<int>(Y));
    result[*i][0] = value<int>(X);
    result[*i][1] = value<int>(Y);
    (*i)++;
    return false;
  };
  if (*i != 4) return -1;
  for (int i = 0; i < 4; i++) {
    if (result[i][0] != expected[i][0])
      return i * 2 + 1;
    if (result[i][1] != expected[i][1])
      return i * 2 + 2;
  }
  return 0;
}
