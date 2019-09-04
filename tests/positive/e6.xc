#include <unification.xh>
#include <list.xh>
#include <map.xh>
#include <stdbool.h>

int main() {
  query
    emptyMap<const char *, int, strcmp>(A),
    mapInsert(A, "a", 1, B),
    mapInsert(B, "c", 3, C),
    mapInsert(C, "b", 2, D),
    mapInsert(D, "d", 4, E),
    mapDelete(E, "b", F),
    mapContains(F, "c", G)
      {
        printf("%s\n", show(A).text);
        printf("%s\n", show(B).text);
        printf("%s\n", show(C).text);
        printf("%s\n", show(D).text);
        printf("%s\n", show(E).text);
        printf("%s\n", show(F).text);
        printf("%s\n", show(G).text);
        return true;
      };
}

