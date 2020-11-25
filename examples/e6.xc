#include <unification.xh>
#include <list.xh>
#include <prolog_utils.xh>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

prolog {
  nqueens(int n, list<int?> ?board);
  nqueens_partial(int width, int height, list<int?> ?board);
  safe(int column, int row, list<int?> board);
# include "e6.pl"
}

bool solve(int n, bool board[n][n]) {
  memset(board, 0, sizeof(bool) * n * n);
  return query N is n, nqueens(N, B) {
    list<int?> ?l = B;
    for (int row = 0; row < n; row++) {
      match (l) {
        ?&[?&column | rest] -> {
          board[row][column] = true;
          l = rest;
        }
        _ -> {
          fprintf(stderr, "Unexpected tail of result list %s\n", show(l).text);
          exit(1);
        }
      }
    }
    return true;
  };
}

void print_board(int n, const bool board[n][n]) {
  printf("   ");
  for (int i = 0; i < n; i++) {
    printf(" %-2d", i);
  }
  printf("\n");
  for (int i = 0; i < n; i++) {
    printf("%2d", i);
    for (int j = 0; j < n; j++) {
      if (board[i][j]) {
        printf("  ♛");
      } else {
        printf("  .");
      }
    }
    printf("\n");
  }
}

int main(unsigned argc, char *argv[]) {
  int n = 8;
  if (argc >= 2) {
    n = atoi(argv[1]);
  }
  
  bool board[n][n];
  if (solve(n, board)) {
    print_board(n, board);
  } else {
    printf("No solution\n");
  }
}
