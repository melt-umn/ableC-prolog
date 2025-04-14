#include <unification.xh>
#include <list.xh>
#include <string.xh>
#include <stdbool.h>

template<typename a, typename b>
datatype Pair {
  pair(a fst, b snd);
};

typedef list<Pair<string ?, bool ?> ?> ?Env;

typedef datatype Expr Expr;

datatype Expr {
  t();
  f();
  varE(string ?id);
  andE(Expr ?e1, Expr ?e2);
  orE(Expr ?e1, Expr ?e2);
  notE(Expr ?e);
};

size_t showExprMaxLen(Expr e);
size_t showExprToBuf(char *buf, Expr e);

show Expr with showExprMaxLen, showExprToBuf;

size_t showExprMaxLen(Expr e) {
  return match (e)
    (t() -> 4;
     f() -> 5;
     varE(?&id) -> id.length;
     andE(e1, e2) -> 7 + showMaxLen(e1) + showMaxLen(e2);
     orE(e1, e2) -> 7 + showMaxLen(e1) + showMaxLen(e2);
     notE(e) -> 3 + showMaxLen(e););
}

size_t wrapParens(char *buf, Expr ?e) {
  return match (e)
    (?&t() -> sprintf(buf, "true");
     ?&f() -> sprintf(buf, "false");
     ?&varE(?&id) -> buildStr(buf, id);
     _ -> buildStr(buf, "(" + show(e) + ")"););
}

size_t showExprToBuf(char *buf, Expr e) {
  return match (e)
    (t() -> sprintf(buf, "true");
     f() -> sprintf(buf, "false");
     varE(?&id) -> buildStr(buf, id);
     andE(e1, e2) -> buildStr(buf, showWith(wrapParens, e1) + " & " + showWith(wrapParens, e2));
     orE(e1, e2) -> buildStr(buf, showWith(wrapParens, e1) + " | " + showWith(wrapParens, e2));
     notE(e1) -> buildStr(buf, "!" + showWith(wrapParens, e1)););
}

prolog {
  lookup(string ?, bool ?, Env);
  evaluate(Expr ?, bool, Env);
  sat(Expr ?);

# include "e5.pl"
}

void test(Expr ?e) {
  allocate_using stack;
  printf("%s: %d\n", show(e).text, query sat((e)) {});
}

Expr ?randTerm(unsigned depth, unsigned numVars, arena_t ar) {
  allocate_using arena ar;
  if (depth == 0) {
    return new var(varE(new var("a" + str(rand() % numVars))));
  } else {
    switch (rand() % 3) {
    case 0:
      return new var(andE(randTerm(depth - 1, numVars, ar), randTerm(depth - 1, numVars, ar)));
    case 1:
      return new var(orE(randTerm(depth - 1, numVars, ar), randTerm(depth - 1, numVars, ar)));
    case 2:
      return new var(notE(randTerm(depth - 1, numVars, ar)));
    }
  }
}

int main(int argc, char *argv[]) {
  with_arena ar {
    test(term<Expr ?> { andE(varE("a"), notE(varE("a"))) });
    test(term<Expr ?> { andE(orE(varE("a"), varE("b")), andE(varE("c"), notE(varE("a")))) });
    test(randTerm(10, 10, ar));
  }
}
