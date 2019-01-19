#include <unification.xh>
#include <list.xh>
#include <stdbool.h>

template<a, b>
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

string showExpr(Expr ?e);
string wrapShowExpr(Expr ?e) {
  return match (e)
    (?&t() -> str("true");
     ?&f() -> str("false");
     ?&varE(?&id) -> id;
     _ -> "(" + showExpr(e) + ")";);
}

string showExpr(Expr ?e) {
  return match (e)
    (?&t() -> str("true");
     ?&f() -> str("false");
     ?&varE(?&id) -> id;
     ?&andE(e1, e2) -> wrapShowExpr(e1) + " & " + wrapShowExpr(e2);
     ?&orE(e1, e2) -> wrapShowExpr(e1) + " | " + wrapShowExpr(e2);
     ?&notE(e1) -> "!" + wrapShowExpr(e1);
     _ -> show(e););
}


prolog {
  lookup(string ?, bool ?, Env);
  evaluate(Expr ?, bool, Env);
  sat(Expr ?);

# include "e5.pl"
}

void test(Expr ?e) {
  printf("%s: %d\n", showExpr(e).text, query E is e, sat(E) { return true; });
}

Expr ?randTerm(unsigned depth, unsigned numVars) {
  if (depth == 0) {
    return boundvar(varE(boundvar("a" + str(rand() % numVars), GC_malloc)), GC_malloc);
  } else {
    switch (rand() % 3) {
    case 0:
      return boundvar(andE(randTerm(depth - 1, numVars), randTerm(depth - 1, numVars)), GC_malloc);
    case 1:
      return boundvar(orE(randTerm(depth - 1, numVars), randTerm(depth - 1, numVars)), GC_malloc);
    case 2:
      return boundvar(notE(randTerm(depth - 1, numVars)), GC_malloc);
    }
  }
}

int main(int argc, char *argv[]) {
  test(term<Expr ?>(alloca) { andE(varE("a"), notE(varE("a"))) });
  test(term<Expr ?>(alloca) { andE(orE(varE("a"), varE("b")), andE(varE("c"), notE(varE("a")))) });
  test(randTerm(10, 10));
}
