#include <unification.xh>
#include <list.xh>
#include <stdbool.h>

template<a, b>
datatype Pair {
  pair(a fst, b snd);
};

typedef list<inst Pair<string ?, bool ?> ?> ?Env;

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

# define member(l, item) member<inst Pair<string ?, bool ?>>(l, item)
# include "e5.pl"
# undef member
}

void test(Expr ?e) {
  printf("%s: %d\n", showExpr(e).text, query E is e, sat(E) { return true; });
}

int main() {
  test(term<Expr ?>(alloca) { andE(varE("a"), notE(varE("a"))) });
  test(term<Expr ?>(alloca) { andE(orE(varE("a"), varE("b")), andE(varE("c"), notE(varE("a")))) });
}
