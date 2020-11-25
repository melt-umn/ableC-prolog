#include <unification.xh>
#include <stdbool.h>

typedef datatype Expr Expr;

datatype Expr {
  value(int ?val);
  e();
  variable(string ?id);
  negative(Expr ?e);
  add(Expr ?e1, Expr ?e2);
  subtract(Expr ?e1, Expr ?e2);
  multiply(Expr ?e1, Expr ?e2);
  divide(Expr ?e1, Expr ?e2);
  exponent(Expr ?e1, Expr ?e2);
  logrithm(Expr ?e1, Expr ?e2);
};

string showExpr(Expr ?e);
string wrapShowExpr(Expr ?e) {
  return match (e)
    (?&value(?&val) -> show(val);
     ?&e() -> str("e");
     ?&variable(?&id) -> id;
     _ -> "(" + showExpr(e) + ")";);
}

string showExpr(Expr ?e) {
  return match (e)
    (?&value(?&val) -> show(val);
     ?&e() -> str("e");
     ?&variable(?&id) -> id;
     ?&negative(e1) -> "-" + wrapShowExpr(e1);
     ?&add(e1, e2) -> wrapShowExpr(e1) + " + " + wrapShowExpr(e2);
     ?&subtract(e1, e2) -> wrapShowExpr(e1) + " - " + wrapShowExpr(e2);
     ?&multiply(e1, e2) -> wrapShowExpr(e1) + " * " + wrapShowExpr(e2);
     ?&divide(e1, e2) -> wrapShowExpr(e1) + " / " + wrapShowExpr(e2);
     ?&exponent(e1, e2) -> wrapShowExpr(e1) + " ^ " + wrapShowExpr(e2);
     ?&logrithm(?&e(), e) -> "ln(" + showExpr(e) + ")";
     ?&logrithm(e1, e2) -> "log(" + showExpr(e1) + ", " + showExpr(e2) + ")";
     _ -> show(e););
}

int mod(int a, int b) {
  return a % b;
}

// Workaround for lack of dif predicate
#define dif(A, B) A \= B

prolog {
  power(int, int, int ?);
  simplified(Expr e1, Expr ?e2);
  constant(Expr ?e1, string ?var);
  d(Expr e, string ?var, Expr ?res);
# include "e4.pl"
}

bool test(Expr ?e) {
  printf("%s\n", show(e).text);
  printf("%s\n", showExpr(e).text);
  bool res1 = query E is e, simplified(E, E1) {
    printf("simplified: %s\n", showExpr(E1).text);
    return false;
  };
  bool res2 = query E is e, d(E, "x", E1), simplified(E1, E2) {
    printf("d/dx: %s\n", showExpr(E1).text);
    printf("d/dx simplified: %s\n", showExpr(E2).text);
    return false;
  };
  printf("\n");
  return res1 && res2;
}

int main() {
  //test(term<Expr ?>(alloca) { exponent(negative(variable("x")), value(3)) });
  //test(term<Expr ?>(alloca) { exponent(negative(variable("x")), add(value(4), negative(value(1)))) });

  //Expr ?e = term<Expr ?>(alloca) { logrithm(value(10), logrithm(value(10), logrithm(value(10), logrithm(value(10), logrithm(value(10), logrithm(value(10), variable("x"))))))) };
  //Expr ?e = term<Expr ?>(alloca) { divide(divide(divide(divide(variable(x), variable(x)), variable(x)), variable(x)), variable(x)) };
  Expr ?e = term<Expr ?>(alloca) { multiply(add(variable("x"), value(1)), multiply(add(exponent(variable("x"), value(2)), value(2)), multiply(add(exponent(variable("x"), value(3)), value(3)), multiply(add(exponent(variable("x"), value(4)), value(4)), add(exponent(variable("x"), value(5)), value(5)))))) };
  
  test(e);
}
