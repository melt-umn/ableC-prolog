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

size_t showExprMaxLen(Expr ?e);
size_t showExpr(char *buf, Expr ?e);

show Expr with showExprMaxLen, showExprToBuf;

size_t showExprMaxLen(Expr ?e) {
  return match (e)
    (?&value(?&val) -> showMaxLen(val);
     ?&e() -> 1;
     ?&variable(?&id) -> id.length;
     ?&negative(e1) -> 2 + showMaxLen(e1);
     ?&add(e1, e2) -> 5 + showMaxLen(e1) + showMaxLen(e2);
     ?&subtract(e1, e2) -> 5 + showMaxLen(e1) + showMaxLen(e2);
     ?&multiply(e1, e2) -> 5 + showMaxLen(e1) + showMaxLen(e2);
     ?&divide(e1, e2) -> 5 + showMaxLen(e1) + showMaxLen(e2);
     ?&exponent(e1, e2) -> 5 + showMaxLen(e1) + showMaxLen(e2);
     ?&logrithm(?&e(), e) -> 6 + showMaxLen(e);
     ?&logrithm(e1, e2) -> 9 + showMaxLen(e1) + showMaxLen(e2);
     _ -> show_var_max_len(e););
}

size_t wrapShowExpr(char *buf, Expr ?e) {
  return match (e)
    (?&value(?&val) -> buildStr(buf, show(val));
     ?&e() -> buildStr(buf, str("e"));
     ?&variable(?&id) -> buildStr(buf, id);
     _ -> buildStr(buf, "(" + show(e) + ")"););
}

size_t showExpr(char *buf, Expr ?e) {
  return match (e)
    (?&value(?&val) -> buildStr(buf, show(val));
     ?&e() -> buildStr(buf, str("e"));
     ?&variable(?&id) -> buildStr(buf, id);
     ?&negative(e1) -> buildStr(buf, "-" + wrapShowExpr(e1));
     ?&add(e1, e2) -> buildStr(buf, wrapShowExpr(e1) + " + " + wrapShowExpr(e2));
     ?&subtract(e1, e2) -> buildStr(buf, wrapShowExpr(e1) + " - " + wrapShowExpr(e2));
     ?&multiply(e1, e2) -> buildStr(buf, wrapShowExpr(e1) + " * " + wrapShowExpr(e2));
     ?&divide(e1, e2) -> buildStr(buf, wrapShowExpr(e1) + " / " + wrapShowExpr(e2));
     ?&exponent(e1, e2) -> buildStr(buf, wrapShowExpr(e1) + " ^ " + wrapShowExpr(e2));
     ?&logrithm(?&e(), e) -> buildStr(buf, "ln(" + showExpr(e) + ")");
     ?&logrithm(e1, e2) -> buildStr(buf, "log(" + showExpr(e1) + ", " + showExpr(e2) + ")");
     _ -> show_var(buf, e););
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
  d(Expr e1, string ?var, Expr ?res);
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
  allocate_using stack;
  //test(term<Expr ?> { exponent(negative(variable("x")), value(3)) });
  //test(term<Expr ?> { exponent(negative(variable("x")), add(value(4), negative(value(1)))) });

  //Expr ?e = term<Expr ?> { logrithm(value(10), logrithm(value(10), logrithm(value(10), logrithm(value(10), logrithm(value(10), logrithm(value(10), variable("x"))))))) };
  //Expr ?e = term<Expr ?> { divide(divide(divide(divide(variable(x), variable(x)), variable(x)), variable(x)), variable(x)) };
  Expr ?e = term<Expr ?> { multiply(add(variable("x"), value(1)), multiply(add(exponent(variable("x"), value(2)), value(2)), multiply(add(exponent(variable("x"), value(3)), value(3)), multiply(add(exponent(variable("x"), value(4)), value(4)), add(exponent(variable("x"), value(5)), value(5)))))) };
  
  test(e);
}
