#include <unification.xh>

datatype Bar {
  Bar(int);
};

prolog {
  foo(datatype Bar);
  foo(Bar(_)).
}
