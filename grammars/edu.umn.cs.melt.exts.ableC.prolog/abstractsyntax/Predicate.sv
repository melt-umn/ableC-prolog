grammar edu:umn:cs:melt:exts:ableC:prolog:abstractsyntax;

synthesized attribute asContinuation::Expr;

nonterminal Predicates with pps, env, errors, defs, asContinuation, transform<Expr>, transformIn<Expr>, substitutions, substituted<Predicates>;

abstract production consPredicate
top::Predicates ::= h::Predicate t::Predicates
{
  propagate substituted;
  top.pps = h.pp :: t.pps;
  top.errors := h.errors ++ t.errors;
  top.defs := h.defs ++ t.defs;
  
  t.env = addEnv(h.defs, h.env);
  
  top.asContinuation = ableC_Expr { lambda allocate(alloca) () -> ($Expr{top.transform}) };
  top.transform = h.transform;
  h.transformIn = t.asContinuation;
  t.transformIn = top.transformIn;
}

abstract production nilPredicate
top::Predicates ::=
{
  propagate substituted;
  top.pps = [];
  top.errors := [];
  top.defs := [];
  top.asContinuation = top.transformIn;
  top.transform = ableC_Expr { $Expr{top.transformIn}() };
}

function foldPredicate
Predicates ::= les::[Predicate]
{
  return foldr(consPredicate, nilPredicate(), les);
}

nonterminal Predicate with location, env, pp, errors, defs, transform<Expr>, transformIn<Expr>, substitutions, substituted<Predicate>;

abstract production predicate
top::Predicate ::= n::Name ts::TypeNames les::LogicExprs
{
  propagate substituted;
  top.pp = pp"${n.pp}${if ts.count == 0 then pp"" else pp"<${ppImplode(pp", ", ts.pps)}>"}(${ppImplode(pp", ", les.pps)})";
  top.errors := les.errors;
  top.defs := ts.defs ++ les.defs;
  top.transform =
    ableC_Expr {
      inst $name{n.name}<$TypeNames{ts}>($Exprs{les.transform}, $Expr{top.transformIn})
    };
  
  ts.returnType = nothing();
  les.expectedTypes = n.predicateItem.instTypereps(ts.typereps);
  
  top.errors <- n.predicateLookupCheck;
  top.errors <-
    if null(n.predicateLookupCheck) && les.count != length(les.expectedTypes)
    then [err(top.location, s"Wrong number of arguments to predicate ${n.name} (expected ${toString(length(les.expectedTypes))}, got ${toString(les.count)})")]
    else [];
  top.errors <-
    flatMap(
      \ t::Type -> decorate t with { otherType = t; }.unifyErrors(n.location, top.env),
      ts.typereps);
}
