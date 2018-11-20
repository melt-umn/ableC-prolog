grammar edu:umn:cs:melt:exts:ableC:prolog:abstractsyntax;

synthesized attribute asContinuation::Expr;

nonterminal Predicates with pps, env, errors, defs, asContinuation, transform<Expr>, transformIn<Expr>, substituted<Predicates>;

abstract production consPredicate
top::Predicates ::= h::Predicate t::Predicates
{
  propagate substituted;
  top.pps = h.pp :: t.pps;
  top.errors := h.errors ++ t.errors;
  
  t.env = addEnv(h.defs, h.env);
  
  top.asContinuation = ableC_Expr { lambda allocate(alloca) () -> ($Expr{top.transform}) };
  top.transform = h.transform;
  h.transformIn = t.asContinuation;
}

abstract production nilPredicate
top::Predicates ::=
{
  propagate substituted;
  top.pps = [];
  top.errors := [];
  top.asContinuation = ableC_Expr { _continuation };
  top.transform = ableC_Expr { _continuation() };
}

nonterminal Predicate with location, env, pp, errors, defs, transform<Expr>, transformIn<Expr>, substituted<Predicate>;

abstract production predicate
top::Predicate ::= n::Name les::LogicExprs
{
  propagate substituted;
  top.pp = pp"${n.pp}(${ppImplode(pp", ", les.pps)})";
  top.errors := les.errors; -- TODO: Lookup check
  top.transform = ableC_Expr { $Name{n}($Exprs{les.transform}, $Expr{top.transformIn}) };
}
