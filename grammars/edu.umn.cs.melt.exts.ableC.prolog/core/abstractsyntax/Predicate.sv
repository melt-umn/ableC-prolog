grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

synthesized attribute continuationTransform::Expr;
inherited attribute continuationTransformIn::Expr;

nonterminal Predicates with pps, env, errors, defs, transform<Expr>, continuationTransform, continuationTransformIn, substitutions, substituted<Predicates>;
flowtype Predicates = decorate {env, continuationTransformIn}, pps {}, errors {env}, defs {env}, transform {decorate}, continuationTransform {decorate}, substituted {substitutions};

abstract production consPredicate
top::Predicates ::= h::Predicate t::Predicates
{
  propagate substituted;
  top.pps = h.pp :: t.pps;
  top.errors := h.errors ++ t.errors;
  top.defs := h.defs ++ t.defs;
  
  t.env = addEnv(h.defs, h.env);
  
  top.continuationTransform =
    ableC_Expr { lambda allocate(alloca) () -> ((_Bool)$Expr{top.transform}) };
  top.transform = h.transform;
  h.continuationTransformIn = t.continuationTransform;
  h.transformIn = t.transform;
  t.continuationTransformIn = top.continuationTransformIn;
}

abstract production nilPredicate
top::Predicates ::=
{
  propagate substituted;
  top.pps = [];
  top.errors := [];
  top.defs := [];
  top.continuationTransform = top.continuationTransformIn;
  top.transform = ableC_Expr { $Expr{top.continuationTransformIn}() };
}

function foldPredicate
Predicates ::= les::[Predicate]
{
  return foldr(consPredicate, nilPredicate(), les);
}

nonterminal Predicate with location, env, pp, errors, defs, transform<Expr>, transformIn<Expr>, continuationTransformIn, substitutions, substituted<Predicate>;
flowtype Predicate = decorate {env, transformIn, continuationTransformIn}, pp {}, errors {env}, defs {env}, transform {decorate}, substituted {substitutions};

abstract production predicate
top::Predicate ::= n::Name ts::TypeNames les::LogicExprs
{
  propagate substituted;
  top.pp = pp"${n.pp}${if ts.count == 0 then pp"" else pp"<${ppImplode(pp", ", ts.pps)}>"}(${ppImplode(pp", ", les.pps)})";
  top.errors := ts.errors ++ les.errors;
  top.defs := ts.defs ++ les.defs;
  top.transform =
    ableC_Expr {
      inst $name{s"_predicate_${n.name}"}<$TypeNames{ts}>($Exprs{les.transform}, $Expr{top.continuationTransformIn})
    };
  
  ts.returnType = nothing();
  les.expectedTypes = n.predicateItem.instTypereps(ts.typereps);
  les.allowUnificationTypes = false;
  les.allocator = ableC_Expr { alloca };
  
  top.errors <- n.predicateLookupCheck;
  top.errors <-
    if null(n.predicateLookupCheck) && ts.count != n.predicateItem.typeParams.count
    then [err(
            n.location,
            s"Wrong number of type arguments for ${n.name}, " ++
            s"expected ${toString(n.predicateItem.typeParams.count)} but got ${toString(ts.count)}")]
    else [];
  top.errors <-
    if null(n.predicateLookupCheck) && les.count != length(les.expectedTypes)
    then [err(top.location, s"Wrong number of arguments to predicate ${n.name} (expected ${toString(length(les.expectedTypes))}, got ${toString(les.count)})")]
    else [];
  top.errors <-
    flatMap(
      \ t::Type -> decorate t with { otherType = t; }.unifyErrors(n.location, top.env),
      ts.typereps);
}

abstract production isPredicate
top::Predicate ::= le::LogicExpr e::Expr
{
  propagate substituted;
  top.pp = pp"(${le.pp}) is (${e.pp})";
  top.errors := le.errors ++ e.errors;
  top.defs := le.defs ++ e.defs;
  top.transform =
    ableC_Expr {
      $Expr{
        unifyExpr(
          le.transform,
          ableC_Expr {
            ({$Stmt{makeUnwrappedVarDecls(e.freeVariables, top.env)}
              $Expr{decExpr(e, location=builtin)};})
          },
          justExpr(ableC_Expr { _trail }),
          location=builtin)} &&
      $Expr{top.transformIn}
    };
  
  le.expectedType = e.typerep;
  le.allowUnificationTypes = true;
  le.allocator = ableC_Expr { alloca };
  -- Don't add le.defs to e's env here, since decorating le requires e's typerep
  e.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  e.returnType = nothing();
}

-- Generate "unwrapped" values corresponding to any variables referenced in the expression.
function makeUnwrappedVarDecls
Stmt ::= freeVariables::[Name] env::Decorated Env
{
  return
    foldStmt(
      flatMap(
        \ n::Name ->
          case lookupValueInLocalScope(n.name, env) of
          | i :: _ ->
            case i.typerep of
            | extType(_, varType(sub)) ->
              [ableC_Stmt {
                 $directTypeExpr{i.typerep} $name{"_" ++ n.name} = $Name{n};
                 $directTypeExpr{sub} $name{n.name} =
                   inst value<$directTypeExpr{sub}>($name{"_" ++ n.name});
               }]
            | _ -> []
            end
          | _ -> []
          end,
        freeVariables));
}
