grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

synthesized attribute continuationTransform::Expr;
inherited attribute continuationTransformIn::Expr;

nonterminal Goals with pps, env, errors, defs, transform<Expr>, continuationTransform, continuationTransformIn, substitutions, substituted<Goals>;
flowtype Goals = decorate {env, continuationTransformIn}, pps {}, errors {env}, defs {env}, transform {decorate}, continuationTransform {decorate}, substituted {substitutions};

abstract production consGoal
top::Goals ::= h::Goal t::Goals
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

abstract production nilGoal
top::Goals ::=
{
  propagate substituted;
  top.pps = [];
  top.errors := [];
  top.defs := [];
  top.continuationTransform = top.continuationTransformIn;
  top.transform = ableC_Expr { $Expr{top.continuationTransformIn}() };
}

function foldGoal
Goals ::= les::[Goal]
{
  return foldr(consGoal, nilGoal(), les);
}

nonterminal Goal with location, env, pp, errors, defs, transform<Expr>, transformIn<Expr>, continuationTransformIn, substitutions, substituted<Goal>;
flowtype Goal = decorate {env, transformIn, continuationTransformIn}, pp {}, errors {env}, defs {env}, transform {decorate}, substituted {substitutions};

abstract production predicateGoal
top::Goal ::= n::Name ts::TypeNames les::LogicExprs
{
  propagate substituted;
  top.pp = pp"${n.pp}<${ppImplode(pp", ", ts.pps)}>(${ppImplode(pp", ", les.pps)})";
  top.errors := ts.errors ++ les.errors;
  top.defs := ts.defs ++ les.defs;
  top.transform =
    ableC_Expr {
      inst $name{s"_predicate_${n.name}"}<$TypeNames{ts}>(
        $Exprs{les.transform}, _trail, $Expr{top.continuationTransformIn})
    };
  
  local typeParams::Names = n.predicateItem.typeParams;
  typeParams.instParamTypes = ts.typereps;
  
  local params::Parameters = n.predicateItem.params;
  params.env =
    addEnv(
      -- Add type args to global scope so that they are visible within template instantiations
      [globalDefsDef(typeParams.typeParamInstDefs)],
      -- NOT the env at the declaration site, but this is equivalent (and more efficient.)
      openScopeEnv(globalEnv(addEnv(ts.defs, ts.env))));
  params.returnType = nothing();
  params.position = 0;
  
  top.defs <- foldr(consDefs, nilDefs(), params.defs).canonicalDefs;
  
  ts.returnType = nothing();
  les.env = addEnv(ts.defs ++ params.defs, ts.env);
  les.expectedTypes = map(\ t::Type -> t.canonicalType, params.typereps);
  les.allowUnificationTypes = false;
  les.allocator = ableC_Expr { alloca };
  
  top.errors <- n.predicateLookupCheck;
  top.errors <-
    if null(n.predicateLookupCheck) && ts.count != typeParams.count
    then [err(
            n.location,
            s"Wrong number of type arguments for ${n.name}, " ++
            s"expected ${toString(typeParams.count)} but got ${toString(ts.count)}")]
    else [];
  top.errors <-
    if null(n.predicateLookupCheck) && les.count != params.count
    then [err(top.location, s"Wrong number of arguments to predicate ${n.name} (expected ${toString(params.count)}, got ${toString(les.count)})")]
    else [];
  top.errors <-
    flatMap(
      \ t::Type -> decorate t with { otherType = t; }.unifyErrors(n.location, top.env),
      ts.typereps);
}

abstract production inferredPredicateGoal
top::Goal ::= n::Name les::LogicExprs
{
  propagate substituted;
  top.pp = pp"${n.pp}(${ppImplode(pp", ", les.pps)})";
  top.errors :=
    if inferredTypeArguments.isJust && !containsErrorType(inferredTypeArguments.fromJust)
    then les.errors
    else [];
  top.defs :=
    if inferredTypeArguments.isJust
    then les.defs
    else [];
  top.transform =
    ableC_Expr {
      inst $name{s"_predicate_${n.name}"}<$TypeNames{
        foldr(
          consTypeName, nilTypeName(),
          map(
           \ t::Type -> typeName(directTypeExpr(t), baseTypeExpr()),
           inferredTypeArguments.fromJust))}>(
        $Exprs{les.transform}, _trail, $Expr{top.continuationTransformIn})
    };
  
  local typeParams::Names = n.predicateItem.typeParams;
  typeParams.instParamTypes = inferredTypeArguments.fromJust;
  
  local params::Parameters = n.predicateItem.params;
  params.env =
    addEnv(
      -- Add type args to global scope so that they are visible within template instantiations
      [globalDefsDef(typeParams.typeParamInstDefs)],
      -- NOT the env at the declaration site, but this is equivalent (and more efficient.)
      openScopeEnv(globalEnv(top.env)));
  params.returnType = nothing();
  params.position = 0;
  params.partialArgumentTypes = les.maybeTypereps;
  
  local inferredTypeArguments::Maybe<[Type]> =
    lookupAll(params.partialInferredTypes, typeParams.names);
  
  top.defs <-
    if inferredTypeArguments.isJust
    then foldr(consDefs, nilDefs(), params.defs).canonicalDefs
    else [];
  
  les.expectedTypes = map(\ t::Type -> t.canonicalType, params.typereps);
  les.allowUnificationTypes = false;
  les.allocator = ableC_Expr { alloca };
  
  top.errors <- n.predicateLookupCheck;
  top.errors <-
    if null(n.predicateLookupCheck) && (!inferredTypeArguments.isJust || containsErrorType(inferredTypeArguments.fromJust))
    then 
      [err(
         top.location,
         s"Type argument inference failed for ${n.name}(${
           implode(
             ", ",
             map(
               \ m::Maybe<Type> ->
                 case m of
                 | just(t) -> showType(t)
                 | nothing() -> "_"
                 end,
               les.maybeTypereps))})")]
    else [];
  top.errors <-
    if null(n.predicateLookupCheck) && les.count != params.count
    then [err(top.location, s"Wrong number of arguments to predicate ${n.name} (expected ${toString(params.count)}, got ${toString(les.count)})")]
    else [];
  top.errors <-
    case inferredTypeArguments of
    | just(ts) ->
      flatMap(
        \ t::Type -> decorate t with { otherType = t; }.unifyErrors(n.location, top.env),
        ts)
    | nothing() -> []
    end;
}

abstract production isGoal
top::Goal ::= le::LogicExpr e::Expr
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

abstract production equalsGoal
top::Goal ::= le1::LogicExpr le2::LogicExpr
{
  propagate substituted;
  top.pp = pp"(${le1.pp}) = (${le2.pp})";
  top.errors := le1.errors ++ le2.errors;
  top.defs := le1.defs ++ le2.defs;
  top.transform =
    ableC_Expr {
      $Expr{
        unifyExpr(
          le1.transform,
          le2.transform,
          justExpr(ableC_Expr { _trail }),
          location=builtin)} &&
      $Expr{top.transformIn}
    };
  
  top.errors <-
    if !le1.maybeTyperep.isJust
    then [err(le1.location, "Could not infer a type for lhs of goal")]
    else [];
  
  local expectedType::Type = fromMaybe(errorType(), le1.maybeTyperep);
  le1.expectedType = expectedType;
  le1.allowUnificationTypes = true;
  le1.allocator = ableC_Expr { alloca };
  le2.expectedType = expectedType;
  le2.allowUnificationTypes = true;
  le2.allocator = ableC_Expr { alloca };
  le2.env = addEnv(le1.defs, le1.env);
}

abstract production notEqualsGoal
top::Goal ::= le1::LogicExpr le2::LogicExpr
{
  propagate substituted;
  top.pp = pp"(${le1.pp}) \= (${le2.pp})";
  
  forwards to notGoal(equalsGoal(le1, le2, location=top.location), location=top.location);
}

abstract production eqGoal
top::Goal ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"(${e1.pp}) =:= (${e2.pp})";
  top.errors := e1.errors ++ e2.errors;
  top.defs := e1.defs ++ e2.defs;
  top.transform =
    ableC_Expr {
      ({$Stmt{makeUnwrappedVarDecls(e1.freeVariables ++ e2.freeVariables, top.env)}
        $Expr{decExpr(e1, location=builtin)} == $Expr{decExpr(e2, location=builtin)};}) &&
        $Expr{top.transformIn}
    };
  
  -- TODO: Types should both be equality types
  top.errors <-
    if compatibleTypes(e1.typerep, e2.typerep, true, true)
    then []
    else [err(top.location, s"Types to =:= goal must match (got ${showType(e1.typerep)}, ${showType(e2.typerep)})")];
  
  e1.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  e1.returnType = nothing();
  e2.env = addEnv(e1.defs, e1.env);
  e2.returnType = nothing();
}

abstract production neqGoal
top::Goal ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"(${e1.pp}) =\= (${e2.pp})";
  top.errors := e1.errors ++ e2.errors;
  top.defs := e1.defs ++ e2.defs;
  top.transform =
    ableC_Expr {
      ({$Stmt{makeUnwrappedVarDecls(e1.freeVariables ++ e2.freeVariables, top.env)}
        $Expr{decExpr(e1, location=builtin)} != $Expr{decExpr(e2, location=builtin)};}) &&
        $Expr{top.transformIn}
    };
  
  -- TODO: Types should both be equality types
  top.errors <-
    if compatibleTypes(e1.typerep, e2.typerep, true, true)
    then []
    else [err(top.location, s"Types to =/= goal must match (got ${showType(e1.typerep)}, ${showType(e2.typerep)})")];
  
  e1.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  e1.returnType = nothing();
  e2.env = addEnv(e1.defs, e1.env);
  e2.returnType = nothing();
}

abstract production ltGoal
top::Goal ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"(${e1.pp}) < (${e2.pp})";
  top.errors := e1.errors ++ e2.errors;
  top.defs := e1.defs ++ e2.defs;
  top.transform =
    ableC_Expr {
      ({$Stmt{makeUnwrappedVarDecls(e1.freeVariables ++ e2.freeVariables, top.env)}
        $Expr{decExpr(e1, location=builtin)} < $Expr{decExpr(e2, location=builtin)};}) &&
        $Expr{top.transformIn}
    };
  
  -- TODO: Types should both be comparison types
  top.errors <-
    if compatibleTypes(e1.typerep, e2.typerep, true, true)
    then []
    else [err(top.location, s"Types to < goal must match (got ${showType(e1.typerep)}, ${showType(e2.typerep)})")];
  
  e1.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  e1.returnType = nothing();
  e2.env = addEnv(e1.defs, e1.env);
  e2.returnType = nothing();
}

abstract production eltGoal
top::Goal ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"(${e1.pp}) =< (${e2.pp})";
  top.errors := e1.errors ++ e2.errors;
  top.defs := e1.defs ++ e2.defs;
  top.transform =
    ableC_Expr {
      ({$Stmt{makeUnwrappedVarDecls(e1.freeVariables ++ e2.freeVariables, top.env)}
        $Expr{decExpr(e1, location=builtin)} <= $Expr{decExpr(e2, location=builtin)};}) &&
        $Expr{top.transformIn}
    };
  
  -- TODO: Types should both be comparison types
  top.errors <-
    if compatibleTypes(e1.typerep, e2.typerep, true, true)
    then []
    else [err(top.location, s"Types to =< goal must match (got ${showType(e1.typerep)}, ${showType(e2.typerep)})")];
  
  e1.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  e1.returnType = nothing();
  e2.env = addEnv(e1.defs, e1.env);
  e2.returnType = nothing();
}

abstract production gtGoal
top::Goal ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"(${e1.pp}) > (${e2.pp})";
  top.errors := e1.errors ++ e2.errors;
  top.defs := e1.defs ++ e2.defs;
  top.transform =
    ableC_Expr {
      ({$Stmt{makeUnwrappedVarDecls(e1.freeVariables ++ e2.freeVariables, top.env)}
        $Expr{decExpr(e1, location=builtin)} > $Expr{decExpr(e2, location=builtin)};}) &&
        $Expr{top.transformIn}
    };
  
  -- TODO: Types should both be comparison types
  top.errors <-
    if compatibleTypes(e1.typerep, e2.typerep, true, true)
    then []
    else [err(top.location, s"Types to > goal must match (got ${showType(e1.typerep)}, ${showType(e2.typerep)})")];
  
  e1.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  e1.returnType = nothing();
  e2.env = addEnv(e1.defs, e1.env);
  e2.returnType = nothing();
}

abstract production gteGoal
top::Goal ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"(${e1.pp}) >= (${e2.pp})";
  top.errors := e1.errors ++ e2.errors;
  top.defs := e1.defs ++ e2.defs;
  top.transform =
    ableC_Expr {
      ({$Stmt{makeUnwrappedVarDecls(e1.freeVariables ++ e2.freeVariables, top.env)}
        $Expr{decExpr(e1, location=builtin)} >= $Expr{decExpr(e2, location=builtin)};}) &&
        $Expr{top.transformIn}
    };
  
  -- TODO: Types should both be comparison types
  top.errors <-
    if compatibleTypes(e1.typerep, e2.typerep, true, true)
    then []
    else [err(top.location, s"Types to >= goal must match (got ${showType(e1.typerep)}, ${showType(e2.typerep)})")];
  
  e1.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  e1.returnType = nothing();
  e2.env = addEnv(e1.defs, e1.env);
  e2.returnType = nothing();
}

abstract production notGoal
top::Goal ::= g::Goal
{
  propagate substituted;
  top.pp = pp"\+ (${g.pp})";
  top.errors := g.errors;
  top.defs := g.defs;
  
  g.transformIn = ableC_Expr { (_Bool)1 };
  g.continuationTransformIn = ableC_Expr { lambda allocate(alloca) () -> ((_Bool)1) };
  top.transform =
    ableC_Expr {
      proto_typedef size_t;
      ({size_t _not_trail_index = _trail.length;
        $Expr{g.transform}? 0 :
          // Undo substitutions made before failure.  Only needed if g fails, since when g succeeds
          // the entire rule fails so thse are fixed later.
          (undo_trail(_trail, _not_trail_index), 1);}) && $Expr{top.transformIn}
    };
}

abstract production cutGoal
top::Goal ::=
{
  propagate substituted;
  top.pp = pp"!";
  top.errors := [];
  top.defs := [];
  top.transform =
    ableC_Expr {
      // If a failure occurs, longjmp out of all continuations back to the current
      // predicate function, which fails immediately.  This is OK because all data
      // is stack-allocated.
      $Expr{top.transformIn} || (longjmp(_cut_buffer, 1), 1)
    };
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
        nubBy(nameEq, freeVariables)));
}
