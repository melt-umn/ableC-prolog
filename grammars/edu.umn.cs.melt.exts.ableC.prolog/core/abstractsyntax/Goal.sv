grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

import core:monad;

autocopy attribute refVariables::[Name];

synthesized attribute continuationTransform::Expr;
inherited attribute continuationTransformIn::Expr;

nonterminal Goals with pps, env, refVariables, errors, defs, freeVariables, transform<Expr>, continuationTransform, continuationTransformIn;
flowtype Goals = decorate {env, refVariables, continuationTransformIn}, pps {}, errors {refVariables, env}, defs {env}, freeVariables {env}, transform {decorate}, continuationTransform {decorate};

propagate errors, defs on Goals;

abstract production consGoal
top::Goals ::= h::Goal t::Goals
{
  top.pps = h.pp :: t.pps;
  top.freeVariables := h.freeVariables ++ removeDefsFromNames(h.defs, t.freeVariables);
  
  t.env = addEnv(h.defs, h.env);
  
  top.continuationTransform =
    ableC_Expr { lambda allocate(alloca) () -> (_Bool)$Expr{top.transform} };
  top.transform = h.transform;
  h.continuationTransformIn = t.continuationTransform;
  h.transformIn = t.transform;
  t.continuationTransformIn = top.continuationTransformIn;
}

abstract production nilGoal
top::Goals ::=
{
  propagate freeVariables;
  top.pps = [];
  top.continuationTransform = top.continuationTransformIn;
  top.transform = ableC_Expr { $Expr{top.continuationTransformIn}() };
}

function foldGoal
Goals ::= les::[Goal]
{
  return foldr(consGoal, nilGoal(), les);
}

nonterminal Goal with location, env, refVariables, pp, errors, defs, freeVariables, transform<Expr>, transformIn<Expr>, continuationTransformIn;
flowtype Goal = decorate {env, refVariables, transformIn, continuationTransformIn}, pp {}, errors {refVariables, env}, defs {env}, freeVariables {env}, transform {decorate};

propagate freeVariables on Goal;

abstract production predicateGoal
top::Goal ::= n::Name ts::TemplateArgNames les::LogicExprs
{
  propagate errors, defs;
  top.pp = pp"${n.pp}<${ppImplode(pp", ", ts.pps)}>(${ppImplode(pp", ", les.pps)})";
  top.transform =
    ableC_Expr {
      inst $name{s"_predicate_${n.name}"}<$TemplateArgNames{ts}>(
        $Exprs{les.transform}, _trail, $Expr{top.continuationTransformIn})
    };
  
  local templateParams::TemplateParameters = n.predicateItem.templateParams;
  
  ts.edu:umn:cs:melt:exts:ableC:templating:abstractsyntax:paramNames = templateParams.names;
  ts.paramKinds = templateParams.kinds;
  ts.substEnv = s:fail();
  
  local params::Parameters = rewriteWith(topDownSubs(ts.substDefs), n.predicateItem.params).fromJust;
  -- NOT the env at the declaration site, but this is equivalent (and more efficient.)
  params.env = openScopeEnv(globalEnv(addEnv(ts.defs, ts.env)));
  params.returnType = nothing();
  params.position = 0;
  
  top.defs <- foldr(consDefs, nilDefs(), params.defs).canonicalDefs;
  
  les.env = addEnv(ts.defs ++ params.defs, ts.env);
  les.expectedTypes = map(\ t::Type -> t.canonicalType, params.typereps);
  les.allowUnificationTypes = false;
  les.allocator = ableC_Expr { alloca };
  
  top.errors <- n.predicateLookupCheck;
  top.errors <-
    if null(n.predicateLookupCheck) && ts.count != templateParams.count
    then [err(
            n.location,
            s"Wrong number of type arguments for ${n.name}, " ++
            s"expected ${toString(templateParams.count)} but got ${toString(ts.count)}")]
    else [];
  top.errors <-
    if null(n.predicateLookupCheck) && les.count != params.count
    then [err(top.location, s"Wrong number of arguments to predicate ${n.name} (expected ${toString(params.count)}, got ${toString(les.count)})")]
    else [];
  top.errors <- ts.argreps.templateArgUnifyErrors(n.location, top.env);
}

abstract production inferredPredicateGoal
top::Goal ::= n::Name les::LogicExprs
{
  top.pp = pp"${n.pp}(${ppImplode(pp", ", les.pps)})";
  top.errors :=
    if inferredTemplateArguments.isJust && !inferredTemplateArguments.fromJust.containsErrorType
    then les.errors
    else [];
  top.defs :=
    if inferredTemplateArguments.isJust
    then les.defs
    else [];
  top.transform =
    ableC_Expr {
      inst $name{s"_predicate_${n.name}"}<$TemplateArgNames{ts.argNames}>(
        $Exprs{les.transform}, _trail, $Expr{top.continuationTransformIn})
    };
  
  local templateParams::TemplateParameters = n.predicateItem.templateParams;
  templateParams.templateParamEnv = globalEnv(top.env);
  
  -- Decorate parameters the first time for template parameter inference...
  local infParams::Parameters = n.predicateItem.params;
  -- NOT the env at the declaration site, but this is equivalent (and more efficient.)
  infParams.env = openScopeEnv(globalEnv(top.env));
  infParams.returnType = nothing();
  infParams.position = 0;
  infParams.partialArgumentTypes = les.maybeTypereps;
  
  local inferredTemplateArguments::Maybe<TemplateArgs> =
    mapMaybe(
      foldr(consTemplateArg, nilTemplateArg(), _),
      lookupAll(infParams.partialInferredArgs, templateParams.names));
  
  local ts::TemplateArgs = inferredTemplateArguments.fromJust;
  ts.edu:umn:cs:melt:exts:ableC:templating:abstractsyntax:paramNames = templateParams.names;
  
  -- ... then re-decorate the substituted parameters to compute the expected types.
  local params::Parameters = rewriteWith(topDownSubs(ts.substDefs), n.predicateItem.params).fromJust;
  -- NOT the env at the declaration site, but this is equivalent (and more efficient.)
  params.env = openScopeEnv(globalEnv(top.env));
  params.returnType = nothing();
  params.position = 0;
  
  top.defs <-
    if inferredTemplateArguments.isJust
    then foldr(consDefs, nilDefs(), params.defs).canonicalDefs
    else [];
  
  les.expectedTypes =
    if inferredTemplateArguments.isJust
    then map(\ t::Type -> t.canonicalType, params.typereps)
    else [];
  les.allowUnificationTypes = false;
  les.allocator = ableC_Expr { alloca };
  
  top.errors <- n.predicateLookupCheck;
  top.errors <-
    if null(n.predicateLookupCheck) && (!inferredTemplateArguments.isJust || inferredTemplateArguments.fromJust.containsErrorType)
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
    if null(n.predicateLookupCheck) && les.count != infParams.count
    then [err(top.location, s"Wrong number of arguments to predicate ${n.name} (expected ${toString(infParams.count)}, got ${toString(les.count)})")]
    else [];
  top.errors <-
    case inferredTemplateArguments of
    | just(ts) -> ts.templateArgUnifyErrors(n.location, top.env)
    | nothing() -> []
    end;
}

abstract production isGoal
top::Goal ::= le::LogicExpr e::Expr
{
  propagate errors, defs;
  top.pp = pp"(${le.pp}) is (${e.pp})";
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
  propagate errors, defs;
  top.pp = pp"(${le1.pp}) = (${le2.pp})";
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
  top.pp = pp"(${le1.pp}) \= (${le2.pp})";
  
  forwards to notGoal(equalsGoal(le1, le2, location=top.location), location=top.location);
}

abstract production eqGoal
top::Goal ::= e1::Expr e2::Expr
{
  propagate errors, defs;
  top.pp = pp"(${e1.pp}) =:= (${e2.pp})";
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
  propagate errors, defs;
  top.pp = pp"(${e1.pp}) =\= (${e2.pp})";
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
  propagate errors, defs;
  top.pp = pp"(${e1.pp}) < (${e2.pp})";
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
  propagate errors, defs;
  top.pp = pp"(${e1.pp}) =< (${e2.pp})";
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
  propagate errors, defs;
  top.pp = pp"(${e1.pp}) > (${e2.pp})";
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
  propagate errors, defs;
  top.pp = pp"(${e1.pp}) >= (${e2.pp})";
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
  propagate errors, defs;
  top.pp = pp"\+ (${g.pp})";
  
  g.transformIn = ableC_Expr { (_Bool)1 };
  g.continuationTransformIn = ableC_Expr { lambda allocate(alloca) () -> (_Bool)1 };
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
  propagate errors, defs;
  top.pp = pp"!";
  top.transform =
    ableC_Expr {
      // If a failure occurs, longjmp out of all continuations back to the current
      // predicate function, which fails immediately.  This is OK because all data
      // is stack-allocated.
      $Expr{top.transformIn} || (longjmp(_cut_buffer, 1), 1)
    };
}

abstract production initiallyGoal
top::Goal ::= s::Stmt
{
  propagate errors, defs;
  top.pp = pp"initially ${braces(nestlines(2, s.pp))})";
  
  top.transform =
    ableC_Expr {
      ({{$Stmt{makeUnwrappedVarDecls(s.freeVariables, top.env)}
         $Stmt{decStmt(s)}}
        $Expr{top.transformIn};})
    };
  
  s.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  s.returnType = nothing();
}

abstract production finallyGoal
top::Goal ::= s::Stmt
{
  propagate errors, defs;
  top.pp = pp"finally ${braces(nestlines(2, s.pp))})";
  
  top.transform =
    ableC_Expr {
      ({{$Stmt{makeUnwrappedVarDecls(s.freeVariables, top.env)}
         push_action(_trail, lambda allocate(malloc) (void) -> void { $Stmt{decStmt(s)} }, free);}
        $Expr{top.transformIn};})
    };
  
  s.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  s.returnType = nothing();
}

synthesized attribute templateArgUnifyErrors::([Message] ::= Location Decorated Env) occurs on TemplateArgs, TemplateArg;

aspect production consTemplateArg
top::TemplateArgs ::= h::TemplateArg t::TemplateArgs
{
  top.templateArgUnifyErrors =
    \ l::Location env::Decorated Env ->
      h.templateArgUnifyErrors(l, env) ++ t.templateArgUnifyErrors(l, env);
}

aspect production nilTemplateArg
top::TemplateArgs ::=
{
  top.templateArgUnifyErrors = \ l::Location env::Decorated Env -> [];
}

aspect default production
top::TemplateArg ::=
{
  top.templateArgUnifyErrors = \ l::Location env::Decorated Env -> [];
}

aspect production typeTemplateArg
top::TemplateArg ::= t::Type
{
  top.templateArgUnifyErrors =
    decorate t.defaultFunctionArrayLvalueConversion
      with {otherType = t.defaultFunctionArrayLvalueConversion;}.unifyErrors;
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
                   inst value_loc<$directTypeExpr{sub}>($name{"_" ++ n.name}, $stringLiteralExpr{n.location.unparse});
               }]
            | _ -> []
            end
          | _ -> []
          end,
        nubBy(nameEq, freeVariables)));
}
