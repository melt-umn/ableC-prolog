grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

inherited attribute predicateName::Maybe<String>;
inherited attribute refVariables::[Name];
inherited attribute lastGoalCond::[[String]];
monoid attribute goalCondParams::[String] with [], union;
synthesized attribute usesContinuation::Boolean;
inherited attribute tailCallPermitted::Boolean;
monoid attribute containsCut::Boolean with false, ||;

synthesized attribute continuationTransform::Expr;
inherited attribute continuationTransformIn::Expr;

tracked nonterminal Goals with pps, env, predicateName, refVariables, lastGoalCond, tailCallPermitted, errors, defs, freeVariables, goalCondParams, containsCut, transform<Expr>, continuationTransform, continuationTransformIn;
flowtype Goals = decorate {env, predicateName, refVariables, lastGoalCond, tailCallPermitted, continuationTransformIn}, pps {}, errors {refVariables, env}, defs {env}, freeVariables {env}, containsCut {env}, goalCondParams {decorate}, transform {decorate}, continuationTransform {decorate};

propagate predicateName, refVariables, errors, defs, goalCondParams, containsCut on Goals;

abstract production consGoal
top::Goals ::= h::Goal t::Goals
{
  top.pps = h.pp :: t.pps;
  top.freeVariables := h.freeVariables ++ removeDefsFromNames(h.defs, t.freeVariables);
  
  h.env = top.env;
  t.env = addEnv(h.defs, h.env);
  
  h.lastGoalCond = if top.tailCallPermitted then top.lastGoalCond else [[]];
  t.lastGoalCond =
    case h of
    | cutGoal() -> []
    | _ -> top.lastGoalCond
    end;
  t.tailCallPermitted = top.tailCallPermitted && !h.usesContinuation;
  
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

tracked nonterminal Goal with env, predicateName, refVariables, lastGoalCond, pp, errors, defs, freeVariables, usesContinuation, goalCondParams, containsCut, transform<Expr>, transformIn<Expr>, continuationTransformIn;
flowtype Goal = decorate {env, predicateName, refVariables, lastGoalCond, transformIn, continuationTransformIn}, pp {}, errors {refVariables, env}, defs {env}, freeVariables {env}, usesContinuation {env}, containsCut {env}, goalCondParams {decorate}, transform {decorate};

propagate errors, defs on Goal excluding inferredPredicateGoal;
propagate goalCondParams, containsCut on Goal excluding notGoal;
propagate predicateName, refVariables, freeVariables on Goal;

aspect default production
top::Goal ::=
{
  top.usesContinuation = false;
}

abstract production predicateGoal
top::Goal ::= n::Name ts::TemplateArgNames les::LogicExprs
{
  top.pp = pp"${n.pp}<${ppImplode(pp", ", ts.pps)}>(${ppImplode(pp", ", les.pps)})";
  top.usesContinuation = true;
  
  local tailCallTrans::Expr =
    ableC_Expr {
      ({$Stmt{params.tailCallTrans}
        _continuation = $Expr{top.continuationTransformIn};
        goto _pred_start;
        0;})
    };
  local regularTrans::Expr =
    ableC_Expr {
      inst $name{s"_predicate_${n.name}"}<$TemplateArgNames{ts}>(
        $Exprs{les.transform}, _trail, $Expr{top.continuationTransformIn})
    };
  top.transform =
    case top.predicateName of
    | just(n1) when n1 == n.name ->
      case top.lastGoalCond of
      | [] -> tailCallTrans
      | [[]] -> regularTrans
      | lgc ->
        conditionalExpr(
          foldr1(
            andExpr,
            map(
              foldr1(orExpr, _),
              map(
                map(\ p::String -> ableC_Expr { $name{s"_${p}_bound"} }, _),
                lgc))),
          tailCallTrans, regularTrans)
      end
    | _ -> regularTrans
    end;
  top.goalCondParams <-
    case top.predicateName of
    | just(n1) when n1 == n.name -> unions(top.lastGoalCond)
    | _ -> []
    end;
  
  n.env = top.env;

  local templateParams::TemplateParameters = n.predicateItem.templateParams;
  
  ts.env = top.env;
  ts.edu:umn:cs:melt:exts:ableC:templating:abstractsyntax:paramNames = templateParams.names;
  ts.paramKinds = templateParams.kinds;
  ts.substEnv = s:fail();
  
  local params::Parameters = s:rewriteWith(topDownSubs(ts.substDefs), n.predicateItem.params).fromJust;
  -- NOT the env at the declaration site, but this is equivalent (and more efficient.)
  params.env = openScopeEnv(globalEnv(addEnv(ts.defs, ts.env)));
  params.controlStmtContext = initialControlStmtContext;
  params.position = 0;
  params.tailCallArgs = les.transform;
  
  top.defs <- foldr(consDefs, nilDefs(), params.defs).canonicalDefs;
  
  les.env = addEnv(ts.defs ++ params.defs, ts.env);
  les.expectedTypes = map(\ t::Type -> t.canonicalType, params.typereps);
  les.allowUnificationTypes = false;
  les.allocator = ableC_Expr { alloca };
  
  top.errors <- n.predicateLookupCheck;
  top.errors <-
    if null(n.predicateLookupCheck) && ts.count != templateParams.count
    then [errFromOrigin(n, s"Wrong number of type arguments for ${n.name}, " ++
            s"expected ${toString(templateParams.count)} but got ${toString(ts.count)}")]
    else [];
  top.errors <-
    if null(n.predicateLookupCheck) && les.count != params.count
    then [errFromOrigin(top, s"Wrong number of arguments to predicate ${n.name} (expected ${toString(params.count)}, got ${toString(les.count)})")]
    else [];
  top.errors <- ts.argreps.templateArgUnifyErrors(n.location, top.env);
}

abstract production inferredPredicateGoal
top::Goal ::= n::Name les::LogicExprs
{
  propagate env;

  top.pp = pp"${n.pp}(${ppImplode(pp", ", les.pps)})";
  top.usesContinuation = true;
  top.errors :=
    case inferredTemplateArguments of
    | just(ts) when !ts.containsErrorType -> les.errors
    | _ -> []
    end;
  top.defs :=
    if inferredTemplateArguments.isJust
    then les.defs
    else [];
  
  local tailCallTrans::Expr =
    ableC_Expr {
      ({$Stmt{params.tailCallTrans}
        _continuation = $Expr{top.continuationTransformIn};
        goto _pred_start;
        0;})
    };
  local regularTrans::Expr =
    ableC_Expr {
      inst $name{s"_predicate_${n.name}"}<$TemplateArgNames{ts.argNames}>(
        $Exprs{les.transform}, _trail, $Expr{top.continuationTransformIn})
    };
  top.transform =
    case top.predicateName of
    | just(n1) when n1 == n.name ->
      case top.lastGoalCond of
      | [] -> tailCallTrans
      | [[]] -> regularTrans
      | lgc ->
        conditionalExpr(
          foldr1(
            andExpr,
            map(
              foldr1(orExpr, _),
              map(
                map(\ p::String -> ableC_Expr { $name{s"_${p}_bound"} }, _),
                lgc))),
          tailCallTrans, regularTrans)
      end
    | _ -> regularTrans
    end;
  top.goalCondParams <-
    case top.predicateName of
    | just(n1) when n1 == n.name -> unions(top.lastGoalCond)
    | _ -> []
    end;
  
  local templateParams::TemplateParameters = n.predicateItem.templateParams;
  templateParams.templateParamEnv = globalEnv(top.env);
  
  -- Decorate parameters the first time for template parameter inference...
  local infParams::Parameters = n.predicateItem.params;
  -- NOT the env at the declaration site, but this is equivalent (and more efficient.)
  infParams.env = openScopeEnv(globalEnv(top.env));
  infParams.controlStmtContext = initialControlStmtContext;
  infParams.position = 0;
  infParams.partialArgumentTypes = les.maybeTypereps;
  
  local inferredTemplateArguments::Maybe<TemplateArgs> =
    map(
      foldr(consTemplateArg, nilTemplateArg(), _),
      traverseA(lookup(_, infParams.partialInferredArgs), templateParams.names));
  
  local ts::TemplateArgs = inferredTemplateArguments.fromJust;
  ts.edu:umn:cs:melt:exts:ableC:templating:abstractsyntax:paramNames = templateParams.names;
  
  -- ... then re-decorate the substituted parameters to compute the expected types.
  local params::Parameters = s:rewriteWith(topDownSubs(ts.substDefs), n.predicateItem.params).fromJust;
  -- NOT the env at the declaration site, but this is equivalent (and more efficient.)
  params.env = openScopeEnv(globalEnv(top.env));
  params.controlStmtContext = initialControlStmtContext;
  params.position = 0;
  params.tailCallArgs = les.transform;
  
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
      [errFromOrigin(top, s"Type argument inference failed for ${n.name}(${
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
    then [errFromOrigin(top, s"Wrong number of arguments to predicate ${n.name} (expected ${toString(infParams.count)}, got ${toString(les.count)})")]
    else [];
  top.errors <-
    case inferredTemplateArguments of
    | just(ts) -> ts.templateArgUnifyErrors(top.env)
    | nothing() -> []
    end;
}

abstract production isGoal
top::Goal ::= le::LogicExpr e::Expr
{
  top.pp = pp"(${le.pp}) is (${e.pp})";
  top.transform =
    ableC_Expr {
      $Expr{
        unifyExpr(
          le.transform,
          ableC_Expr {
            ({$Stmt{makeUnwrappedVarDecls(e.freeVariables, top.env)}
              $Expr{decExpr(e)};})
          },
          justExpr(ableC_Expr { _trail }))} &&
      $Expr{top.transformIn}
    };

  le.env = top.env;
  le.expectedType = e.typerep;
  le.allowUnificationTypes = true;
  le.allocator = ableC_Expr { alloca };
  -- Don't add le.defs to e's env here, since decorating le requires e's typerep
  e.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  e.controlStmtContext = initialControlStmtContext;
}

abstract production equalsGoal
top::Goal ::= le1::LogicExpr le2::LogicExpr
{
  top.pp = pp"(${le1.pp}) = (${le2.pp})";
  top.transform =
    ableC_Expr {
      $Expr{
        unifyExpr(
          le1.transform,
          le2.transform,
          justExpr(ableC_Expr { _trail }))} &&
      $Expr{top.transformIn}
    };
  
  top.errors <-
    if !le1.maybeTyperep.isJust
    then [errFromOrigin(le1, "Could not infer a type for lhs of goal")]
    else [];
  
  local expectedType::Type = fromMaybe(errorType(), le1.maybeTyperep);
  le1.expectedType = expectedType;
  le1.allowUnificationTypes = true;
  le1.allocator = ableC_Expr { alloca };
  le1.env = top.env;
  le2.expectedType = expectedType;
  le2.allowUnificationTypes = true;
  le2.allocator = ableC_Expr { alloca };
  le2.env = addEnv(le1.defs, le1.env);
}

abstract production notEqualsGoal
top::Goal ::= le1::LogicExpr le2::LogicExpr
{
  top.pp = pp"(${le1.pp}) \= (${le2.pp})";
  
  forwards to notGoal(equalsGoal(le1, le2));
}

abstract production eqGoal
top::Goal ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp}) =:= (${e2.pp})";
  top.transform =
    ableC_Expr {
      ({$Stmt{makeUnwrappedVarDecls(e1.freeVariables ++ e2.freeVariables, top.env)}
        $Expr{decExpr(e1)} == $Expr{decExpr(e2)};}) &&
        $Expr{top.transformIn}
    };
  
  -- TODO: Types should both be equality types
  top.errors <-
    if compatibleTypes(e1.typerep, e2.typerep, true, true)
    then []
    else [errFromOrigin(top, s"Types to =:= goal must match (got ${showType(e1.typerep)}, ${showType(e2.typerep)})")];
  
  e1.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  e1.controlStmtContext = initialControlStmtContext;
  e2.env = addEnv(e1.defs, e1.env);
  e2.controlStmtContext = initialControlStmtContext;
}

abstract production neqGoal
top::Goal ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp}) =\= (${e2.pp})";
  top.transform =
    ableC_Expr {
      ({$Stmt{makeUnwrappedVarDecls(e1.freeVariables ++ e2.freeVariables, top.env)}
        $Expr{decExpr(e1)} != $Expr{decExpr(e2)};}) &&
        $Expr{top.transformIn}
    };
  
  -- TODO: Types should both be equality types
  top.errors <-
    if compatibleTypes(e1.typerep, e2.typerep, true, true)
    then []
    else [errFromOrigin(top, s"Types to =/= goal must match (got ${showType(e1.typerep)}, ${showType(e2.typerep)})")];
  
  e1.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  e1.controlStmtContext = initialControlStmtContext;
  e2.env = addEnv(e1.defs, e1.env);
  e2.controlStmtContext = initialControlStmtContext;
}

abstract production ltGoal
top::Goal ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp}) < (${e2.pp})";
  top.transform =
    ableC_Expr {
      ({$Stmt{makeUnwrappedVarDecls(e1.freeVariables ++ e2.freeVariables, top.env)}
        $Expr{decExpr(e1)} < $Expr{decExpr(e2)};}) &&
        $Expr{top.transformIn}
    };
  
  -- TODO: Types should both be comparison types
  top.errors <-
    if compatibleTypes(e1.typerep, e2.typerep, true, true)
    then []
    else [errFromOrigin(top, s"Types to < goal must match (got ${showType(e1.typerep)}, ${showType(e2.typerep)})")];
  
  e1.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  e1.controlStmtContext = initialControlStmtContext;
  e2.env = addEnv(e1.defs, e1.env);
  e2.controlStmtContext = initialControlStmtContext;
}

abstract production eltGoal
top::Goal ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp}) =< (${e2.pp})";
  top.transform =
    ableC_Expr {
      ({$Stmt{makeUnwrappedVarDecls(e1.freeVariables ++ e2.freeVariables, top.env)}
        $Expr{decExpr(e1)} <= $Expr{decExpr(e2)};}) &&
        $Expr{top.transformIn}
    };
  
  -- TODO: Types should both be comparison types
  top.errors <-
    if compatibleTypes(e1.typerep, e2.typerep, true, true)
    then []
    else [errFromOrigin(top, s"Types to =< goal must match (got ${showType(e1.typerep)}, ${showType(e2.typerep)})")];
  
  e1.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  e1.controlStmtContext = initialControlStmtContext;
  e2.env = addEnv(e1.defs, e1.env);
  e2.controlStmtContext = initialControlStmtContext;
}

abstract production gtGoal
top::Goal ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp}) > (${e2.pp})";
  top.transform =
    ableC_Expr {
      ({$Stmt{makeUnwrappedVarDecls(e1.freeVariables ++ e2.freeVariables, top.env)}
        $Expr{decExpr(e1)} > $Expr{decExpr(e2)};}) &&
        $Expr{top.transformIn}
    };
  
  -- TODO: Types should both be comparison types
  top.errors <-
    if compatibleTypes(e1.typerep, e2.typerep, true, true)
    then []
    else [errFromOrigin(top, s"Types to > goal must match (got ${showType(e1.typerep)}, ${showType(e2.typerep)})")];
  
  e1.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  e1.controlStmtContext = initialControlStmtContext;
  e2.env = addEnv(e1.defs, e1.env);
  e2.controlStmtContext = initialControlStmtContext;
}

abstract production gteGoal
top::Goal ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp}) >= (${e2.pp})";
  top.transform =
    ableC_Expr {
      ({$Stmt{makeUnwrappedVarDecls(e1.freeVariables ++ e2.freeVariables, top.env)}
        $Expr{decExpr(e1)} >= $Expr{decExpr(e2)};}) &&
        $Expr{top.transformIn}
    };
  
  -- TODO: Types should both be comparison types
  top.errors <-
    if compatibleTypes(e1.typerep, e2.typerep, true, true)
    then []
    else [errFromOrigin(top, s"Types to >= goal must match (got ${showType(e1.typerep)}, ${showType(e2.typerep)})")];
  
  e1.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  e1.controlStmtContext = initialControlStmtContext;
  e2.env = addEnv(e1.defs, e1.env);
  e2.controlStmtContext = initialControlStmtContext;
}

abstract production notGoal
top::Goal ::= g::Goal
{
  propagate env;
  top.pp = pp"\+ (${g.pp})";
  top.goalCondParams := [];
  top.containsCut := false;
  top.errors <-
    if g.containsCut
    then [errFromOrigin(g, "Cuts are not permitted within \\+")]
    else [];
  
  g.transformIn = ableC_Expr { (_Bool)1 };
  g.continuationTransformIn = ableC_Expr { lambda allocate(alloca) () -> (_Bool)1 };
  g.lastGoalCond = [[]];
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
  top.pp = pp"!";
  top.containsCut <- true;
  top.transform =
    ableC_Expr {
      // If a failure occurs, longjmp out of all continuations back to the current
      // predicate function, which fails immediately.  This is OK because all data
      // is stack-allocated.
      $Expr{top.transformIn} ||
      (undo_trail(_trail, _initial_trail_index), longjmp(_cut_buffer, 1), 1)
    };
}

abstract production initiallyGoal
top::Goal ::= s::Stmt
{
  top.pp = pp"initially ${braces(nestlines(2, s.pp))})";
  top.transform =
    ableC_Expr {
      ({{$Stmt{makeUnwrappedVarDecls(s.freeVariables, top.env)}
         $Stmt{decStmt(s)}}
        $Expr{top.transformIn};})
    };
  
  s.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  s.controlStmtContext = initialControlStmtContext;
}

abstract production finallyGoal
top::Goal ::= s::Stmt
{
  top.pp = pp"finally ${braces(nestlines(2, s.pp))})";
  top.transform =
    ableC_Expr {
      ({{$Stmt{makeUnwrappedVarDecls(s.freeVariables, top.env)}
         push_action(_trail, lambda allocate(malloc) (void) -> void { $Stmt{decStmt(s)} }, free);}
        $Expr{top.transformIn};})
    };
  
  s.env = addEnv(makeUnwrappedVarDefs(top.env), top.env);
  s.controlStmtContext = initialControlStmtContext;
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
        nub(freeVariables)));
}
