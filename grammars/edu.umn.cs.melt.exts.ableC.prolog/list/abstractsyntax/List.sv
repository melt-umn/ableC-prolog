grammar edu:umn:cs:melt:exts:ableC:prolog:list:abstractsyntax;

abstract production constructList
top::Expr ::= sub::TypeName allocate::Expr init::ListInitializers
{
  propagate controlStmtContext;
  top.pp = pp"newlist<${sub.pp}>(${allocate.pp})[${ppImplode(pp", ", init.pps)}]";
  
  local localErrors::[Message] =
    sub.errors ++ allocate.errors ++ init.errors ++
    decorate sub.typerep with {otherType = sub.typerep;}.unifyErrors(top.location, top.env) ++
    checkListHeaderDef("_list_d", top.location, top.env);
  
  sub.env = globalEnv(top.env);
  allocate.env = sub.env;
  init.env = addEnv(sub.defs, top.env);
  init.maybeParamType = just(sub.typerep);
  init.allocator = allocate;
  
  local fwrd::Expr = init.host;
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production inferredConstructList
top::Expr ::= allocate::Expr init::ListInitializers
{
  propagate env, controlStmtContext;
  top.pp = pp"newlist(${allocate.pp})[${ppImplode(pp", ", init.pps)}]";
  
  local localErrors::[Message] =
    allocate.errors ++ init.errors ++
    checkListHeaderDef("_list_d", top.location, top.env);
  
  init.maybeParamType = nothing();
  init.allocator = allocate;
  
  local fwrd::Expr = init.host;
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

inherited attribute maybeParamType::Maybe<Type>;

nonterminal ListInitializers with pps, env, maybeParamType, allocator, 
  errors, host<Expr>, controlStmtContext;

propagate allocator, controlStmtContext, errors on ListInitializers;

abstract production consListInitializer
top::ListInitializers ::= h::Expr t::ListInitializers
{
  top.pps = h.pp :: t.pps;
  
  t.maybeParamType = just(fromMaybe(h.typerep, top.maybeParamType));
  
  local cons::Expr = 
    ableC_Expr {
      inst cons<$directTypeExpr{t.maybeParamType.fromJust}>
    };
  cons.env = top.env;
  cons.controlStmtContext = initialControlStmtContext;
  
  -- Avoid rececorating h unless we are using it to infer the parameter type
  h.env = if top.maybeParamType.isJust then addEnv(cons.defs, cons.env) else top.env;
  t.env = addEnv((if top.maybeParamType.isJust then [] else cons.defs) ++ h.defs, h.env);
  top.host =
    ableC_Expr {
      $Expr{decExpr(cons, location=builtin)}(
        $Expr{top.allocator},
        $Expr{if top.maybeParamType.isJust then decExpr(h, location=builtin) else h},
        $Expr{t.host})
    };
  
  top.errors <-
    case top.maybeParamType of
    | just(t) ->
      if !typeAssignableTo(t, h.typerep)
      then [err(h.location, s"Invalid type in list initializer: Expected ${showType(t)}, got ${showType(h.typerep)}")]
      else []
    | nothing() -> decorate h.typerep with {otherType = h.typerep;}.unifyErrors(h.location, t.env)
    end;
}

abstract production tailListInitializer
top::ListInitializers ::= e::Expr
{
  propagate env;
  top.pps = [pp"| ${e.pp}"]; -- TODO: Fix this
  top.host = decExpr(e, location=builtin);
  
  top.errors <-
    if !typeAssignableTo(extType(nilQualifier(), varType(extType(nilQualifier(), listType(top.maybeParamType.fromJust)))), e.typerep)
    then [err(e.location, s"Invalid type in list initializer tail: Expected list<${showType(top.maybeParamType.fromJust)}> ?, got ${showType(e.typerep)}")]
    else [];
}

abstract production nilListInitializer
top::ListInitializers ::= loc::Location
{
  top.pps = [];
  top.errors <-
    if top.maybeParamType.isJust
    then []
    else [err(loc, "Can't infer type argument for empty list")];
  top.host =
    ableC_Expr {
      inst nil<$directTypeExpr{top.maybeParamType.fromJust}>($Expr{top.allocator})
    };
}

abstract production listUnifyExpr
top::Expr ::= e1::Expr e2::Expr trail::Expr
{
  propagate env, controlStmtContext;
  top.pp = pp"unifyList(${e1.pp}, ${e2.pp}, ${trail.pp})";
  
  local subType::Type = listSubType(e1.typerep);
  forwards to
    ableC_Expr {
      inst unify_list<$directTypeExpr{subType}>($Expr{e1}, $Expr{e2}, $Expr{trail})
    };
}

inherited attribute paramType::Type;

abstract production listLogicExpr
top::LogicExpr ::= l::ListLogicExprs
{
  propagate env, allocator, allowUnificationTypes, refVariables, errors, defs;
  top.pp = pp"[${ppImplode(pp", ", l.pps)}]";
  top.maybeTyperep =
    case l.maybeTyperep of
    | just(t) -> just(extType(nilQualifier(), listType(t)))
    | nothing() -> nothing()
    end;
  top.transform = l.transform;
  
  local baseType::Type =
    case top.expectedType of
    | extType(_, varType(sub)) -> sub
    | t -> t
    end;
  l.paramType = listSubType(baseType);
  l.expectedType = top.expectedType;
  
  local expectedType::Type = top.expectedType;
  expectedType.otherType = extType(nilQualifier(), listType(l.paramType));
  top.errors <- expectedType.unifyErrors(top.location, top.env);

  top.isExcludable =
    case l, decorate top.isExcludableBy with {env = top.env;} of
    | consListLogicExpr(_, _), listLogicExpr(nilListLogicExpr()) ->
      case top.expectedType of
      | extType(_, varType(_)) -> [[top.paramNameIn]]
      | _ -> []
      end
    | nilListLogicExpr(), listLogicExpr(consListLogicExpr(_, _)) ->
      case top.expectedType of
      | extType(_, varType(_)) -> [[top.paramNameIn]]
      | _ -> []
      end
    | _, _ -> [[]]
    end;
}

nonterminal ListLogicExprs with pps, env, paramType, edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax:expectedType, allowUnificationTypes, allocator, refVariables, errors, defs, maybeTyperep, edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax:transform<Expr>;
flowtype ListLogicExprs = decorate {env, paramType, expectedType, allowUnificationTypes, allocator, refVariables}, pps {}, errors {decorate}, defs {env, paramType, expectedType, allowUnificationTypes}, maybeTyperep {env, allowUnificationTypes}, transform {decorate};

propagate paramType, allocator, refVariables, errors, defs on ListLogicExprs;

abstract production consListLogicExpr
top::ListLogicExprs ::= h::LogicExpr t::ListLogicExprs
{
  top.pps = h.pp :: t.pps;
  top.maybeTyperep = h.maybeTyperep; -- Only look at first elemet to avoid a dependency cycle
  top.transform =
    makeVarExpr(
      top.allocator,
      top.allowUnificationTypes,
      top.expectedType,
      ableC_Expr {
        ($BaseTypeExpr{
           listTypeExpr(
             nilQualifier(),
             typeName(directTypeExpr(top.paramType), baseTypeExpr()),
             builtin)})
          inst _Cons<$directTypeExpr{top.paramType}>($Expr{h.transform}, $Expr{t.transform})
      });
  
  h.env = top.env;
  h.expectedType = top.paramType;
  h.allowUnificationTypes = false;
  t.env = addEnv(h.defs, h.env);
  t.expectedType =
    extType(nilQualifier(), varType(extType(nilQualifier(), listType(top.paramType))));
  t.allowUnificationTypes = false;
}

abstract production tailListLogicExpr
top::ListLogicExprs ::= e::LogicExpr
{
  propagate env;
  top.pps = [pp"| ${e.pp}"]; -- TODO: Fix this
  top.maybeTyperep = e.maybeTyperep;
  top.transform = e.transform;
  
  e.expectedType = top.expectedType;
  e.allowUnificationTypes = top.allowUnificationTypes;
}

abstract production nilListLogicExpr
top::ListLogicExprs ::=
{
  top.pps = [];
  top.maybeTyperep = nothing();
  top.transform =
    makeVarExpr(
      top.allocator,
      top.allowUnificationTypes,
      top.expectedType,
      ableC_Expr {
        ($BaseTypeExpr{
           listTypeExpr(
             nilQualifier(),
             typeName(directTypeExpr(top.paramType), baseTypeExpr()),
             builtin)})
          inst _Nil<$directTypeExpr{top.paramType}>()
      });
}

abstract production listPattern
top::Pattern ::= l::ListPatterns
{
  propagate initialEnv, errors;
  top.pp = pp"[${ppImplode(pp", ", l.pps)}]";
  top.patternDecls = @l.patternDecls;
  top.transform = @l.transform;
  
  l.expectedType = listSubType(top.expectedType);
  l.transformIn = error("Shouldn't be used");
  l.isBoundTransformIn = ableC_Expr { 1 };
  l.valueTransformIn = top.transformIn;
  
  top.errors <-
    case top.expectedType of
    | extType(_, listType(_)) -> []
    | errorType() -> []
    | _ -> [err(top.location, s"List pattern expected to match a list (got ${showType(top.expectedType)})")]
    end;
}

inherited attribute isBoundTransformIn::Expr;
inherited attribute valueTransformIn::Expr;

nonterminal ListPatterns with pps, errors, initialEnv,
  edu:umn:cs:melt:exts:ableC:algebraicDataTypes:patternmatching:abstractsyntax:expectedType,
  patternDecls,
  edu:umn:cs:melt:exts:ableC:algebraicDataTypes:patternmatching:abstractsyntax:transform<Expr>,
  transformIn<Expr>, isBoundTransformIn, valueTransformIn;

propagate initialEnv, errors on ListPatterns;

abstract production consListPattern
top::ListPatterns ::= h::Pattern t::ListPatterns
{
  top.pps = h.pp :: t.pps;
  
  h.expectedType = top.expectedType;
  t.expectedType = top.expectedType;

  top.patternDecls = consDecl(decls(@h.patternDecls), @t.patternDecls);

  local tmpName::String = "_tmp_list_" ++ toString(genInt());
  top.transform =
    ableC_Expr {
      $Expr{top.isBoundTransformIn} &&
      ({proto_typedef _list_d;
        inst _list_d<$directTypeExpr{top.expectedType}> $name{tmpName} =
          (inst _list_d<$directTypeExpr{top.expectedType}>)$Expr{top.valueTransformIn};
        $name{tmpName}.tag == _list_d__Cons &&
        $Expr{@h.transform} && $Expr{@t.transform};})
    };
  h.transformIn =
    ableC_Expr {
      proto_typedef _list_d;
      $name{tmpName}.contents._Cons.head
    };
  t.transformIn =
    ableC_Expr {
      proto_typedef _list_d;
      $name{tmpName}.contents._Cons.tail
    };
  t.isBoundTransformIn =
    ableC_Expr {
      ({template<typename a> _Bool is_bound();
        is_bound($Expr{t.transformIn});})
    };
  t.valueTransformIn =
    ableC_Expr {
      ({template<typename a> a value();
        value($Expr{t.transformIn});})
    };
}

abstract production tailListPattern
top::ListPatterns ::= p::Pattern
{
  propagate env;
  top.pps = [pp"| ${p.pp}"]; -- TODO: Fix this
  top.patternDecls = @p.patternDecls;
  top.transform = @p.transform;
  
  p.expectedType = extType(nilQualifier(), varType(extType(nilQualifier(), listType(top.expectedType))));
  p.transformIn = top.transformIn;
}

abstract production nilListPattern
top::ListPatterns ::=
{
  top.pps = [];

  top.patternDecls = nilDecl();
  top.transform =
    ableC_Expr {
      proto_typedef _list_d;
      $Expr{top.isBoundTransformIn} &&
      ((inst _list_d<$directTypeExpr{top.expectedType}>)$Expr{top.valueTransformIn}).tag == _list_d__Nil
    };
}

-- Check the given env for the given template name
function checkListHeaderDef
[Message] ::= n::String loc::Location env::Decorated Env
{
  return
    if !null(lookupTemplate(n, env))
    then []
    else [err(loc, "Missing include of list.xh")];
}

-- Check that operand has list type
function checkListType
[Message] ::= sub::Type t::Type op::String loc::Location
{
  return
    if typeAssignableTo(extType(nilQualifier(), listType(sub)), t)
    then []
    else [err(loc, s"Operand to ${op} expected list<${showType(sub)}> (got ${showType(t)})")];
}
