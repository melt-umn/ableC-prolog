grammar edu:umn:cs:melt:exts:ableC:prolog:list:abstractsyntax;

abstract production constructList
top::Expr ::= sub::TypeName allocate::Expr init::ListInitializers
{
  propagate substituted;
  top.pp = pp"newlist<${sub.pp}>(${allocate.pp})[${ppImplode(pp", ", init.pps)}]";
  
  local localErrors::[Message] =
    sub.errors ++ allocate.errors ++ init.errors ++
    decorate sub.typerep with {otherType = sub.typerep;}.unifyErrors(top.location, top.env) ++
    checkListHeaderDef("_list_d", top.location, top.env);
  
  sub.env = globalEnv(top.env);
  init.env = addEnv(sub.defs, top.env);
  init.maybeParamType = just(sub.typerep);
  init.allocator = allocate;
  
  local fwrd::Expr = init.host;
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production inferredConstructList
top::Expr ::= allocate::Expr init::ListInitializers
{
  propagate substituted;
  top.pp = pp"newlist(${allocate.pp})[${ppImplode(pp", ", init.pps)}]";
  
  local localErrors::[Message] =
    allocate.errors ++ init.errors ++
    checkListHeaderDef("_list_d", top.location, top.env);
  
  init.maybeParamType = nothing();
  init.allocator = allocate;
  
  local fwrd::Expr = init.host;
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

autocopy attribute maybeParamType::Maybe<Type>;

nonterminal ListInitializers with pps, env, returnType, maybeParamType, allocator, errors, host<Expr>, substituted<ListInitializers>, substitutions;

abstract production consListInitializer
top::ListInitializers ::= h::Expr t::ListInitializers
{
  propagate substituted;
  top.pps = h.pp :: t.pps;
  top.errors := h.errors ++ t.errors;
  
  t.maybeParamType = just(fromMaybe(h.typerep, top.maybeParamType));
  
  local cons::Expr = 
    ableC_Expr {
      inst cons<$directTypeExpr{t.maybeParamType.fromJust}>
    };
  cons.env = top.env;
  cons.returnType = nothing();
  
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
  propagate substituted;
  top.pps = [pp"| ${e.pp}"]; -- TODO: Fix this
  top.errors := e.errors;
  top.host = decExpr(e, location=builtin);
  
  top.errors <-
    if !typeAssignableTo(extType(nilQualifier(), varType(extType(nilQualifier(), listType(top.maybeParamType.fromJust)))), e.typerep)
    then [err(e.location, s"Invalid type in list initializer tail: Expected list<${showType(top.maybeParamType.fromJust)}> ?, got ${showType(e.typerep)}")]
    else [];
}

abstract production nilListInitializer
top::ListInitializers ::= loc::Location
{
  propagate substituted;
  top.pps = [];
  top.errors :=
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
  propagate substituted;
  top.pp = pp"unifyList(${e1.pp}, ${e2.pp}, ${trail.pp})";
  
  local subType::Type = listSubType(e1.typerep);
  forwards to
    ableC_Expr {
      inst unify_list<$directTypeExpr{subType}>($Expr{e1}, $Expr{e2}, $Expr{trail})
    };
}

autocopy attribute paramType::Type;

abstract production listLogicExpr
top::LogicExpr ::= l::ListLogicExprs
{
  propagate substituted;
  top.pp = pp"[${ppImplode(pp", ", l.pps)}]";
  top.errors := l.errors;
  top.defs := l.defs;
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
}

nonterminal ListLogicExprs with pps, env, paramType, edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax:expectedType, allowUnificationTypes, allocator, errors, defs, maybeTyperep, edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax:transform<Expr>, substituted<ListLogicExprs>, substitutions;
flowtype ListLogicExprs = decorate {env, paramType, expectedType, allowUnificationTypes, allocator}, pps {}, errors {decorate}, defs {decorate}, maybeTyperep {env, allowUnificationTypes}, transform {decorate}, substituted {substitutions};

abstract production consListLogicExpr
top::ListLogicExprs ::= h::LogicExpr t::ListLogicExprs
{
  propagate substituted;
  top.pps = h.pp :: t.pps;
  top.errors := h.errors ++ t.errors;
  top.defs := h.defs ++ t.defs;
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
  propagate substituted;
  top.pps = [pp"| ${e.pp}"]; -- TODO: Fix this
  top.errors := e.errors;
  top.defs := e.defs;
  top.maybeTyperep = e.maybeTyperep;
  top.transform = e.transform;
  
  e.expectedType = top.expectedType;
  e.allowUnificationTypes = top.allowUnificationTypes;
}

abstract production nilListLogicExpr
top::ListLogicExprs ::=
{
  propagate substituted;
  top.pps = [];
  top.errors := [];
  top.defs := [];
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
  propagate substituted;
  top.pp = pp"[${ppImplode(pp", ", l.pps)}]";
  top.errors := l.errors;
  top.defs := l.defs;
  top.decls = l.decls;
  top.patternDefs := l.patternDefs;
  top.transform = l.transform;
  
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

nonterminal ListPatterns with pps, errors, env, returnType, defs, edu:umn:cs:melt:exts:ableC:algebraicDataTypes:patternmatching:abstractsyntax:decls, patternDefs, edu:umn:cs:melt:exts:ableC:algebraicDataTypes:patternmatching:abstractsyntax:expectedType, edu:umn:cs:melt:exts:ableC:algebraicDataTypes:patternmatching:abstractsyntax:transform<Expr>, transformIn<Expr>, isBoundTransformIn, valueTransformIn, substituted<ListPatterns>, substitutions;

abstract production consListPattern
top::ListPatterns ::= h::Pattern t::ListPatterns
{
  propagate substituted;
  top.pps = h.pp :: t.pps;
  top.errors := h.errors ++ t.errors;
  top.defs := h.defs ++ t.defs;
  top.decls = h.decls ++ t.decls;
  top.patternDefs := h.patternDefs ++ t.patternDefs;
  
  h.expectedType = top.expectedType;
  t.expectedType = top.expectedType;
  
  local isBound::Expr = top.isBoundTransformIn;
  isBound.env = top.env;
  isBound.returnType = nothing();
  top.defs <- isBound.defs;
  
  local valueDecl::Stmt =
    ableC_Stmt {
      proto_typedef _list_d;
      inst _list_d<$directTypeExpr{top.expectedType}> $name{tmpName} =
        (inst _list_d<$directTypeExpr{top.expectedType}>)$Expr{top.valueTransformIn};
    };
  valueDecl.env = addEnv(isBound.defs, openScopeEnv(isBound.env));
  valueDecl.returnType = nothing();
  top.defs <- valueDecl.defs;
  
  h.env = addEnv(valueDecl.defs, valueDecl.env);
  t.env = addEnv(h.defs, h.env);
  
  local tmpName::String = "_tmp_list_" ++ toString(genInt());
  top.transform =
    ableC_Expr {
      $Expr{decExpr(isBound, location=builtin)} &&
      ({$Stmt{decStmt(valueDecl)}
        $name{tmpName}.tag == _list_d__Cons &&
        $Expr{h.transform} && $Expr{t.transform};})
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
  propagate substituted;
  top.pps = [pp"| ${p.pp}"]; -- TODO: Fix this
  top.errors := p.errors;
  top.defs := p.defs;
  top.decls = p.decls;
  top.patternDefs := p.patternDefs;
  top.transform = p.transform;
  
  p.expectedType = extType(nilQualifier(), varType(extType(nilQualifier(), listType(top.expectedType))));
  p.transformIn = top.transformIn;
}

abstract production nilListPattern
top::ListPatterns ::=
{
  propagate substituted;
  top.pps = [];
  top.errors := [];
  top.defs := [];
  top.decls = [];
  top.patternDefs := [];
  
  local isBound::Expr = top.isBoundTransformIn;
  isBound.env = top.env;
  isBound.returnType = nothing();
  top.defs <- isBound.defs;
  
  top.transform =
    ableC_Expr {
      proto_typedef _list_d;
      $Expr{decExpr(isBound, location=builtin)} &&
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
