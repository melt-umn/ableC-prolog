grammar edu:umn:cs:melt:exts:ableC:prolog:list:abstractsyntax;

abstract production constructList
top::Expr ::= sub::TypeName init::ListInitializers
{
  propagate controlStmtContext;
  top.pp = pp"newlist<${sub.pp}>[${ppImplode(pp", ", init.pps)}]";

  local localErrors::[Message] =
    sub.errors ++ init.errors ++
    decorate sub.typerep with {otherType = sub.typerep;}.unifyErrors(top.env) ++
    checkListHeaderDef(top.env);

  init.maybeParamType = just(sub.typerep);

  forward fwrd = letExpr(consDecl(typePreDecls(@sub), nilDecl()), @init.listTrans);

  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

abstract production inferredConstructList
top::Expr ::= init::ListInitializers
{
  top.pp = pp"newlist[${ppImplode(pp", ", init.pps)}]";

  local localErrors::[Message] =
    init.errors ++ checkListHeaderDef(top.env);
  
  init.maybeParamType = nothing();

  forward fwrd = @init.listTrans;

  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

inherited attribute maybeParamType::Maybe<Type>;
translation attribute listTrans::Expr;

tracked nonterminal ListInitializers with pps, maybeParamType,
  errors, listTrans;

propagate errors on ListInitializers;

abstract production consListInitializer
top::ListInitializers ::= h::Expr t::ListInitializers
{
  top.pps = h.pp :: t.pps;

  nondecorated local paramType::Type = fromMaybe(h.typerep, top.maybeParamType);
  t.maybeParamType = just(paramType);

  top.listTrans = letExpr(
    consDecl(bindExprDecl(freshName("l"), @h), nilDecl()),
    boundVarExpr(
      extType(nilQualifier(), listType(paramType)),
      ableC_Expr {
        ($directTypeExpr{extType(nilQualifier(), listType(paramType))})
          inst _Cons<$directTypeExpr{paramType}>($Expr{h.bindRefExpr}, $Expr{@t.listTrans})
      }));

  top.errors <-
    case top.maybeParamType of
    | just(t) ->
      if !typeAssignableTo(t, h.typerep)
      then [errFromOrigin(h, s"Invalid type in list initializer: Expected ${show(80, t)}, got ${show(80, h.typerep)}")]
      else []
    | nothing() -> decorate h.typerep with {otherType = h.typerep;}.unifyErrors(t.listTrans.env)
    end;
}

abstract production tailListInitializer
top::ListInitializers ::= e::Expr
{
  top.pps = [pp"| ${e.pp}"]; -- TODO: Fix this
  top.listTrans = @e;
  
  top.errors <-
    if !typeAssignableTo(extType(nilQualifier(), varType(extType(nilQualifier(), listType(top.maybeParamType.fromJust)))), e.typerep)
    then [errFromOrigin(e, s"Invalid type in list initializer tail: Expected list<${show(80, top.maybeParamType.fromJust)}> ?, got ${show(80, e.typerep)}")]
    else [];
}

abstract production nilListInitializer
top::ListInitializers ::=
{
  top.pps = [];

  nondecorated local paramType::Type = top.maybeParamType.fromJust;
  top.listTrans = boundVarExpr(
    extType(nilQualifier(), listType(paramType)),
    ableC_Expr {
      ($directTypeExpr{extType(nilQualifier(), listType(paramType))})
        inst _Nil<$directTypeExpr{paramType}>()
    });

  top.errors <-
    if top.maybeParamType.isJust
    then []
    else [errFromOrigin(top, "Can't infer type argument for empty list")];
}

abstract production listUnifyExpr implements Unify
top::Expr ::= e1::Expr e2::Expr trail::Expr paramType::Type
{
  top.pp = pp"unifyList(${e1.pp}, ${e2.pp}, ${trail.pp}, ${paramType.lpp}${paramType.rpp})";

  forwards to customTemplateUnifyExpr(@e1, @e2, @trail,
    name("unify_list"), ^paramType);
}

inherited attribute paramType::Type;

abstract production listLogicExpr
top::LogicExpr ::= l::ListLogicExprs
{
  propagate env, allowUnificationTypes, refVariables, errors, defs;
  top.pp = pp"[${ppImplode(pp", ", l.pps)}]";
  top.maybeTyperep =
    case l.maybeTyperep of
    | just(t) -> just(extType(nilQualifier(), listType(t)))
    | nothing() -> nothing()
    end;
  top.transform = l.transform;
  
  nondecorated local baseType::Type =
    case top.expectedType of
    | extType(_, varType(sub)) -> ^sub
    | t -> t
    end;
  l.paramType = listSubType(baseType);
  l.expectedType = top.expectedType;
  
  local expectedType::Type = top.expectedType;
  expectedType.otherType = extType(nilQualifier(), listType(l.paramType));
  top.errors <- expectedType.unifyErrors(top.env);

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

tracked nonterminal ListLogicExprs with
  pps, env, paramType, edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax:expectedType,
  allowUnificationTypes, refVariables, errors, defs, maybeTyperep,
  edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax:transform<Expr>;
flowtype ListLogicExprs =
  decorate {env, paramType, expectedType, allowUnificationTypes, refVariables},
  pps {}, errors {decorate}, defs {env, paramType, expectedType, allowUnificationTypes},
  maybeTyperep {env, allowUnificationTypes}, transform {decorate};

propagate paramType, refVariables, errors, defs on ListLogicExprs;

abstract production consListLogicExpr
top::ListLogicExprs ::= h::LogicExpr t::ListLogicExprs
{
  top.pps = h.pp :: t.pps;
  top.maybeTyperep = h.maybeTyperep; -- Only look at first elemet to avoid a dependency cycle
  top.transform =
    makeVarExpr(
      top.allowUnificationTypes,
      top.expectedType,
      ableC_Expr {
        ($BaseTypeExpr{
           listTypeExpr(
             nilQualifier(),
             typeName(directTypeExpr(top.paramType), baseTypeExpr()))})
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
      top.allowUnificationTypes,
      top.expectedType,
      ableC_Expr {
        ($BaseTypeExpr{
           listTypeExpr(
             nilQualifier(),
             typeName(directTypeExpr(top.paramType), baseTypeExpr()))})
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
    | _ -> [errFromOrigin(top, s"List pattern expected to match a list (got ${show(80, top.expectedType)})")]
    end;
}

inherited attribute isBoundTransformIn::Expr;
inherited attribute valueTransformIn::Expr;

tracked nonterminal ListPatterns with pps, errors, initialEnv,
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
fun checkListHeaderDef [Message] ::= env::Env =
  if !null(lookupTemplate("_list_d", env))
  then []
  else [errFromOrigin(ambientOrigin(), "Missing include of list.xh")];

-- Check that operand has list type
fun checkListType [Message] ::= sub::Type t::Type op::String =
  if typeAssignableTo(extType(nilQualifier(), listType(sub)), t)
  then []
  else [errFromOrigin(ambientOrigin(), s"Operand to ${op} expected list<${show(80, sub)}> (got ${show(80, t)})")];
