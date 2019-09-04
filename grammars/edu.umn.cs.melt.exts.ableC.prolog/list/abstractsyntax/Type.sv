grammar edu:umn:cs:melt:exts:ableC:prolog:list:abstractsyntax;

import edu:umn:cs:melt:ableC:abstractsyntax:overloadable;

abstract production listTypeExpr 
top::BaseTypeExpr ::= q::Qualifiers sub::TypeName loc::Location
{
  top.pp = pp"${terminate(space(), q.pps)}list<${sub.pp}>";
  
  top.inferredArgs = sub.inferredArgs;
  sub.argumentType =
    case top.argumentType of
    | extType(_, listType(t)) -> t
    | _ -> errorType()
    end;
  
  sub.env = globalEnv(top.env);
  
  local localErrors::[Message] =
    sub.errors ++ checkListHeaderDef("_list_d", loc, top.env);
  
  local globalDecls::Decls =
    foldDecl(
      sub.decls ++
      [templateTypeExprInstDecl(
         q, name("_list_d", location=builtin),
         foldTemplateArg([typeTemplateArg(sub.typerep)]))]);
  
  -- Non-interfering overrides for better performance
  top.decls = [injectGlobalDeclsDecl(globalDecls)];
  top.errors := localErrors;
  top.typerep =
    case sub.typerep of
    | errorType() -> errorType()
    | _ -> extType(q, listType(sub.typerep))
    end;
  
  forwards to
    if !null(localErrors) || case sub.typerep of errorType() -> true | _ -> false end
    then errorTypeExpr(localErrors)
    else injectGlobalDeclsTypeExpr(globalDecls, extTypeExpr(q, listType(sub.typerep)));
}

abstract production listType
top::ExtType ::= sub::Type
{
  propagate canonicalType;
  top.pp = pp"list<${sub.lpp}${sub.rpp}>";
  top.host =
    extType(
      top.givenQualifiers,
      adtExtType(
        "_list_d",
        templateMangledName("_list_d", foldTemplateArg([typeTemplateArg(sub)])),
        templateMangledRefId("_list_d", foldTemplateArg([typeTemplateArg(sub)])))).host;
  top.baseTypeExpr =
    listTypeExpr(top.givenQualifiers, typeName(sub.baseTypeExpr, sub.typeModifierExpr), builtin);
  top.mangledName = s"list_${sub.mangledName}_";
  top.isEqualTo =
    \ other::ExtType ->
      case other of
      | listType(otherSub) -> compatibleTypes(sub, otherSub, false, false)
      | _ -> false
      end;
  
  top.maybeRefId = just(templateMangledRefId("_list_d", foldTemplateArg([typeTemplateArg(sub)])));
  
  top.unifyErrors =
    \ l::Location env::Decorated Env ->
      case top.otherType of
      | extType(_, listType(otherSub)) ->
        if compatibleTypes(sub, otherSub, false, false)
        then decorate sub with {otherType = otherSub;}.unifyErrors(l, env)
        else [err(l, s"Unification list types must match (got ${showType(sub)}, ${showType(otherSub)})")]
      | extType(_, varType(extType(_, listType(otherSub)))) ->
        if compatibleTypes(sub, otherSub, false, false)
        then decorate sub with {otherType = otherSub;}.unifyErrors(l, env)
        else [err(l, s"Unification value and variable list types must match (got ${showType(sub)}, ${showType(otherSub)})")]
      | errorType() -> []
      | t -> [err(l, s"Unification is not defined for list<${showType(sub)}> and non-list ${showType(t)}")]
      end ++
      checkListHeaderDef("unify_list", l, env);
  top.unifyProd =
    case top.otherType of
    | extType(_, listType(_)) -> listUnifyExpr(_, _, _, location=_)
    | extType(_, varType(_)) -> valVarUnifyExpr(_, _, _, location=_)
    | errorType() -> \ Expr Expr Expr l::Location -> errorExpr([], location=l)
    end;
  
  top.showErrors =
    \ l::Location env::Decorated Env ->
      sub.showErrors(l, env) ++
      checkListHeaderDef("show_list", l, env);
  top.showProd =
    \ e::Expr -> ableC_Expr { inst show_list<$directTypeExpr{sub}>($Expr{e}) };
}

-- Find the sub-type of a list type
function listSubType
Type ::= t::Type
{
  return
    case t of
    | extType(_, listType(sub)) -> sub
    | _ -> errorType()
    end;
}
