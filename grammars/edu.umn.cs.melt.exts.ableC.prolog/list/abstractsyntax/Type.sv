grammar edu:umn:cs:melt:exts:ableC:prolog:list:abstractsyntax;

abstract production listTypeExpr 
top::BaseTypeExpr ::= q::Qualifiers sub::TypeName
{
  top.pp = pp"${terminate(space(), q.pps)}list<${sub.pp}>";
  
  top.inferredArgs := sub.inferredArgs;
  sub.argumentType =
    case top.argumentType of
    | extType(_, listType(t)) -> ^t
    | _ -> errorType()
    end;

  local localErrors::[Message] = sub.errors ++ checkListHeaderDef(top.env);

  forward fwrd =
    injectGlobalDeclsTypeExpr(
      consDecl(
        typePreDecls(@sub),
        consDecl(
          templateTypeExprInstDecl(
            ^q, name("_list_d"),
            consTemplateArg(typeTemplateArg(sub.typerep), nilTemplateArg())),
          nilDecl())),
      extTypeExpr(@q, listType(sub.typerep)));

  forwards to if null(localErrors) then @fwrd else errorTypeExpr(localErrors);
}

abstract production listType
top::ExtType ::= sub::Type
{
  propagate canonicalType;
  top.pp = pp"list<${sub.lpp}${sub.rpp}>";

  local templateArgs::TemplateArgs = consTemplateArg(typeTemplateArg(@sub), nilTemplateArg());
  top.host =
    extType(
      top.givenQualifiers,
      adtExtType(
        "_list_d",
        templateArgs.templateMangledName("_list_d"),
        templateArgs.templateMangledRefId("_list_d"))).host;
  top.baseTypeExpr =
    listTypeExpr(top.givenQualifiers, typeName(sub.baseTypeExpr, sub.typeModifierExpr));
  top.mangledName = s"list_${sub.mangledName}_";
  top.isEqualTo =
    \ other::ExtType ->
      case other of
      | listType(otherSub) -> compatibleTypes(^sub, ^otherSub, false, false)
      | _ -> false
      end;
  
  top.maybeRefId := just(templateArgs.templateMangledRefId("_list_d"));
  
  top.unifyErrors =
    \ env::Env ->
      case top.otherType of
      | extType(_, listType(otherSub)) ->
        if compatibleTypes(^sub, ^otherSub, false, false)
        then decorate ^sub with {otherType = ^otherSub;}.unifyErrors(env)
        else [errFromOrigin(ambientOrigin(), s"Unification list types must match (got ${show(80, ^sub)}, ${show(80, ^otherSub)})")]
      | extType(_, varType(extType(_, listType(otherSub)))) ->
        if compatibleTypes(^sub, ^otherSub, false, false)
        then decorate ^sub with {otherType = ^otherSub;}.unifyErrors(env)
        else [errFromOrigin(ambientOrigin(), s"Unification value and variable list types must match (got ${show(80, ^sub)}, ${show(80, ^otherSub)})")]
      | errorType() -> []
      | t -> [errFromOrigin(ambientOrigin(), s"Unification is not defined for list<${show(80, ^sub)}> and non-list ${show(80, t)}")]
      end ++
      checkListHeaderDef(env);
  top.unifyProd =
    case top.otherType of
    | extType(_, listType(_)) -> listUnifyExpr(^sub)
    | extType(_, varType(otherSub)) -> valVarUnifyExpr(^otherSub)
    | _ -> defaultUnifyExpr
    end;

  top.showErrors := \ env::Env -> sub.showErrors(env) ++ checkListHeaderDef(env);
  top.showMaxLenProd = \ e::Expr -> ableC_Expr {
    inst show_list_max_len<$directTypeExpr{^sub}>($Expr{e})
  };
  top.showProd = \ buf::Expr e::Expr -> ableC_Expr {
    inst show_list_to_buf<$directTypeExpr{^sub}>($Expr{buf}, $Expr{e})
  };
}

-- Find the sub-type of a list type
function listSubType
Type ::= t::Type
{
  return
    case t of
    | extType(_, listType(sub)) -> ^sub
    | _ -> errorType()
    end;
}
