grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

abstract production termExpr
top::Expr ::= ty::TypeName le::LogicExpr
{
  top.pp = pp"term<${ty.pp}> {${le.pp}}";
  
  local localErrors::[Message] =
    ty.errors ++ le.errors ++
    (if !ty.typerep.isCompleteType(top.env)
     then [errFromOrigin(top, s"term type parameter has incomplete type ${show(80, ty.typerep)}")]
     else []) ++
    checkUnificationHeaderDef(top.env);

  le.env = addEnv(ty.defs, ty.env);
  le.refVariables = [];
  le.expectedType = ty.typerep;
  le.allowUnificationTypes = false;
  
  forward fwrd =
    ableC_Expr {
      ({$Decl{typePreDecls(@ty)}
        $Decl{decls(makeVarDecls(le.defs))}
        $Expr{le.transform};})
    };

  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

abstract production inferredTermExpr
top::Expr ::= le::LogicExpr
{
  top.pp = pp"term {${le.pp}}";
  
  local localErrors::[Message] =
    if !le.maybeTyperep.isJust
    then [errFromOrigin(top, "Couldn't infer type of term")]
    else le.errors;

  le.env = top.env;
  local inferredType::Type = fromMaybe(errorType(), le.maybeTyperep);
  
  forward fwrd =
    termExpr(
      typeName(directTypeExpr(le.maybeTyperep.fromJust), baseTypeExpr()),
      @le);

  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}
