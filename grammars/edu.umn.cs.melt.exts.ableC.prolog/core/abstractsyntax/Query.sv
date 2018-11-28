grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

abstract production queryExpr
top::Expr ::= gs::Goals body::Stmt
{
  propagate substituted;
  top.pp = pp"query ${ppImplode(pp", ", gs.pps)} ${braces(nestlines(2, body.pp))}";
  
  local localErrors::[Message] = gs.errors ++ body.errors;
  gs.env = openScopeEnv(top.env);
  body.env = openScopeEnv(addEnv(gs.defs, gs.env));
  body.returnType = just(builtinType(nilQualifier(), boolType()));
  
  gs.continuationTransformIn = ableC_Expr { lambda allocate(alloca) () -> (_Bool) { $Stmt{body} } };
  local fwrd::Expr =
    ableC_Expr {
      proto_typedef unification_trail;
      ({unification_trail _trail = new_trail();
        $Stmt{makeVarDecls(gs.defs)}
        _Bool _result = $Expr{gs.transform};
        undo_trail(_trail, 0);
        delete _trail;
        _result;})
    };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

-- Generate declarations for all defined variables
function makeVarDecls
Stmt ::= defs::[Def]
{
  return
    foldStmt(
      catMaybes(
        map(
          \ item::Pair<String ValueItem> ->
            case item.snd of
            | varValueItem(t, _) ->
              just(
                mkDecl(
                  item.fst, item.snd.typerep,
                  freeVarExpr(
                    typeName(directTypeExpr(varSubType(t)), baseTypeExpr()),
                    ableC_Expr { alloca },
                    location=builtin),
                  builtin))
            | _ -> nothing()
            end,
          foldr(consDefs, nilDefs(), defs).valueContribs)));
}
