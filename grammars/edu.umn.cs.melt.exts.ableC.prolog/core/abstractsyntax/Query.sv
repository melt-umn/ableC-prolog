grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

abstract production queryExpr
top::Expr ::= ps::Predicates body::Stmt
{
  propagate substituted;
  top.pp = pp"query ${ppImplode(pp", ", ps.pps)} ${braces(nestlines(2, body.pp))}";
  
  local localErrors::[Message] = ps.errors ++ body.errors;
  ps.env = openScopeEnv(top.env);
  body.env = openScopeEnv(addEnv(ps.defs, ps.env));
  body.returnType = just(builtinType(nilQualifier(), boolType()));
  
  ps.continuationTransformIn = ableC_Expr { lambda allocate(alloca) () -> (_Bool) { $Stmt{body} } };
  local fwrd::Expr =
    ableC_Expr {
      proto_typedef unification_trail;
      ({unification_trail _trail = new_trail();
        $Stmt{makeVarDecls(ps.defs)}
        _Bool _result = $Expr{ps.transform};
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
