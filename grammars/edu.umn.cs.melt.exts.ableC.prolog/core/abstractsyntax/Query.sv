grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

abstract production queryExpr
top::Expr ::= gs::Goals body::Stmt
{
  top.pp = pp"query ${ppImplode(pp", ", gs.pps)} ${braces(nestlines(2, body.pp))}";
  
  local localErrors::[Message] = gs.errors ++ body.errors;
  
  gs.env = openScopeEnv(top.env);
  gs.predicateName = nothing();
  gs.refVariables = gs.freeVariables;
  gs.isLastGoal = true;
  gs.tailCallPermitted = false;
  
  -- Need to decorate var decls here to compute the env for body, since this may
  -- contain defs not in gs.defs
  local varDecls::Stmt = makeVarDecls(gs.defs);
  varDecls.env = gs.env;
  varDecls.returnType = nothing();
  
  body.env = addEnv(body.functionDefs, capturedEnv(addEnv(varDecls.defs, gs.env)));
  body.returnType = just(builtinType(nilQualifier(), boolType()));
  
  gs.continuationTransformIn = ableC_Expr { _success_continuation };
  local fwrd::Expr =
    ableC_Expr {
      proto_typedef unification_trail, jmp_buf;
      ({unification_trail _trail = new_trail();
        $Stmt{decStmt(varDecls)}
        closure<() -> _Bool> _success_continuation =
          lambda allocate(alloca) () -> _Bool { $Stmt{decStmt(body)} };
        
        // If a failure after cut occurs, control is returned to this point with longjmp
        jmp_buf _cut_buffer;
        setjmp(_cut_buffer)?
         ({undo_trail(_trail, 0);
           delete _trail;
           0;}) :
         ({_Bool _result = $Expr{gs.transform};
           undo_trail(_trail, 0);
           delete _trail;
           _result;});})
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
