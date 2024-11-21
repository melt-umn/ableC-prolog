grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

abstract production queryExpr
top::Expr ::= gs::Goals body::Stmt
{
  top.pp = pp"query ${ppImplode(pp", ", gs.pps)} ${braces(nestlines(2, body.pp))}";
  attachNote extensionGenerated("ableC-prolog");
  
  local localErrors::[Message] = gs.errors ++ body.errors;
  
  gs.env = openScopeEnv(top.env);
  gs.predicateName = nothing();
  gs.refVariables = gs.freeVariables;
  gs.lastGoalCond = [[]];
  gs.tailCallPermitted = false;
  
  gs.continuationTransformIn = ableC_Expr { _success_continuation };
  local fwrd::Expr =
    ableC_Expr {
      proto_typedef unification_trail, jmp_buf, size_t, arena_t;
      ({allocate_using stack;
        arena_t _trail_arena = arena_create();
        unification_trail _trail = new_trail(_trail_arena);
        $Decl{decls(makeVarDecls(gs.defs))}
        closure<() -> _Bool> _success_continuation =
          lambda () -> _Bool {
            $Stmt{@body}
            return 1;
          };
        
        $Stmt{
          if gs.containsCut
          then ableC_Stmt {
            size_t _initial_trail_index = 0;
            jmp_buf _cut_buffer;
            // If a failure after cut occurs, control is returned to this point with longjmp
            _Bool _result = setjmp(_cut_buffer)? 0 : $Expr{gs.transform};
          }
          else ableC_Stmt {
            _Bool _result = $Expr{gs.transform};
          }
        }
        
        undo_trail(_trail, 0);
        arena_destroy(_trail_arena);
        _result;})
    };
  fwrd.env = top.env;
  fwrd.controlStmtContext = top.controlStmtContext;
  
  forwards to mkErrorCheck(localErrors, @fwrd);
}

production queryElseStmt
top::Stmt ::= gs::Goals body::Stmt el::Stmt
{
  top.pp = pp"query ${ppImplode(pp", ", gs.pps)} ${braces(nestlines(2, body.pp))} else ${el.pp}";

  forwards to ifStmtNoElse(notExpr(queryExpr(@gs, @body)), @el);
}

-- Generate declarations for all defined variables
fun makeVarDecls Decls ::= defs::[Def] =
  foldDecl(filterMap(
    \ item::Pair<String ValueItem> ->
      case item.snd of
      | varValueItem(extType(_, varType(t))) ->
        just(ableC_Decl {
          $directTypeExpr{item.snd.typerep} $name{item.fst} =
            $Expr{freeVarTypeNameExpr(typeName(t.baseTypeExpr, t.typeModifierExpr))};
        })
      | _ -> nothing()
      end,
    foldr(consDefs, nilDefs(), defs).valueContribs));
