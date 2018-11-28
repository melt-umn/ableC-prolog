grammar edu:umn:cs:melt:exts:ableC:prolog:core:concretesyntax;

marking terminal Query_t 'query' lexer classes {Ckeyword};

concrete productions top::PrimaryExpr_c
| 'query' ps::Goals_c '{' body::BlockItemList_c '}'
  { top.ast = queryExpr(foldGoal(ps.ast), foldStmt(body.ast), location=top.location); }
| 'query' ps::Goals_c '{' '}'
  { top.ast = queryExpr(foldGoal(ps.ast), nullStmt(), location=top.location); }
