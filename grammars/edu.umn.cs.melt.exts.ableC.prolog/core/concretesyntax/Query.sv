grammar edu:umn:cs:melt:exts:ableC:prolog:core:concretesyntax;

marking terminal Query_t 'query' lexer classes {Keyword, Global};

concrete productions top::PrimaryExpr_c
| 'query' ps::Body_c '{' body::BlockItemList_c '}'
  { top.ast = queryExpr(foldGoal(ps.ast), foldStmt(body.ast)); }
| 'query' ps::Body_c '{' '}'
  { top.ast = queryExpr(foldGoal(ps.ast), nullStmt()); }
