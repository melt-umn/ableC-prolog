grammar edu:umn:cs:melt:exts:ableC:prolog:concretesyntax;

marking terminal Query_t 'query' lexer classes {Ckeyword};

concrete productions top::PrimaryExpr_c
| 'query' ps::Predicates_c '{' body::BlockItemList_c '}'
  { top.ast = queryExpr(foldPredicate(ps.ast), foldStmt(body.ast), location=top.location); }
| 'query' ps::Predicates_c '{' '}'
  { top.ast = queryExpr(foldPredicate(ps.ast), nullStmt(), location=top.location); }
