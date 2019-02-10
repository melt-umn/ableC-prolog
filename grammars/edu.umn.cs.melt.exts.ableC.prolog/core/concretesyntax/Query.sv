grammar edu:umn:cs:melt:exts:ableC:prolog:core:concretesyntax;

marking terminal Query_t 'query' lexer classes {Cidentifier}, font=font_all;

aspect parser attribute context
  action {
    context = addIdentsToScope([name("query", location=builtin)], Query_t, context);
  };

concrete productions top::PrimaryExpr_c
| 'query' ps::Body_c '{' body::BlockItemList_c '}'
  { top.ast = queryExpr(foldGoal(ps.ast), foldStmt(body.ast), location=top.location); }
| 'query' ps::Body_c '{' '}'
  { top.ast = queryExpr(foldGoal(ps.ast), nullStmt(), location=top.location); }
