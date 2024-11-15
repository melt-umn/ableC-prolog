grammar edu:umn:cs:melt:exts:ableC:prolog:core:concretesyntax;

marking terminal Term_t 'term' lexer classes {Keyword, Global};

concrete productions top::PrimaryExpr_c
| 'term' '<' ty::TypeName_c '>' '{' le::LogicExpr_c '}'
  { top.ast = termExpr(ty.ast, le.ast); }
| 'term' '{' le::LogicExpr_c '}'
  { top.ast = inferredTermExpr(le.ast); }
