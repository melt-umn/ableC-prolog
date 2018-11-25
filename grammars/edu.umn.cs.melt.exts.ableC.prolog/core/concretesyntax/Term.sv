grammar edu:umn:cs:melt:exts:ableC:prolog:core:concretesyntax;

marking terminal Term_t 'term' lexer classes {Ckeyword};

concrete productions top::PrimaryExpr_c
| 'term' '<' ty::TypeName_c '>' LParen_t allocate::AssignExpr_c ')' '{' le::LogicExpr_c '}'
  { top.ast = termExpr(ty.ast, allocate.ast, le.ast, location=top.location); }