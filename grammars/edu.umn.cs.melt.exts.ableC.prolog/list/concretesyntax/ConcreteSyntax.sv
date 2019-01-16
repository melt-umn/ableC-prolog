grammar edu:umn:cs:melt:exts:ableC:prolog:list:concretesyntax;

imports silver:langutil;
imports edu:umn:cs:melt:ableC:concretesyntax;
imports edu:umn:cs:melt:exts:ableC:algebraicDataTypes:patternmatching:concretesyntax;
imports edu:umn:cs:melt:exts:ableC:prolog:core:concretesyntax;

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;
imports edu:umn:cs:melt:exts:ableC:prolog:list:abstractsyntax;

marking terminal List_t 'list' lexer classes {Ckeyword};

concrete productions top::TypeSpecifier_c
| 'list' LessThan_t sub::TypeName_c '>'
    { top.realTypeSpecifiers = [listTypeExpr(top.givenQualifiers, sub.ast, top.location)];
      top.preTypeSpecifiers = []; }

marking terminal NewList_t 'newlist' lexer classes {Ckeyword};

concrete productions top::PrimaryExpr_c
| 'newlist' LessThan_t sub::TypeName_c '>' LParen_t allocate::Expr_c ')' LBracket_t init::ListInitializerList_c ']'
  { top.ast = constructList(sub.ast, allocate.ast, init.ast, location=top.location); }

nonterminal ListInitializerList_c with location, ast<ListInitializers>;

concrete productions top::ListInitializerList_c
| h::ExclusiveOrExpr_c ',' t::ListInitializerList_c
    { top.ast = consListInitializer(h.ast, t.ast);  }
| e::ExclusiveOrExpr_c
    { top.ast = consListInitializer(e.ast, nilListInitializer()); }
| h::InclusiveOrExpr_c '|' t::ExclusiveOrExpr_c
    { top.ast = consListInitializer(h.ast, tailListInitializer(t.ast)); }
|
    { top.ast = nilListInitializer(); }

marking terminal ListLBracket_t '[' lexer classes {Csymbol};

concrete productions top::LogicExpr_c
| ListLBracket_t l::ListLogicExprList_c ']'
  { top.ast = listLogicExpr(l.ast, location=top.location); }

nonterminal ListLogicExprList_c with location, ast<ListLogicExprs>;

concrete productions top::ListLogicExprList_c
| h::LogicExpr_c ',' t::ListLogicExprList_c
    { top.ast = consListLogicExpr(h.ast, t.ast);  }
| e::LogicExpr_c
    { top.ast = consListLogicExpr(e.ast, nilListLogicExpr()); }
| h::LogicExpr_c '|' t::LogicExpr_c
    { top.ast = consListLogicExpr(h.ast, tailListLogicExpr(t.ast)); }
|
    { top.ast = nilListLogicExpr(); }

marking terminal ListPatternLBracket_t '[' lexer classes {Csymbol};

concrete productions top::BasicPattern_c
| ListPatternLBracket_t l::ListPatternList_c ']'
  { top.ast = listPattern(l.ast, location=top.location); }

nonterminal ListPatternList_c with location, ast<ListPatterns>;

concrete productions top::ListPatternList_c
| h::Pattern_c ',' t::ListPatternList_c
    { top.ast = consListPattern(h.ast, t.ast);  }
| e::Pattern_c
    { top.ast = consListPattern(e.ast, nilListPattern()); }
| h::Pattern_c '|' t::Pattern_c
    { top.ast = consListPattern(h.ast, tailListPattern(t.ast)); }
|
    { top.ast = nilListPattern(); }
