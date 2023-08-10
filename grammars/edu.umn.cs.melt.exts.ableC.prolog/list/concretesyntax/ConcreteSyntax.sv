grammar edu:umn:cs:melt:exts:ableC:prolog:list:concretesyntax;

imports silver:langutil;
imports edu:umn:cs:melt:ableC:concretesyntax;
imports edu:umn:cs:melt:exts:ableC:algebraicDataTypes:patternmatching:concretesyntax;
imports edu:umn:cs:melt:exts:ableC:prolog:core:concretesyntax;

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:overloadable as ovrld;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;
imports edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;
imports edu:umn:cs:melt:exts:ableC:prolog:list:abstractsyntax;

marking terminal List_t 'list' lexer classes {Type, Global};

concrete productions top::TypeSpecifier_c
| 'list' LessThan_t sub::TypeName_c '>'
    { top.realTypeSpecifiers = [listTypeExpr(top.givenQualifiers, sub.ast)];
      top.preTypeSpecifiers = []; }

marking terminal NewList_t 'newlist' lexer classes {Keyword, Global};

concrete productions top::PrimaryExpr_c
| 'newlist' LessThan_t sub::TypeName_c '>' LParen_t allocate::Expr_c ')' LBracket_t init::ListInitializerList_c ']'
  { top.ast = constructList(sub.ast, allocate.ast, init.ast); }
| 'newlist' LParen_t allocate::Expr_c ')' LBracket_t init::ListInitializerList_c ']'
  { top.ast = inferredConstructList(allocate.ast, init.ast); }

tracked nonterminal ListInitializerList_c with ast<ListInitializers>;

concrete productions top::ListInitializerList_c
| h::AssignExpr_c ',' t::ListInitializerList_c
    { top.ast = consListInitializer(h.ast, t.ast);  }
| e::AssignExpr_c
    { top.ast =
        -- Semantic workaround for parsing ambiguity with |
        case decorate e.ast with {env = emptyEnv();
            controlStmtContext = initialControlStmtContext;} of
        | ovrld:orBitExpr(h, t) -> consListInitializer(h, tailListInitializer(t))
        | _ -> consListInitializer(e.ast, nilListInitializer())
        end;
    }
|
    { top.ast = nilListInitializer(); }

marking terminal ListLBracket_t '[';

concrete productions top::LogicExpr_c
| ListLBracket_t l::ListLogicExprList_c ']'
  { top.ast = listLogicExpr(l.ast); }

tracked nonterminal ListLogicExprList_c with ast<ListLogicExprs>;

concrete productions top::ListLogicExprList_c
| h::LogicExpr_c ',' t::ListLogicExprList_c
    { top.ast = consListLogicExpr(h.ast, t.ast);  }
| e::LogicExpr_c
    { top.ast = consListLogicExpr(e.ast, nilListLogicExpr()); }
| h::LogicExpr_c '|' t::LogicExpr_c
    { top.ast = consListLogicExpr(h.ast, tailListLogicExpr(t.ast)); }
|
    { top.ast = nilListLogicExpr(); }

marking terminal ListPatternLBracket_t '[';

concrete productions top::BasicPattern_c
| ListPatternLBracket_t l::ListPatternList_c ']'
  { top.ast = listPattern(l.ast); }

tracked nonterminal ListPatternList_c with ast<ListPatterns>;

concrete productions top::ListPatternList_c
| h::Pattern_c ',' t::ListPatternList_c
    { top.ast = consListPattern(h.ast, t.ast);  }
| e::Pattern_c
    { top.ast = consListPattern(e.ast, nilListPattern()); }
| h::Pattern_c '|' t::Pattern_c
    { top.ast = consListPattern(h.ast, tailListPattern(t.ast)); }
|
    { top.ast = nilListPattern(); }
