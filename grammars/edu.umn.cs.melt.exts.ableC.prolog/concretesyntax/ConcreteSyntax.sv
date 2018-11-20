grammar edu:umn:cs:melt:exts:ableC:prolog:concretesyntax;

imports edu:umn:cs:melt:ableC:concretesyntax;
imports edu:umn:cs:melt:ableC:concretesyntax:lexerHack as lh;
imports silver:langutil; 

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:exts:ableC:prolog:abstractsyntax;

exports edu:umn:cs:melt:exts:ableC:unification:concretesyntax;

marking terminal Prolog_t 'prolog' lexer classes {Ckeyword};
terminal If_t ':-';

concrete productions top::Declaration_c
| 'prolog' '{' ls::LogicStmts_c '}'
  { top.ast = logicDecl(ls.ast); }

nonterminal LogicStmts_c with location, ast<LogicStmts>;

concrete productions top::LogicStmts_c
| h::LogicStmt_c t::LogicStmts_c
  { top.ast = consLogicStmt(h.ast, t.ast); }
|
  { top.ast = nilLogicStmt(); }

nonterminal LogicStmt_c with location, ast<LogicStmt>;

concrete productions top::LogicStmt_c
| id::Identifier_c typeParams::TypeParameters_c LParen_t params::ParameterTypeList_c ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, typeParams.ast, foldParameterDecl(params.ast), location=top.location), location=top.location); }
  action { context = lh:closeScope(context); } -- Opened by TemplateParams_c
| id::Identifier_c typeParams::TypeParameters_c LParen_t ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, typeParams.ast, nilParameters(), location=top.location), location=top.location); }
  action { context = lh:closeScope(context); } -- Opened by TemplateParams_c
| id::Identifier_c LParen_t params::ParameterTypeList_c ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, nilName(), foldParameterDecl(params.ast), location=top.location), location=top.location); }
| id::Identifier_c LParen_t ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, nilName(), nilParameters(), location=top.location), location=top.location); }
| id::Identifier_c LParen_t le::LogicExprs_c ')' '.'
  { }
| id::Identifier_c LParen_t le::LogicExprs_c ')' ':-' ps::Predicates_c '.'
  { }

nonterminal LogicExprs_c with location, ast<[LogicExpr]>;

concrete productions top::LogicExprs_c
| h::LogicExpr_c ',' t::LogicExprs_c
  { top.ast = h.ast :: t.ast; }
| h::LogicExpr_c
  { top.ast = [h.ast]; }
|
  { top.ast = []; }

nonterminal LogicExpr_c with location, ast<LogicExpr>;

concrete productions top::LogicExpr_c
| id::Identifier_c LParen_t le::LogicExprs_c ')'
  { }

nonterminal Predicates_c with location, ast<[Predicate]>;

concrete productions top::Predicates_c
| h::Predicate_c ',' t::Predicates_c
  { top.ast = h.ast :: t.ast; }
| h::Predicate_c
  { top.ast = [h.ast]; }

nonterminal Predicate_c with location, ast<Predicate>;

concrete productions top::Predicate_c
| id::Identifier_c LParen_t le::LogicExprs_c ')'
  { }