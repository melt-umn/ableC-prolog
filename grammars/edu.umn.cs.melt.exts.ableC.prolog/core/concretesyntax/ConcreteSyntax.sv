grammar edu:umn:cs:melt:exts:ableC:prolog:core:concretesyntax;

imports edu:umn:cs:melt:ableC:concretesyntax;
imports edu:umn:cs:melt:ableC:concretesyntax:lexerHack as lh;
imports silver:langutil; 

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

exports edu:umn:cs:melt:exts:ableC:unification:concretesyntax;

marking terminal Prolog_t 'prolog' lexer classes {Ckeyword};
terminal If_t ':-';
terminal Is_t 'is';
terminal Wildcard_t '_';

disambiguate Identifier_t, Wildcard_t {
  pluck Wildcard_t;
}

disambiguate Identifier_t, TypeName_t, Wildcard_t {
  pluck Wildcard_t;
}

concrete productions top::Declaration_c
| 'prolog' '{' ls::LogicStmts_c '}'
  { top.ast = logicDecl(ls.ast); }

closed nonterminal LogicStmts_c with location, ast<LogicStmts>;

concrete productions top::LogicStmts_c
| h::LogicStmt_c t::LogicStmts_c
  { top.ast = consLogicStmt(h.ast, t.ast); }
|
  { top.ast = nilLogicStmt(); }

closed nonterminal LogicStmt_c with location, ast<LogicStmt>;

concrete productions top::LogicStmt_c
| id::Identifier_c '<' typeParams::TypeParameters_c '>' LParen_t params::ParameterTypeList_c ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, typeParams.ast, foldParameterDecl(params.ast), location=top.location), location=top.location); }
  action { context = lh:closeScope(context); } -- Opened by TemplateParams_c
| id::Identifier_c '<' typeParams::TypeParameters_c '>' LParen_t ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, typeParams.ast, nilParameters(), location=top.location), location=top.location); }
  action { context = lh:closeScope(context); } -- Opened by TemplateParams_c
| id::Identifier_c LParen_t params::ParameterTypeList_c ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, nilName(), foldParameterDecl(params.ast), location=top.location), location=top.location); }
| id::Identifier_c LParen_t ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, nilName(), nilParameters(), location=top.location), location=top.location); }
| id::Identifier_c LParen_t le::LogicExprs_c ')' '.'
  { top.ast = ruleLogicStmt(id.ast, foldLogicExpr(le.ast), nilGoal(), location=top.location); }
| id::Identifier_c LParen_t le::LogicExprs_c ')' ':-' ps::Goals_c '.'
  { top.ast = ruleLogicStmt(id.ast, foldLogicExpr(le.ast), foldGoal(ps.ast), location=top.location); }

closed nonterminal LogicExprs_c with location, ast<[LogicExpr]>;

concrete productions top::LogicExprs_c
| h::LogicExpr_c ',' t::LogicExprs_c
  { top.ast = h.ast :: t.ast; }
| h::LogicExpr_c
  { top.ast = [h.ast]; }

closed nonterminal LogicExpr_c with location, ast<LogicExpr>;

concrete productions top::LogicExpr_c
| id::Identifier_c
  { top.ast = varLogicExpr(id.ast, location=top.location); }
| '_'
  { top.ast = wildcardLogicExpr(location=top.location); }
| c::Constant_c
  { top.ast = constLogicExpr(c.ast, location=top.location); }
| s::StringConstant_c
  { top.ast = constLogicExpr(stringLiteral(s.ast, location=s.location), location=top.location); }
| id::Identifier_c LParen_t le::LogicExprs_c ')'
  { top.ast = constructorLogicExpr(id.ast, foldLogicExpr(le.ast), location=top.location); }
| id::Identifier_c LParen_t ')'
  { top.ast = constructorLogicExpr(id.ast, nilLogicExpr(), location=top.location); }

closed nonterminal Goals_c with location, ast<[Goal]>;

concrete productions top::Goals_c
| h::Goal_c ',' t::Goals_c
  { top.ast = h.ast :: t.ast; }
| h::Goal_c
  { top.ast = [h.ast]; }

closed nonterminal Goal_c with location, ast<Goal>;

concrete productions top::Goal_c
| id::Identifier_c '<' tns::TypeNames_c '>' LParen_t les::LogicExprs_c ')'
  { top.ast = predicateGoal(id.ast, tns.ast, foldLogicExpr(les.ast), location=top.location); }
| id::Identifier_c '<' tns::TypeNames_c '>' LParen_t ')'
  { top.ast = predicateGoal(id.ast, tns.ast, nilLogicExpr(), location=top.location); }
| id::Identifier_c LParen_t les::LogicExprs_c ')'
  { top.ast = predicateGoal(id.ast, nilTypeName(), foldLogicExpr(les.ast), location=top.location); }
| id::Identifier_c LParen_t ')'
  { top.ast = predicateGoal(id.ast, nilTypeName(), nilLogicExpr(), location=top.location); }
| le::LogicExpr_c 'is' e::PrimaryExpr_c
  { top.ast = isGoal(le.ast, e.ast, location=top.location); }
| Not_t
  { top.ast = cutGoal(location=top.location); }
