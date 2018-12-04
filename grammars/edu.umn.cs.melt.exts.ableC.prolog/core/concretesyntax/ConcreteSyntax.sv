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
terminal NotGoal_t '\+';
terminal NotEquals_t '\=';
terminal Eq_t '=:=';
terminal NotEq_t '=/=';
terminal PLessThan_t '<';
terminal EqualLessThan_t '=<';
terminal Wildcard_t '_';

disambiguate Identifier_t, Wildcard_t {
  pluck Wildcard_t;
}

disambiguate Identifier_t, TypeName_t, Wildcard_t {
  pluck Wildcard_t;
}

-- Fix ambiguity between 'a<...>(...)' and 'a < b' due to insufficient lookahead.
-- This makes so the lhs of the '<' goal must be wrapped in parentheses
disambiguate LessThan_t, PLessThan_t {
  pluck LessThan_t;
}

terminal PrologComment_t /% .*/ lexer classes {Ccomment};

concrete productions top::Declaration_c
| 'prolog' '{' ls::LogicStmts_c '}'
  { top.ast = logicDecl(ls.ast, top.location); }

closed nonterminal LogicStmts_c with location, ast<LogicStmts>;

concrete productions top::LogicStmts_c
| h::LogicStmt_c t::LogicStmts_c
  layout {LineComment, BlockComment, Spaces_t, NewLine_t, PrologComment_t}
  { top.ast = consLogicStmt(h.ast, t.ast); }
|
  layout {LineComment, BlockComment, Spaces_t, NewLine_t, PrologComment_t}
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
| '-' c::Constant_c
  { top.ast = constLogicExpr(negativeExpr(c.ast, location=top.location), location=top.location); }
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
| id::Identifier_c LessThan_t tns::TypeNames_c '>' LParen_t les::LogicExprs_c ')'
  { top.ast = predicateGoal(id.ast, tns.ast, foldLogicExpr(les.ast), location=top.location); }
| id::Identifier_c LessThan_t tns::TypeNames_c '>' LParen_t ')'
  { top.ast = predicateGoal(id.ast, tns.ast, nilLogicExpr(), location=top.location); }
| id::Identifier_c LParen_t les::LogicExprs_c ')'
  { top.ast = predicateGoal(id.ast, nilTypeName(), foldLogicExpr(les.ast), location=top.location); }
| id::Identifier_c LParen_t ')'
  { top.ast = predicateGoal(id.ast, nilTypeName(), nilLogicExpr(), location=top.location); }
| le::LogicExpr_c 'is' e::PrimaryExpr_c
  { top.ast = isGoal(le.ast, e.ast, location=top.location); }
| le1::LogicExpr_c '=' le2::LogicExpr_c
  { top.ast = equalsGoal(le1.ast, le2.ast, location=top.location); }
| le1::LogicExpr_c '\=' le2::LogicExpr_c
  { top.ast = notEqualsGoal(le1.ast, le2.ast, location=top.location); }
| e1::PrologPrimaryExpr_c '=:=' e2::PrimaryExpr_c
  { top.ast = eqGoal(e1.ast, e2.ast, location=top.location); }
| e1::PrologPrimaryExpr_c '=/=' e2::PrimaryExpr_c
  { top.ast = neqGoal(e1.ast, e2.ast, location=top.location); }
| e1::PrologPrimaryExpr_c PLessThan_t e2::PrimaryExpr_c
  { top.ast = ltGoal(e1.ast, e2.ast, location=top.location); }
| e1::PrologPrimaryExpr_c '=<' e2::PrimaryExpr_c
  { top.ast = eltGoal(e1.ast, e2.ast, location=top.location); }
| e1::PrologPrimaryExpr_c '>' e2::PrimaryExpr_c
  { top.ast = gtGoal(e1.ast, e2.ast, location=top.location); }
| e1::PrologPrimaryExpr_c '>=' e2::PrimaryExpr_c
  { top.ast = gteGoal(e1.ast, e2.ast, location=top.location); }
| '\+' g::Goal_c
  { top.ast = notGoal(g.ast, location=top.location); }
| Not_t
  { top.ast = cutGoal(location=top.location); }

-- Needed due to MWDA
nonterminal PrologPrimaryExpr_c with location, ast<Expr>;

concrete productions top::PrologPrimaryExpr_c
| id::Identifier_c
    { top.ast = directRefExpr(id.ast, location=top.location); }
-- dec
| c::DecConstant_t
    { top.ast = realConstant(integerConstant(c.lexeme, false, noIntSuffix(), location=top.location), location=top.location); }
| c::DecConstantU_t
    { top.ast = realConstant(integerConstant(c.lexeme, true, noIntSuffix(), location=top.location), location=top.location); }
| c::DecConstantL_t
    { top.ast = realConstant(integerConstant(c.lexeme, false, longIntSuffix(), location=top.location), location=top.location); }
| c::DecConstantUL_t
    { top.ast = realConstant(integerConstant(c.lexeme, true, longIntSuffix(), location=top.location), location=top.location); }
| c::DecConstantLL_t
    { top.ast = realConstant(integerConstant(c.lexeme, false, longLongIntSuffix(), location=top.location), location=top.location); }
| c::DecConstantULL_t
    { top.ast = realConstant(integerConstant(c.lexeme, true, longLongIntSuffix(), location=top.location), location=top.location); }
-- oct
| c::OctConstant_t
    { top.ast = realConstant(octIntegerConstant(c.lexeme, false, noIntSuffix(), location=top.location), location=top.location); }
| c::OctConstantU_t
    { top.ast = realConstant(integerConstant(c.lexeme, true, noIntSuffix(), location=top.location), location=top.location); }
| c::OctConstantL_t
    { top.ast = realConstant(integerConstant(c.lexeme, false, longIntSuffix(), location=top.location), location=top.location); }
| c::OctConstantUL_t
    { top.ast = realConstant(integerConstant(c.lexeme, true, longIntSuffix(), location=top.location), location=top.location); }
| c::OctConstantLL_t
    { top.ast = realConstant(integerConstant(c.lexeme, false, longLongIntSuffix(), location=top.location), location=top.location); }
| c::OctConstantULL_t
    { top.ast = realConstant(integerConstant(c.lexeme, true, longLongIntSuffix(), location=top.location), location=top.location); }
| c::OctConstantError_t
    { top.ast = errorExpr([err(top.location, "Erroneous octal constant: " ++ c.lexeme)], location=top.location); }
-- hex
| c::HexConstant_t
    { top.ast = realConstant(hexIntegerConstant(c.lexeme, false, noIntSuffix(), location=top.location), location=top.location); }
| c::HexConstantU_t
    { top.ast = realConstant(hexIntegerConstant(c.lexeme, true, noIntSuffix(), location=top.location), location=top.location); }
| c::HexConstantL_t
    { top.ast = realConstant(hexIntegerConstant(c.lexeme, false, longIntSuffix(), location=top.location), location=top.location); }
| c::HexConstantUL_t
    { top.ast = realConstant(hexIntegerConstant(c.lexeme, true, longIntSuffix(), location=top.location), location=top.location); }
| c::HexConstantLL_t
    { top.ast = realConstant(hexIntegerConstant(c.lexeme, false, longLongIntSuffix(), location=top.location), location=top.location); }
| c::HexConstantULL_t
    { top.ast = realConstant(hexIntegerConstant(c.lexeme, true, longLongIntSuffix(), location=top.location), location=top.location); }
-- floats
| c::FloatConstant_t
    { top.ast = realConstant(floatConstant(c.lexeme, doubleFloatSuffix(), location=top.location), location=top.location); }
| c::FloatConstantFloat_t
    { top.ast = realConstant(floatConstant(c.lexeme, floatFloatSuffix(), location=top.location), location=top.location); }
| c::FloatConstantLongDouble_t
    { top.ast = realConstant(floatConstant(c.lexeme, longDoubleFloatSuffix(), location=top.location), location=top.location); }
-- hex floats
| c::HexFloatConstant_t
    { top.ast = realConstant(hexFloatConstant(c.lexeme, doubleFloatSuffix(), location=top.location), location=top.location); }
| c::HexFloatConstantFloat_t
    { top.ast = realConstant(hexFloatConstant(c.lexeme, floatFloatSuffix(), location=top.location), location=top.location); }
| c::HexFloatConstantLongDouble_t
    { top.ast = realConstant(hexFloatConstant(c.lexeme, longDoubleFloatSuffix(), location=top.location), location=top.location); }
-- characters
| c::CharConstant_t
    { top.ast = characterConstant(c.lexeme, noCharPrefix(), location=top.location); }
| c::CharConstantL_t
    { top.ast = characterConstant(c.lexeme, wcharCharPrefix(), location=top.location); }
| c::CharConstantU_t
    { top.ast = characterConstant(c.lexeme, char16CharPrefix(), location=top.location); }
| c::CharConstantUBig_t
    { top.ast = characterConstant(c.lexeme, char32CharPrefix(), location=top.location); }
| sc::StringConstant_t
    { top.ast = stringLiteral(sc.lexeme, location=top.location); }
| LParen_t e::Expr_c  ')'
    { top.ast = parenExpr(e.ast, location=top.location); }
