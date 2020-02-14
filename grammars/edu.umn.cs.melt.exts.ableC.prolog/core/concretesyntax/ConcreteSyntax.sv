grammar edu:umn:cs:melt:exts:ableC:prolog:core:concretesyntax;

imports edu:umn:cs:melt:ableC:concretesyntax;
imports silver:langutil; 

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:exts:ableC:templating:abstractsyntax;
imports edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

exports edu:umn:cs:melt:exts:ableC:templating:concretesyntax:templateParameters;
exports edu:umn:cs:melt:exts:ableC:templating:concretesyntax:templateArguments;

marking terminal Prolog_t 'prolog' lexer classes {Keyword, Global};
terminal If_t ':-';
terminal Is_t 'is' lexer classes {Keyword};
terminal NotGoal_t '\+' lexer classes {Operator};
terminal NotEquals_t '\=' lexer classes {Operator};
terminal Eq_t '=:=' lexer classes {Operator};
terminal NotEq_t '=\=' lexer classes {Operator};
terminal PLessThan_t '<' lexer classes {Operator};
terminal EqualLessThan_t '=<' lexer classes {Operator};

-- Fix ambiguity between 'a<...>(...)' and 'a < b' due to insufficient lookahead.
-- This makes so the lhs of the '<' goal must be wrapped in parentheses
disambiguate LessThan_t, PLessThan_t {
  pluck LessThan_t;
}

terminal PrologComment_t /%.*/ lexer classes {Comment};

-- Used to seed follow sets for MDA
terminal LogicExprNEVER_t 'LogicExprNEVER_t123456789!!!never';

-- Record the type parameters of all known prediates so that rules can add the
-- appropriate names to the parser context.
parser attribute predicateTemplateParams::[Pair<String [Pair<String TerminalId>]>]
  action { predicateTemplateParams = []; };

concrete productions top::Declaration_c
| 'prolog' '{' ls::LogicStmts_c '}'
  layout {
    -- We are choosing to allow regular C line comments in addition to Prolog-style ones.
    PrologComment_t, LineComment_t, BlockComment_t,
    NewLine_t, Spaces_t,
    -- Parse these to allow for .pl files to be #included in logic decl blocks
    CPP_Location_Tag_t
  }
  { top.ast = logicDecl(ls.ast, top.location); }

closed nonterminal LogicStmts_c with location, ast<LogicStmts>;

concrete productions top::LogicStmts_c
| h::LogicStmt_c t::LogicStmts_c
  { top.ast = consLogicStmt(h.ast, t.ast); }
|
  { top.ast = nilLogicStmt(); }

closed nonterminal LogicStmt_c
  layout {
    -- Only C's layout terminals
    LineComment_t, BlockComment_t,
    NewLine_t, Spaces_t,  CPP_Location_Tag_t
  }
  with location, ast<LogicStmt>;

concrete productions top::LogicStmt_c
| id::Identifier_c LessThan_t templateParams::TemplateParameters_c '>' LParen_t params::ParameterTypeList_c ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, templateParams.ast, foldParameterDecl(params.ast), location=top.location), location=top.location); }
  action {
    context = closeScope(context); -- Opened by TemplateParameters_c
    predicateTemplateParams =
      pair(
        id.ast.name,
        zipWith(
          pair, templateParams.ast.names,
          map(
            \ k::Maybe<TypeName> -> if k.isJust then Identifier_t else TypeName_t,
            templateParams.ast.kinds))) ::
        predicateTemplateParams;
  }
| id::Identifier_c LessThan_t templateParams::TemplateParameters_c '>' LParen_t ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, templateParams.ast, nilParameters(), location=top.location), location=top.location); }
  action {
    context = closeScope(context); -- Opened by TemplateParameters_c
    predicateTemplateParams =
      pair(
        id.ast.name,
        zipWith(
          pair, templateParams.ast.names,
          map(
            \ k::Maybe<TypeName> -> if k.isJust then Identifier_t else TypeName_t,
            templateParams.ast.kinds))) ::
        predicateTemplateParams;
  }
| id::Identifier_c LParen_t params::ParameterTypeList_c ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, nilTemplateParameter(), foldParameterDecl(params.ast), location=top.location), location=top.location); }
| id::Identifier_c LParen_t ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, nilTemplateParameter(), nilParameters(), location=top.location), location=top.location); }
| h::Head_c '.'
  { top.ast = ruleLogicStmt(h.ast.fst, h.ast.snd, nilGoal(), location=top.location); }
  action { context = closeScope(context); } -- Opened by Head_c
| h::Head_c ':-' ps::Body_c '.'
  { top.ast = ruleLogicStmt(h.ast.fst, h.ast.snd, foldGoal(ps.ast), location=top.location); }
  action { context = closeScope(context); } -- Opened by Head_c

closed nonterminal Head_c with location, ast<Pair<Name LogicExprs>>;

concrete productions top::Head_c
| id::Identifier_c LParen_t le::LogicExprs_c ')'
  { top.ast = pair(id.ast, foldLogicExpr(le.ast)); }
  action {
    local templateParams::[Pair<String TerminalId>] =
      fromMaybe([], lookupBy(stringEq, id.ast.name, predicateTemplateParams));
    -- Open a new scope containing templateParams
    context = (templateParams ++ head(context)) :: context;
    context = addIdentsToScope(le.declaredIdents, Identifier_t, context);
  }

closed nonterminal Body_c with location, ast<[Goal]>;

concrete productions top::Body_c
| h::Goal_c ',' t::Body_c
  { top.ast = h.ast :: t.ast; }
| h::Goal_c
  { top.ast = [h.ast]; }

closed nonterminal Goal_c with location, ast<Goal>;

concrete productions top::Goal_c
| id::Identifier_c LessThan_t tas::TemplateArguments_c '>' LParen_t les::LogicExprs_c ')'
  { top.ast = predicateGoal(id.ast, tas.ast, foldLogicExpr(les.ast), location=top.location); }
  action { context = addIdentsToScope(les.declaredIdents, Identifier_t, context); }
| id::Identifier_c LessThan_t tas::TemplateArguments_c '>' LParen_t ')'
  { top.ast = predicateGoal(id.ast, tas.ast, nilLogicExpr(), location=top.location); }
| id::Identifier_c LParen_t les::LogicExprs_c ')'
  { top.ast = inferredPredicateGoal(id.ast, foldLogicExpr(les.ast), location=top.location); }
  action { context = addIdentsToScope(les.declaredIdents, Identifier_t, context); }
| id::Identifier_c LParen_t ')'
  { top.ast = inferredPredicateGoal(id.ast, nilLogicExpr(), location=top.location); }
| le::LogicExpr_c 'is' e::PrologPrimaryExpr_c
  { top.ast = isGoal(le.ast, e.ast, location=top.location); }
  action { context = addIdentsToScope(le.declaredIdents, Identifier_t, context); }
| le1::LogicExpr_c '=' le2::LogicExpr_c
  { top.ast = equalsGoal(le1.ast, le2.ast, location=top.location); }
  action { context = addIdentsToScope(le1.declaredIdents ++ le2.declaredIdents, Identifier_t, context); }
| le1::LogicExpr_c '\=' le2::LogicExpr_c
  { top.ast = notEqualsGoal(le1.ast, le2.ast, location=top.location); }
| e1::PrologPrimaryExpr_c '=:=' e2::PrologPrimaryExpr_c
  { top.ast = eqGoal(e1.ast, e2.ast, location=top.location); }
| e1::PrologPrimaryExpr_c '=\=' e2::PrologPrimaryExpr_c
  { top.ast = neqGoal(e1.ast, e2.ast, location=top.location); }
| e1::PrologPrimaryExpr_c PLessThan_t e2::PrologPrimaryExpr_c
  { top.ast = ltGoal(e1.ast, e2.ast, location=top.location); }
| e1::PrologPrimaryExpr_c '=<' e2::PrologPrimaryExpr_c
  { top.ast = eltGoal(e1.ast, e2.ast, location=top.location); }
| e1::PrologPrimaryExpr_c '>' e2::PrologPrimaryExpr_c
  { top.ast = gtGoal(e1.ast, e2.ast, location=top.location); }
| e1::PrologPrimaryExpr_c '>=' e2::PrologPrimaryExpr_c
  { top.ast = gteGoal(e1.ast, e2.ast, location=top.location); }
| '\+' g::Goal_c
  { top.ast = notGoal(g.ast, location=top.location); }
| Not_t
  { top.ast = cutGoal(location=top.location); }

closed nonterminal LogicExprs_c with location, ast<[LogicExpr]>, declaredIdents;

concrete productions top::LogicExprs_c
| h::LogicExpr_c ',' t::LogicExprs_c
  {
    top.ast = h.ast :: t.ast;
    top.declaredIdents = h.declaredIdents ++ t.declaredIdents;
  }
| h::LogicExpr_c
  {
    top.ast = [h.ast];
    top.declaredIdents = [];
  }

closed nonterminal LogicExpr_c with location, ast<LogicExpr>, declaredIdents;

aspect default production
top::LogicExpr_c ::=
{
  top.declaredIdents = [];
}

concrete productions top::LogicExpr_c
| id::Identifier_t
  {
    top.ast =
      if id.lexeme == "_"
      then wildcardLogicExpr(location=top.location)
      else nameLogicExpr(fromId(id), location=top.location);
    top.declaredIdents = [fromId(id)];
  }
| c::PrologConstant_c
  { top.ast = constLogicExpr(c.ast, location=top.location); }
| '-' c::PrologConstant_c
  { top.ast = constLogicExpr(negativeExpr(c.ast, location=top.location), location=top.location); }
| sc::StringConstant_t
  { top.ast = constLogicExpr(stringLiteral(sc.lexeme, location=sc.location), location=top.location); }
| id::Identifier_c LParen_t le::LogicExprs_c ')'
  {
    top.ast = constructorLogicExpr(id.ast, foldLogicExpr(le.ast), location=top.location);
    top.declaredIdents = le.declaredIdents;
  }
| id::Identifier_c LParen_t ')'
  { top.ast = constructorLogicExpr(id.ast, nilLogicExpr(), location=top.location); }
-- Seed follow set with some extra terminals useful for extensions,
-- such as Prolog lists
| LogicExprNEVER_t LogicExpr_c ']'
  { top.ast = error("shouldn't occur in parse tree!"); }
| LogicExprNEVER_t LogicExpr_c '|'
  { top.ast = error("shouldn't occur in parse tree!"); }

-- Needed due to MDA
nonterminal PrologPrimaryExpr_c with location, ast<Expr>;

concrete productions top::PrologPrimaryExpr_c
| id::Identifier_t
    { top.ast = directRefExpr(fromId(id), location=top.location); }
| c::PrologConstant_c
    { top.ast = c.ast; }
| sc::StringConstant_t
    { top.ast = stringLiteral(sc.lexeme, location=top.location); }
| LParen_t e::Expr_c  ')'
    { top.ast = parenExpr(e.ast, location=top.location); }

nonterminal PrologConstant_c with location, ast<Expr>;

concrete productions top::PrologConstant_c
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
