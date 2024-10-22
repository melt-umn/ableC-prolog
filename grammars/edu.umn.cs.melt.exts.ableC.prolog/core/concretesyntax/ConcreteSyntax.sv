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
terminal Initially_t 'initially' lexer classes {Keyword};
terminal Finally_t 'finally' lexer classes {Keyword};
terminal NotGoal_t '\+' lexer classes {Operator};
terminal NotEquals_t '\=' lexer classes {Operator};
terminal Eq_t '=:=' lexer classes {Operator};
terminal NotEq_t '=\=' lexer classes {Operator};
terminal PLessThan_t '<' lexer classes {Operator};
terminal EqualLessThan_t '=<' lexer classes {Operator};

disambiguate Initially_t, Identifier_t {
  pluck Initially_t;
}

disambiguate Finally_t, Identifier_t {
  pluck Finally_t;
}

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
  { top.ast = logicDecl(ls.ast); }

closed tracked nonterminal LogicStmts_c with ast<LogicStmts>;

concrete productions top::LogicStmts_c
| h::LogicStmt_c t::LogicStmts_c
  { top.ast = consLogicStmt(h.ast, t.ast); }
|
  { top.ast = nilLogicStmt(); }

closed tracked nonterminal LogicStmt_c
  layout {
    -- Only C's layout terminals
    LineComment_t, BlockComment_t,
    NewLine_t, Spaces_t,  CPP_Location_Tag_t
  }
  with ast<LogicStmt>;

concrete productions top::LogicStmt_c
| id::Identifier_c LessThan_t templateParams::TemplateParameters_c '>' LParen_t params::ParameterTypeList_c ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, templateParams.ast, foldParameterDecl(params.ast))); }
  action {
    context = closeScope(context); -- Opened by TemplateParameters_c
    predicateTemplateParams =
      ( id.ast.name,
        zip(
          templateParams.ast.names,
          map(
            \ k::Maybe<TypeName> -> if k.isJust then Identifier_t else TypeName_t,
            templateParams.ast.kinds))) ::
        predicateTemplateParams;
  }
| id::Identifier_c LessThan_t templateParams::TemplateParameters_c '>' LParen_t ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, templateParams.ast, nilParameters())); }
  action {
    context = closeScope(context); -- Opened by TemplateParameters_c
    predicateTemplateParams =
      ( id.ast.name,
        zip(
          templateParams.ast.names,
          map(
            \ k::Maybe<TypeName> -> if k.isJust then Identifier_t else TypeName_t,
            templateParams.ast.kinds))) ::
        predicateTemplateParams;
  }
| id::Identifier_c LParen_t params::ParameterTypeList_c ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, nilTemplateParameter(), foldParameterDecl(params.ast))); }
| id::Identifier_c LParen_t ')' ';'
  { top.ast = declLogicStmt(predicateDecl(id.ast, nilTemplateParameter(), nilParameters())); }
| h::Head_c '.'
  { top.ast = ruleLogicStmt(h.ast.fst, h.ast.snd, nilGoal()); }
  action { context = closeScope(context); } -- Opened by Head_c
| h::Head_c ':-' ps::Body_c '.'
  { top.ast = ruleLogicStmt(h.ast.fst, h.ast.snd, foldGoal(ps.ast)); }
  action { context = closeScope(context); } -- Opened by Head_c

closed tracked nonterminal Head_c with ast<Pair<Name LogicExprs>>;

concrete productions top::Head_c
| id::Identifier_c LParen_t le::LogicExprs_c ')'
  { top.ast = (id.ast, foldLogicExpr(le.ast)); }
  action {
    local templateParams::[Pair<String TerminalId>] =
      fromMaybe([], lookup(id.ast.name, predicateTemplateParams));
    -- Open a new scope containing templateParams
    context = (templateParams ++ head(context)) :: context;
    context = addIdentsToScope(le.declaredIdents, Identifier_t, context);
  }
| id::Identifier_c LParen_t ')'
  { top.ast = (id.ast, nilLogicExpr()); }
  action {
    local templateParams::[Pair<String TerminalId>] =
      fromMaybe([], lookup(id.ast.name, predicateTemplateParams));
    -- Open a new scope containing templateParams
    context = (templateParams ++ head(context)) :: context;
  }

closed tracked nonterminal Body_c with ast<[Goal]>;

concrete productions top::Body_c
| h::Goal_c ',' t::Body_c
  { top.ast = h.ast :: t.ast; }
| h::Goal_c
  { top.ast = [h.ast]; }

closed tracked nonterminal Goal_c with ast<Goal>;

concrete productions top::Goal_c
| id::Identifier_c LessThan_t tas::TemplateArguments_c '>' LParen_t les::LogicExprs_c ')'
  { top.ast = predicateGoal(id.ast, tas.ast, foldLogicExpr(les.ast)); }
  action { context = addIdentsToScope(les.declaredIdents, Identifier_t, context); }
| id::Identifier_c LessThan_t tas::TemplateArguments_c '>' LParen_t ')'
  { top.ast = predicateGoal(id.ast, tas.ast, nilLogicExpr()); }
| id::Identifier_c LParen_t les::LogicExprs_c ')'
  { top.ast = inferredPredicateGoal(id.ast, foldLogicExpr(les.ast)); }
  action { context = addIdentsToScope(les.declaredIdents, Identifier_t, context); }
| id::Identifier_c LParen_t ')'
  { top.ast = inferredPredicateGoal(id.ast, nilLogicExpr()); }
| le::LogicExpr_c 'is' e::PrologPrimaryExpr_c
  { top.ast = isGoal(le.ast, e.ast); }
  action { context = addIdentsToScope(le.declaredIdents, Identifier_t, context); }
| le1::LogicExpr_c '=' le2::LogicExpr_c
  { top.ast = equalsGoal(le1.ast, le2.ast); }
  action { context = addIdentsToScope(le1.declaredIdents ++ le2.declaredIdents, Identifier_t, context); }
| le1::LogicExpr_c '\=' le2::LogicExpr_c
  { top.ast = notEqualsGoal(le1.ast, le2.ast); }
| e1::PrologPrimaryExpr_c '=:=' e2::PrologPrimaryExpr_c
  { top.ast = eqGoal(e1.ast, e2.ast); }
| e1::PrologPrimaryExpr_c '=\=' e2::PrologPrimaryExpr_c
  { top.ast = neqGoal(e1.ast, e2.ast); }
| e1::PrologPrimaryExpr_c PLessThan_t e2::PrologPrimaryExpr_c
  { top.ast = ltGoal(e1.ast, e2.ast); }
| e1::PrologPrimaryExpr_c '=<' e2::PrologPrimaryExpr_c
  { top.ast = eltGoal(e1.ast, e2.ast); }
| e1::PrologPrimaryExpr_c '>' e2::PrologPrimaryExpr_c
  { top.ast = gtGoal(e1.ast, e2.ast); }
| e1::PrologPrimaryExpr_c '>=' e2::PrologPrimaryExpr_c
  { top.ast = gteGoal(e1.ast, e2.ast); }
| '\+' g::Goal_c
  { top.ast = notGoal(g.ast); }
| Not_t
  { top.ast = cutGoal(); }
| 'initially' '{' s::BlockItemList_c '}'
  { top.ast = initiallyGoal(foldStmt(s.ast)); }
| 'initially' '{' '}'
  { top.ast = initiallyGoal(nullStmt()); }
| 'finally' '{' s::BlockItemList_c '}'
  { top.ast = finallyGoal(foldStmt(s.ast)); }
| 'finally' '{' '}'
  { top.ast = finallyGoal(nullStmt()); }

closed tracked nonterminal LogicExprs_c with ast<[LogicExpr]>, declaredIdents;

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

closed tracked nonterminal LogicExpr_c with ast<LogicExpr>, declaredIdents;

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
      then wildcardLogicExpr()
      else nameLogicExpr(fromId(id));
    top.declaredIdents = [fromId(id)];
  }
| c::PrologConstant_c
  { top.ast = constLogicExpr(c.ast); }
| '-' c::PrologConstant_c
  { top.ast = constLogicExpr(negativeExpr(c.ast)); }
| sc::StringConstant_t
  { top.ast = constLogicExpr(stringLiteral(sc.lexeme)); }
| id::Identifier_c LParen_t le::LogicExprs_c ')'
  {
    top.ast = constructorLogicExpr(id.ast, foldLogicExpr(le.ast));
    top.declaredIdents = le.declaredIdents;
  }
| id::Identifier_c LParen_t ')'
  { top.ast = constructorLogicExpr(id.ast, nilLogicExpr()); }
-- Seed follow set with some extra terminals useful for extensions,
-- such as Prolog lists
| LogicExprNEVER_t LogicExpr_c ']'
  { top.ast = error("shouldn't occur in parse tree!"); }
| LogicExprNEVER_t LogicExpr_c '|'
  { top.ast = error("shouldn't occur in parse tree!"); }

-- Needed due to MDA
tracked nonterminal PrologPrimaryExpr_c with ast<Expr>;

concrete productions top::PrologPrimaryExpr_c
| id::Identifier_t
    { top.ast = directRefExpr(fromId(id)); }
| c::PrologConstant_c
    { top.ast = c.ast; }
| sc::StringConstant_t
    { top.ast = stringLiteral(sc.lexeme); }
| LParen_t e::Expr_c  ')'
    { top.ast = parenExpr(e.ast); }

tracked nonterminal PrologConstant_c with ast<Expr>;

concrete productions top::PrologConstant_c
-- dec
| c::DecConstant_t
    { top.ast = realConstant(integerConstant(c.lexeme, false, noIntSuffix())); }
| c::DecConstantU_t
    { top.ast = realConstant(integerConstant(c.lexeme, true, noIntSuffix())); }
| c::DecConstantL_t
    { top.ast = realConstant(integerConstant(c.lexeme, false, longIntSuffix())); }
| c::DecConstantUL_t
    { top.ast = realConstant(integerConstant(c.lexeme, true, longIntSuffix())); }
| c::DecConstantLL_t
    { top.ast = realConstant(integerConstant(c.lexeme, false, longLongIntSuffix())); }
| c::DecConstantULL_t
    { top.ast = realConstant(integerConstant(c.lexeme, true, longLongIntSuffix())); }
-- oct
| c::OctConstant_t
    { top.ast = realConstant(octIntegerConstant(c.lexeme, false, noIntSuffix())); }
| c::OctConstantU_t
    { top.ast = realConstant(integerConstant(c.lexeme, true, noIntSuffix())); }
| c::OctConstantL_t
    { top.ast = realConstant(integerConstant(c.lexeme, false, longIntSuffix())); }
| c::OctConstantUL_t
    { top.ast = realConstant(integerConstant(c.lexeme, true, longIntSuffix())); }
| c::OctConstantLL_t
    { top.ast = realConstant(integerConstant(c.lexeme, false, longLongIntSuffix())); }
| c::OctConstantULL_t
    { top.ast = realConstant(integerConstant(c.lexeme, true, longLongIntSuffix())); }
| c::OctConstantError_t
    { top.ast = errorExpr([errFromOrigin(top, "Erroneous octal constant: " ++ c.lexeme)]); }
-- hex
| c::HexConstant_t
    { top.ast = realConstant(hexIntegerConstant(c.lexeme, false, noIntSuffix())); }
| c::HexConstantU_t
    { top.ast = realConstant(hexIntegerConstant(c.lexeme, true, noIntSuffix())); }
| c::HexConstantL_t
    { top.ast = realConstant(hexIntegerConstant(c.lexeme, false, longIntSuffix())); }
| c::HexConstantUL_t
    { top.ast = realConstant(hexIntegerConstant(c.lexeme, true, longIntSuffix())); }
| c::HexConstantLL_t
    { top.ast = realConstant(hexIntegerConstant(c.lexeme, false, longLongIntSuffix())); }
| c::HexConstantULL_t
    { top.ast = realConstant(hexIntegerConstant(c.lexeme, true, longLongIntSuffix())); }
-- floats
| c::FloatConstant_t
    { top.ast = realConstant(floatConstant(c.lexeme, doubleFloatSuffix())); }
| c::FloatConstantFloat_t
    { top.ast = realConstant(floatConstant(c.lexeme, floatFloatSuffix())); }
| c::FloatConstantLongDouble_t
    { top.ast = realConstant(floatConstant(c.lexeme, longDoubleFloatSuffix())); }
-- hex floats
| c::HexFloatConstant_t
    { top.ast = realConstant(hexFloatConstant(c.lexeme, doubleFloatSuffix())); }
| c::HexFloatConstantFloat_t
    { top.ast = realConstant(hexFloatConstant(c.lexeme, floatFloatSuffix())); }
| c::HexFloatConstantLongDouble_t
    { top.ast = realConstant(hexFloatConstant(c.lexeme, longDoubleFloatSuffix())); }
-- characters
| c::CharConstant_t
    { top.ast = characterConstant(c.lexeme, noCharPrefix()); }
| c::CharConstantL_t
    { top.ast = characterConstant(c.lexeme, wcharCharPrefix()); }
| c::CharConstantU_t
    { top.ast = characterConstant(c.lexeme, char16CharPrefix()); }
| c::CharConstantUBig_t
    { top.ast = characterConstant(c.lexeme, char32CharPrefix()); }
