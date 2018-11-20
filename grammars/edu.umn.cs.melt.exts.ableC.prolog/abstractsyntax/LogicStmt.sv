grammar edu:umn:cs:melt:exts:ableC:prolog:abstractsyntax;

synthesized attribute transform<a>::a;
synthesized attribute ruleTransform::[Pair<String Stmt>];
inherited attribute ruleTransformIn::[Pair<String Stmt>];

nonterminal LogicStmts with  pps, errors, defs, env, ruleTransform, substituted<LogicStmts>;

abstract production consLogicStmt
top::LogicStmts ::= h::LogicStmt t::LogicStmts
{
  propagate substituted;
  top.pps = h.pp :: t.pps;
  top.errors := h.errors ++ t.errors;
  top.ruleTransform = h.ruleTransform ++ t.ruleTransform;
  h.ruleTransformIn = t.ruleTransform;
}

abstract production nilLogicStmt
top::LogicStmts ::=
{
  propagate substituted;
  top.pps = [];
  top.errors := [];
  top.ruleTransform = [];
}


nonterminal LogicStmt with location, pp, errors, defs, env, ruleTransform, ruleTransformIn, substituted<LogicStmt>;

abstract production ruleLogicStmt
top::LogicStmt ::= n::Name les::LogicExprs ps::Predicates
{
  propagate substituted;
  top.pp = pp"${n.pp}(${ppImplode(pp", ", les.pps)})${if null(ps.pps) then pp"." else pp" :- ${ppImplode(pp", ", ps.pps)}"}";
  top.errors := les.errors ++ ps.errors; -- TODO: Lookup check in local scope
  top.ruleTransform =
    [pair(
       n.name,
       ableC_Stmt {
         // New scope containing the allocated variables
         {
           // Declare and initialize variables
           $Stmt{
             foldStmt(
               catMaybes(
                 map(
                   \ item::Pair<String ValueItem> ->
                     case item.snd of
                     | varValueItem(_, _) ->
                       just(
                         mkDecl(
                           item.fst, item.snd.typerep,
                           freeVarExpr(
                             typeName(directTypeExpr(item.snd.typerep), baseTypeExpr()),
                             ableC_Expr { alloca },
                             location=builtin),
                           builtin))
                     | _ -> nothing()
                     end,
                   foldr(consDefs, nilDefs(), les.defs ++ ps.defs).valueContribs)))}
           // Unify each argument expression on the LHS with each parameter value
           // If successful, evaluate the RHS 
           if ($Expr{les.paramUnifyTransform} && $Expr{ps.transform}) {
             // Search has succeeded, so we are done immediately
             delete _trail;
             return 1;
           }
           // This branch of the search failed, undo the effects of the above unifications
           undo_trail(_trail);
         }
       })];
}

abstract production declLogicStmt
top::LogicStmt ::= d::PredicateDecl
{
  propagate substituted;
  top.pp = d.pp;
  top.errors := d.errors;
  top.defs := d.defs;
  d.ruleTransformIn = top.ruleTransformIn;
}
