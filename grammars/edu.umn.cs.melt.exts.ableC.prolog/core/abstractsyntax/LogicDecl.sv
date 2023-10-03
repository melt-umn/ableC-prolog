grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

import silver:util:treeset as ts;

abstract production logicDecl
top::Decl ::= lss::LogicStmts
{
  top.pp = pp"prolog ${braces(nestlines(2, terminate(line(), lss.pps)))}";
  
  -- Logic decls are *type checked* in a new scope to distinguish currently specifiable predicates,
  -- but defs are inserted at the global scope via defsDecl.
  lss.env = openScopeEnv(top.env);
  
  local localErrors::[Message] =
    lss.errors ++
    if !top.isTopLevel
    then [errFromOrigin(top, "Logic declarations must be global")]
    else [];
  
  forwards to
    decls(
      if !null(localErrors)
      then consDecl(
        warnDecl(localErrors),
        if containsErrors(localErrors, false)
        then foldDecl([defsDecl(lss.errorDefs)])
        else lss.transform)
      else lss.transform);
}

monoid attribute errorDefs::[Def] with [], ++;

synthesized attribute coveredPatterns::[Pair<String LogicExprs>];
inherited attribute coveredPatternsIn::[Pair<String LogicExprs>];

synthesized attribute predicateGoalCondParams::[Pair<String [String]>];
inherited attribute predicateGoalCondParamsIn::[Pair<String [String]>];

synthesized attribute cutPredicates::[String];
inherited attribute cutPredicatesIn::[String];

synthesized attribute transform<a>::a;
synthesized attribute ruleTransform::[Pair<String Stmt>];
inherited attribute ruleTransformIn::[Pair<String Stmt>];

tracked nonterminal LogicStmts with pps, errors, errorDefs, env, coveredPatterns, predicateGoalCondParams, cutPredicates, transform<Decls>, ruleTransform;
flowtype LogicStmts = decorate {env}, pps {}, errors {decorate}, errorDefs {decorate}, coveredPatterns {decorate}, predicateGoalCondParams {decorate}, transform {decorate}, ruleTransform {decorate};

propagate errors, errorDefs on LogicStmts;

abstract production consLogicStmt
top::LogicStmts ::= h::LogicStmt t::LogicStmts
{
  top.pps = h.pp :: t.pps;
  top.coveredPatterns = h.coveredPatterns ++ t.coveredPatterns;
  h.coveredPatternsIn = t.coveredPatterns;
  
  top.predicateGoalCondParams = h.predicateGoalCondParams ++ t.predicateGoalCondParams;
  h.predicateGoalCondParamsIn = t.predicateGoalCondParams;
  
  top.cutPredicates = union(h.cutPredicates, t.cutPredicates);
  h.cutPredicatesIn = t.cutPredicates;
  
  top.transform = appendDecls(h.transform, t.transform);
  top.ruleTransform = h.ruleTransform ++ t.ruleTransform;
  h.ruleTransformIn = t.ruleTransform;
  h.env = top.env;
  t.env = addEnv(h.defs, h.env);
}

abstract production nilLogicStmt
top::LogicStmts ::=
{
  top.pps = [];
  top.coveredPatterns = [];
  top.predicateGoalCondParams = [];
  top.cutPredicates = [];
  top.transform = nilDecl();
  top.ruleTransform = [];
}

tracked nonterminal LogicStmt with pp, errors, defs, errorDefs, env, coveredPatterns, coveredPatternsIn, predicateGoalCondParams, predicateGoalCondParamsIn, cutPredicates, cutPredicatesIn, transform<Decls>, ruleTransform, ruleTransformIn;
flowtype LogicStmt = decorate {env, coveredPatternsIn, predicateGoalCondParamsIn, cutPredicatesIn, ruleTransformIn}, pp {}, errors {decorate}, defs {decorate}, errorDefs {decorate}, coveredPatterns {decorate}, predicateGoalCondParams {decorate}, transform {decorate}, ruleTransform {decorate};

propagate errors on LogicStmt;

abstract production ruleLogicStmt
top::LogicStmt ::= n::Name les::LogicExprs gs::Goals
{
  top.pp = pp"${n.pp}(${ppImplode(pp", ", les.pps)})${if null(gs.pps) then pp"." else pp" :- ${ppImplode(pp", ", gs.pps)}"}";
  top.defs := [];
  top.errorDefs := [];

  n.env = top.env;
  
  local templateParams::TemplateParameters = n.predicateItem.templateParams;
  templateParams.templateParamEnv = globalEnv(top.env);
  les.env = addEnv(globalDefsDef(templateParams.templateParamDefs) :: n.predicateItem.functionDefs, openScopeEnv(top.env));
  les.refVariables = removeDefsFromNames(les.defs, gs.freeVariables);
  les.paramNamesIn = n.predicateItem.paramNames;
  les.expectedTypes = n.predicateItem.typereps;
  les.allowUnificationTypes = true;
  les.allocator = ableC_Expr { alloca };
  gs.env = addEnv(les.defs, openScopeEnv(les.env));
  gs.predicateName = just(n.name);
  gs.refVariables = les.refVariables;
  local lastGoalConds::[ts:Set<String>] =
    nub(
      flatMap(
        \ les1::LogicExprs -> map(
          ts:add(_, ts:empty()),
          decorate les1 with {
            env = les.env; expectedTypes = les.expectedTypes; allowUnificationTypes = true;
            isExcludableBy = les; paramNamesIn = les.paramNamesIn;}.isExcludable),
        lookupAll(n.name, top.coveredPatternsIn)));
  gs.lastGoalCond =
    map(ts:toList,
      removeAllBy(
        \ c1::ts:Set<String> c2::ts:Set<String> -> ts:subset(c2, c1) && !ts:subset(c1, c2),
        lastGoalConds, lastGoalConds));
  gs.tailCallPermitted = true;
  
  top.errors <- n.predicateLocalLookupCheck;
  top.errors <-
    if null(n.predicateLookupCheck) && les.count != length(les.expectedTypes)
    then [errFromOrigin(top, s"Wrong number of arguments to predicate ${n.name} (expected ${toString(length(les.expectedTypes))}, got ${toString(les.count)})")]
    else [];
  
  top.coveredPatterns = [(n.name, les)];
  top.predicateGoalCondParams = [(n.name, gs.goalCondParams)];
  top.cutPredicates = if gs.containsCut then [n.name] else [];
  
  top.transform = nilDecl();
  top.ruleTransform =
    [( n.name,
       ableC_Stmt {
         // New scope containing the allocated variables
         {
           // Declare and initialize variables
           $Stmt{makeVarDecls(les.defs ++ gs.defs)}
           // Unify each argument expression on the LHS with each parameter value
           // If successful, evaluate the RHS
           if ($Expr{les.paramUnifyTransform} && $Expr{gs.transform}) {
             // Search has succeeded, so we are done immediately
             undo_trail(_trail, _initial_trail_index);
             return 1;
           }
         }
       })];
   gs.continuationTransformIn = ableC_Expr { _continuation };
}

abstract production declLogicStmt
top::LogicStmt ::= d::PredicateDecl
{
  propagate env, defs, errorDefs;
  top.pp = d.pp;
  top.transform = d.transform;
  top.coveredPatterns = [];
  top.predicateGoalCondParams = [];
  d.predicateGoalCondParamsIn = top.predicateGoalCondParamsIn;
  top.cutPredicates = [];
  d.cutPredicatesIn = top.cutPredicatesIn;
  top.ruleTransform = [];
  d.ruleTransformIn = top.ruleTransformIn;
}
