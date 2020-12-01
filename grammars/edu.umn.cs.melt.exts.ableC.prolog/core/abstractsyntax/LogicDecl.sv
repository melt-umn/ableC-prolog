grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

abstract production logicDecl
top::Decl ::= lss::LogicStmts loc::Location
{
  top.pp = pp"prolog ${braces(nestlines(2, terminate(line(), lss.pps)))}";
  
  -- Logic decls are *type checked* in a new scope to distinguish currently specifiable predicates,
  -- but defs are inserted at the global scope via defsDecl.
  lss.env = openScopeEnv(top.env);
  
  local localErrors::[Message] =
    lss.errors ++
    if !top.isTopLevel
    then [err(loc, "Logic declarations must be global")]
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

synthesized attribute transform<a>::a;
synthesized attribute ruleTransform::[Pair<String Stmt>];
inherited attribute ruleTransformIn::[Pair<String Stmt>];

nonterminal LogicStmts with pps, errors, errorDefs, env, coveredPatterns, predicateGoalCondParams, transform<Decls>, ruleTransform;
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
  
  top.transform = appendDecls(h.transform, t.transform);
  top.ruleTransform = h.ruleTransform ++ t.ruleTransform;
  h.ruleTransformIn = t.ruleTransform;
  t.env = addEnv(h.defs, h.env);
}

abstract production nilLogicStmt
top::LogicStmts ::=
{
  top.pps = [];
  top.coveredPatterns = [];
  top.predicateGoalCondParams = [];
  top.transform = nilDecl();
  top.ruleTransform = [];
}

nonterminal LogicStmt with location, pp, errors, defs, errorDefs, env, coveredPatterns, coveredPatternsIn, predicateGoalCondParams, predicateGoalCondParamsIn, transform<Decls>, ruleTransform, ruleTransformIn;
flowtype LogicStmt = decorate {env, coveredPatternsIn, predicateGoalCondParamsIn, ruleTransformIn}, pp {}, errors {decorate}, defs {decorate}, errorDefs {decorate}, coveredPatterns {decorate}, predicateGoalCondParams {decorate}, transform {decorate}, ruleTransform {decorate};

abstract production ruleLogicStmt
top::LogicStmt ::= n::Name les::LogicExprs gs::Goals
{
  propagate errors;
  top.pp = pp"${n.pp}(${ppImplode(pp", ", les.pps)})${if null(gs.pps) then pp"." else pp" :- ${ppImplode(pp", ", gs.pps)}"}";
  top.defs := [];
  top.errorDefs := [];
  
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
  gs.lastGoalCond =
    unionsBy(
      \ e1::[String] e2::[String] -> all(zipWith(stringEq, e1, e2)),
      map(
        \ les1::LogicExprs -> decorate les1 with {
            env = les.env; expectedTypes = les.expectedTypes; allowUnificationTypes = true;
            isExcludableBy = les; paramNamesIn = les.paramNamesIn;}.isExcludable,
        lookupAllBy(stringEq, n.name, top.coveredPatternsIn)));
  gs.tailCallPermitted = true;
  
  top.errors <- n.predicateLocalLookupCheck;
  top.errors <-
    if null(n.predicateLookupCheck) && les.count != length(les.expectedTypes)
    then [err(top.location, s"Wrong number of arguments to predicate ${n.name} (expected ${toString(length(les.expectedTypes))}, got ${toString(les.count)})")]
    else [];
  
  top.coveredPatterns = [pair(n.name, les)];
  top.predicateGoalCondParams = [pair(n.name, gs.goalCondParams)];
  
  top.transform = nilDecl();
  top.ruleTransform =
    [pair(
       n.name,
       ableC_Stmt {
         // New scope containing the allocated variables
         {
           // Declare and initialize variables
           $Stmt{makeVarDecls(les.defs ++ gs.defs)}
           // Unify each argument expression on the LHS with each parameter value
           // If successful, evaluate the RHS
           if ($Expr{les.paramUnifyTransform} && $Expr{gs.transform}) {
             // Search has succeeded, so we are done immediately
             return 1;
           }
         }
       })];
   gs.continuationTransformIn = ableC_Expr { _continuation };
}

abstract production declLogicStmt
top::LogicStmt ::= d::PredicateDecl
{
  propagate errors, defs, errorDefs;
  top.pp = d.pp;
  top.transform = d.transform;
  top.coveredPatterns = [];
  top.predicateGoalCondParams = [];
  d.predicateGoalCondParamsIn = top.predicateGoalCondParamsIn;
  top.ruleTransform = [];
  d.ruleTransformIn = top.ruleTransformIn;
}
