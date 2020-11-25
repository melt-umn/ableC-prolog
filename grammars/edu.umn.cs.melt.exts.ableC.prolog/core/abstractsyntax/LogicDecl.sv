grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

abstract production logicDecl
top::Decl ::= lss::LogicStmts loc::Location
{
  --top.pp = pp"prolog ${braces(nestlines(2, terminate(line(), lss.pps)))}";
  
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
      then foldDecl([warnDecl(localErrors), defsDecl(lss.errorDefs)])
      else lss.transform);
}

synthesized attribute transform<a>::a;
synthesized attribute ruleTransform::[Pair<String Stmt>];
inherited attribute ruleTransformIn::[Pair<String Stmt>];

monoid attribute errorDefs::[Def] with [], ++;

nonterminal LogicStmts with pps, errors, errorDefs, env, transform<Decls>, ruleTransform;
flowtype LogicStmts = decorate {env}, pps {}, errors {decorate}, errorDefs {decorate}, transform {decorate}, ruleTransform {decorate};

propagate errors, errorDefs on LogicStmts;

abstract production consLogicStmt
top::LogicStmts ::= h::LogicStmt t::LogicStmts
{
  top.pps = h.pp :: t.pps;
  top.transform = appendDecls(h.transform, t.transform);
  top.ruleTransform = h.ruleTransform ++ t.ruleTransform;
  h.ruleTransformIn = t.ruleTransform;
  t.env = addEnv(h.defs, h.env);
}

abstract production nilLogicStmt
top::LogicStmts ::=
{
  top.pps = [];
  top.transform = nilDecl();
  top.ruleTransform = [];
}

nonterminal LogicStmt with location, pp, errors, defs, errorDefs, env, transform<Decls>, ruleTransform, ruleTransformIn;
flowtype LogicStmt = decorate {env, ruleTransformIn}, pp {}, errors {decorate}, defs {decorate}, errorDefs {decorate}, transform {decorate}, ruleTransform {decorate};

abstract production ruleLogicStmt
top::LogicStmt ::= n::Name les::LogicExprs gs::Goals
{
  propagate errors;
  top.pp = pp"${n.pp}(${ppImplode(pp", ", les.pps)})${if null(gs.pps) then pp"." else pp" :- ${ppImplode(pp", ", gs.pps)}"}";
  top.defs := [];
  top.errorDefs := [];
  
  local templateParams::TemplateParameters = n.predicateItem.templateParams;
  templateParams.templateParamEnv = globalEnv(top.env);
  les.env = addEnv([globalDefsDef(templateParams.templateParamDefs)], openScopeEnv(top.env));
  les.refVariables = removeDefsFromNames(les.defs, gs.freeVariables);
  les.paramNamesIn = n.predicateItem.paramNames;
  les.expectedTypes = n.predicateItem.typereps;
  les.allowUnificationTypes = true;
  les.allocator = ableC_Expr { alloca };
  gs.env = addEnv(les.defs, les.env);
  gs.refVariables = les.refVariables;
  
  top.errors <- n.predicateLocalLookupCheck;
  top.errors <-
    if null(n.predicateLookupCheck) && les.count != length(les.expectedTypes)
    then [err(top.location, s"Wrong number of arguments to predicate ${n.name} (expected ${toString(length(les.expectedTypes))}, got ${toString(les.count)})")]
    else [];
  
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
  top.ruleTransform = [];
  d.ruleTransformIn = top.ruleTransformIn;
}
