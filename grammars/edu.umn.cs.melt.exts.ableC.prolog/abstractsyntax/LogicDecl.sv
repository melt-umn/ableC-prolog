grammar edu:umn:cs:melt:exts:ableC:prolog:abstractsyntax;

abstract production logicDecl
top::Decl ::= lss::LogicStmts
{
  propagate substituted;
  top.pp = pp"logic ${braces(nestlines(2, terminate(line(), lss.pps)))}";
  
  lss.env = openScopeEnv(top.env);
  
  forwards to
    decls(
      if !null(lss.errors)
      then foldDecl([warnDecl(lss.errors), defsDecl(lss.errorDefs)])
      else lss.transform);
}

synthesized attribute transform<a>::a;
synthesized attribute ruleTransform::[Pair<String Stmt>];
inherited attribute ruleTransformIn::[Pair<String Stmt>];

synthesized attribute errorDefs::[Def] with ++;

nonterminal LogicStmts with pps, errors, errorDefs, env, transform<Decls>, ruleTransform, substitutions, substituted<LogicStmts>;
flowtype LogicStmts = decorate {env}, pps {}, errors {decorate}, errorDefs {decorate}, transform {decorate}, ruleTransform {decorate}, substituted {substitutions};

abstract production consLogicStmt
top::LogicStmts ::= h::LogicStmt t::LogicStmts
{
  propagate substituted;
  top.pps = h.pp :: t.pps;
  top.errors := h.errors ++ t.errors;
  top.errorDefs := h.errorDefs ++ t.errorDefs;
  top.transform = appendDecls(h.transform, t.transform);
  top.ruleTransform = h.ruleTransform ++ t.ruleTransform;
  h.ruleTransformIn = t.ruleTransform;
  t.env = addEnv(h.defs, h.env);
}

abstract production nilLogicStmt
top::LogicStmts ::=
{
  propagate substituted;
  top.pps = [];
  top.errors := [];
  top.errorDefs := [];
  top.transform = nilDecl();
  top.ruleTransform = [];
}

nonterminal LogicStmt with location, pp, errors, defs, errorDefs, env, transform<Decls>, ruleTransform, ruleTransformIn, substitutions, substituted<LogicStmt>;
flowtype LogicStmt = decorate {env, ruleTransformIn}, pp {}, errors {decorate}, defs {decorate}, errorDefs {decorate}, transform {decorate}, ruleTransform {decorate}, substituted {substitutions};

abstract production ruleLogicStmt
top::LogicStmt ::= n::Name les::LogicExprs ps::Predicates
{
  propagate substituted;
  top.pp = pp"${n.pp}(${ppImplode(pp", ", les.pps)})${if null(ps.pps) then pp"." else pp" :- ${ppImplode(pp", ", ps.pps)}"}";
  top.errors := les.errors ++ ps.errors;
  top.defs := [];
  top.errorDefs := [];
  
  les.env = addEnv([globalDefsDef(n.predicateItem.typeParams.typeParamDefs)], openScopeEnv(top.env));
  les.paramNamesIn = n.predicateItem.paramNames;
  les.expectedTypes = n.predicateItem.typereps;
  les.allowUnificationTypes = true;
  les.allocator = ableC_Expr { alloca };
  ps.env = addEnv(les.defs, les.env);
  
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
           $Stmt{makeVarDecls(les.defs ++ ps.defs)}
           // Unify each argument expression on the LHS with each parameter value
           // If successful, evaluate the RHS
           if ($Expr{les.paramUnifyTransform} && $Expr{ps.transform}) {
             // Search has succeeded, so we are done immediately
             undo_trail(_trail);
             delete _trail;
             return 1;
           }
           // This branch of the search failed, undo the effects of the above unifications
           undo_trail(_trail);
         }
       })];
   ps.continuationTransformIn = ableC_Expr { _continuation };
}

abstract production declLogicStmt
top::LogicStmt ::= d::PredicateDecl
{
  propagate substituted;
  top.pp = d.pp;
  top.errors := d.errors;
  top.defs := d.defs;
  top.errorDefs := d.errorDefs;
  top.transform = d.transform;
  top.ruleTransform = [];
  d.ruleTransformIn = top.ruleTransformIn;
}
