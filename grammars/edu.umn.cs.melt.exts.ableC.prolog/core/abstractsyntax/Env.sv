grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

import silver:util:raw:treemap as tm;

abstract production typeParamValueItem
top::ValueItem ::= t::Type loc::Location
{
  top.pp = pp"type param";
  top.typerep = t;
  top.sourceLocation = loc;
  top.isItemType = true;
}

abstract production varValueItem
top::ValueItem ::= t::Type loc::Location
{
  top.pp = pp"var";
  top.typerep = t;
  top.sourceLocation = loc;
  top.isItemValue = true;
}

-- Generate defs for "unwrapped" values corresponding to variables referenced
-- in "is" predicate expression.
function makeUnwrappedVarDefs
[Def] ::= env::Decorated Env
{
  return
    flatMap(
      \ p::Pair<String ValueItem> ->
        case p of
        | pair(n, varValueItem(t, l)) -> [valueDef(n, varValueItem(varSubType(t), l))]
        | _ -> []
        end,
      tm:toList(head(env.values)));
}

closed nonterminal PredicateItem with paramNames, typereps, typeParams, instTypereps, sourceLocation;

abstract production predicateItem
top::PredicateItem ::= d::Decorated PredicateDecl
{
  top.paramNames = d.paramNames;
  top.typereps = d.typereps;
  top.typeParams = d.typeParams;
  top.instTypereps = d.instTypereps;
  top.sourceLocation = d.location;
}

abstract production errorPredicateItem
top::PredicateItem ::= 
{
  top.paramNames = [];
  top.typereps = [];
  top.typeParams = decorate nilName() with { env = emptyEnv(); };
  top.instTypereps = \ [Type] -> [];
  top.sourceLocation = loc("nowhere", -1, -1, -1, -1, -1, -1);
}

synthesized attribute predicates::Scopes<PredicateItem> occurs on Env;
synthesized attribute predicateContribs::Contribs<PredicateItem> occurs on Defs, Def;

aspect production emptyEnv_i
top::Env ::=
{
  top.predicates = emptyScope();
}
aspect production addEnv_i
top::Env ::= d::Defs  e::Decorated Env
{
  top.predicates = addGlobalScope(gd.predicateContribs, addScope(d.predicateContribs, e.predicates));
}
aspect production openScopeEnv_i
top::Env ::= e::Decorated Env
{
  top.predicates = openScope(e.predicates);
}
aspect production globalEnv_i
top::Env ::= e::Decorated Env
{
  top.predicates = globalScope(e.predicates);
}
aspect production nonGlobalEnv_i
top::Env ::= e::Decorated Env
{
  top.predicates = nonGlobalScope(e.predicates);
}

aspect production nilDefs
top::Defs ::=
{
  top.predicateContribs = [];
}
aspect production consDefs
top::Defs ::= h::Def  t::Defs
{
  top.predicateContribs = h.predicateContribs ++ t.predicateContribs;
}

aspect default production
top::Def ::=
{
  top.predicateContribs = [];
}

abstract production predicateDef
top::Def ::= s::String  t::PredicateItem
{
  top.predicateContribs = [pair(s, t)];
}

function lookupPredicate
[PredicateItem] ::= n::String  e::Decorated Env
{
  return lookupScope(n, e.predicates);
}

function lookupPredicateInLocalScope
[PredicateItem] ::= n::String  e::Decorated Env
{
  return lookupScope(n, e.predicates);
}

synthesized attribute predicateItem::Decorated PredicateItem occurs on Name;
synthesized attribute predicateLookupCheck::[Message] occurs on Name;
synthesized attribute predicateLocalLookupCheck::[Message] occurs on Name;
synthesized attribute predicateRedeclarationCheck::[Message] occurs on Name;

aspect production name
top::Name ::= n::String
{
  local predicates::[PredicateItem] = lookupPredicate(n, top.env);
  top.predicateLookupCheck =
    case predicates of
    | [] -> [err(top.location, "Undeclared predicate " ++ n)]
    | _ :: _ -> []
    end;
  top.predicateLocalLookupCheck =
    case lookupPredicateInLocalScope(n, top.env), predicates of
    | _ :: _, _ -> []
    | [], _ :: _ -> [err(top.location, "Predicate " ++ n ++ " not in current declaration block")]
    | [], [] -> [err(top.location, "Undeclared predicate " ++ n)]
    end;
    
  top.predicateRedeclarationCheck =
    case predicates of
    | [] -> []
    | v :: _ ->
      [err(top.location, 
          "Redeclaration of " ++ n ++ ". Original (from line " ++
          toString(v.sourceLocation.line) ++ ")")]
    end;
  
  local predicate::PredicateItem = if null(predicates) then errorPredicateItem() else head(predicates);
  top.predicateItem = predicate;
}