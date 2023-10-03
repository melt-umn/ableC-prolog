grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

import silver:util:treemap as tm;

-- Represents a type parameter
abstract production templateParamValueItem
top::ValueItem ::= t::Type isTypeParam::Boolean
{
  top.pp = pp"type param";
  top.typerep = t;
  top.isItemType = isTypeParam;
  top.isItemValue = !isTypeParam;
}

-- Represents a unification variable
abstract production varValueItem
top::ValueItem ::= t::Type
{
  top.pp = pp"var";
  top.typerep = t;
  top.isItemValue = true;
}

-- Wraps another ValueItem and canonicalizes its type
abstract production canonicalValueItem
top::ValueItem ::= v::ValueItem
{
  top.pp = pp"canonical ${v.pp}";
  top.typerep = v.typerep.canonicalType;
  top.directRefHandler = v.directRefHandler;
  top.directCallHandler = v.directCallHandler;
  top.isItemValue = v.isItemValue;
  top.isItemType = v.isItemType;
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
        | (n, varValueItem(t)) -> [valueDef(n, varValueItem(varSubType(t)))]
        | _ -> []
        end,
      tm:toList(head(env.values)));
}

closed tracked nonterminal PredicateItem with paramNames, typereps, templateParams, params, functionDefs, labelDefs;

abstract production predicateItem
top::PredicateItem ::= d::Decorated PredicateDecl
{
  top.paramNames = d.paramNames;
  top.typereps = d.typereps;
  top.templateParams = d.templateParams;
  top.params = d.params;
  top.functionDefs := d.functionDefs;
  top.labelDefs := d.labelDefs;
}

abstract production errorPredicateItem
top::PredicateItem ::= 
{
  top.paramNames = [];
  top.typereps = [];
  top.templateParams = nilTemplateParameter();
  top.params = nilParameters();
  top.functionDefs := [];
  top.labelDefs := [];
}

synthesized attribute predicates::Scopes<PredicateItem> occurs on Env;

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
aspect production functionEnv_i
top::Env ::= e::Decorated Env
{
  top.predicates = functionScope(e.predicates);
}

synthesized attribute predicateContribs::Contribs<PredicateItem> occurs on Defs, Def;
synthesized attribute canonicalDefs::[Def] occurs on Defs, Def;

aspect production nilDefs
top::Defs ::=
{
  top.predicateContribs = [];
  top.canonicalDefs = [];
}
aspect production consDefs
top::Defs ::= h::Def  t::Defs
{
  top.predicateContribs = h.predicateContribs ++ t.predicateContribs;
  top.canonicalDefs = h.canonicalDefs ++ t.canonicalDefs;
}

aspect default production
top::Def ::=
{
  top.predicateContribs = [];
  top.canonicalDefs = [top];
}

abstract production predicateDef
top::Def ::= s::String  t::PredicateItem
{
  top.predicateContribs = [(s, t)];
}

aspect production valueDef
top::Def ::= s::String  t::ValueItem
{
  top.canonicalDefs = [valueDef(s, canonicalValueItem(t))];
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
    | [] -> [errFromOrigin(top, "Undeclared predicate " ++ n)]
    | _ :: _ -> []
    end;
  top.predicateLocalLookupCheck =
    case lookupPredicateInLocalScope(n, top.env), predicates of
    | _ :: _, _ -> []
    | [], _ :: _ -> [errFromOrigin(top, "Predicate " ++ n ++ " not in current declaration block")]
    | [], [] -> [errFromOrigin(top, "Undeclared predicate " ++ n)]
    end;
    
  top.predicateRedeclarationCheck =
    case predicates of
    | [] -> []
    | v :: _ ->
      [errFromOrigin(top, 
          "Redeclaration of " ++ n ++ ". Original (from " ++
          getParsedOriginLocationOrFallback(v).unparse ++ ")")]
    end;
  
  local predicate::PredicateItem = if null(predicates) then errorPredicateItem() else head(predicates);
  top.predicateItem = predicate;
}
