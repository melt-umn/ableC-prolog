grammar edu:umn:cs:melt:exts:ableC:prolog:abstractsyntax;

synthesized attribute instTypereps::([Type] ::= [Type]);

nonterminal PredicateDecl with location, env, pp, errors, defs, paramNames, typereps, instTypereps, transform<Decl>, ruleTransformIn, substitutions, substituted<PredicateDecl>;

abstract production predicateDecl
top::PredicateDecl ::= n::Name typeParams::Names params::Parameters
{
  propagate substituted;
  top.pp = pp"${n.pp}<${ppImplode(text(", "), typeParams.pps)}>(${ppImplode(pp", ", params.pps)});";
  top.errors := params.errors;
  top.defs := predicateDef(n.name, predicateItem(top)) :: params.defs;
  top.paramNames = params.paramNames;
  top.typereps = params.typereps;
  top.instTypereps =
    \ ts::[Type] ->
      decorate params with {
        env = addEnv(typeParamInstDefs(ts, typeParams), openScopeEnv(top.env));
        returnType = nothing();
        position = 0;
      }.typereps;
  
  params.env = addEnv(typeParams.typeParamDefs, openScopeEnv(top.env));
  params.returnType = nothing();
  params.position = 0;
  
  top.errors <- n.predicateRedeclarationCheck;
  top.errors <- typeParams.typeParameterErrors;
  top.errors <- params.unifyErrors(top.location, top.env);
  
  top.transform =
    ableC_Decl {
      proto_typedef unification_trail;
      template<$Names{typeParams}>
      _Bool $Name{n}($Parameters{params}, closure<() -> _Bool> _continuation) {
        unification_trail _trail = new_trail();
        
        $Stmt{foldStmt(lookupAllBy(stringEq, n.name, top.ruleTransformIn))}
        
        delete _trail;
        return 0;
      }
    };
}

synthesized attribute typeParamDefs::[Def] occurs on Names, Name;
synthesized attribute typeParamInstDefs::[Def] occurs on Names, Name;
inherited attribute instParamTypes::[Type] occurs on Names;

aspect production consName
top::Names ::= h::Name t::Names
{
  top.typeParamDefs = h.typeParamDefs ++ t.typeParamDefs;
  top.typeParamInstDefs = h.typeParamInstDefs ++ t.typeParamInstDefs;
  
  local splitTypes :: Pair<Type [Type]> =
    case top.instParamTypes of
    | t::ts -> pair(t, ts)
    | [] -> pair(errorType(), [])
    end;
  h.instParamType = splitTypes.fst;
  t.instParamTypes = splitTypes.snd;
}

aspect production nilName
top::Names ::=
{
  top.typeParamDefs = [];
  top.typeParamInstDefs = [];
}

function typeParamInstDefs
[Def] ::= ts::[Type] ns::Names
{
  ns.instParamTypes = ts;
  return ns.typeParamInstDefs;
}

inherited attribute instParamType::Type occurs on Name;

aspect production name
top::Name ::= n::String
{
  top.typeParamDefs =
    [valueDef(n, typeParamValueItem(extType(nilQualifier(), typeVarType(n)), top.location))];
  top.typeParamInstDefs = [valueDef(n, typeParamValueItem(top.instParamType, top.location))];
}

synthesized attribute paramNames::[String] occurs on Parameters;
attribute transform<Parameters> occurs on Parameters;

aspect production consParameters
top::Parameters ::= h::ParameterDecl t::Parameters
{
  propagate transform;
  top.paramNames = h.paramName :: t.paramNames;
}

aspect production nilParameters
top::Parameters ::= 
{
  propagate transform;
  top.paramNames = [];
}

synthesized attribute paramName::String occurs on ParameterDecl;
attribute transform<ParameterDecl> occurs on ParameterDecl;

aspect production parameterDecl
top::ParameterDecl ::= storage::StorageClasses  bty::BaseTypeExpr  mty::TypeModifierExpr  n::MaybeName  attrs::Attributes
{
  production paramName::Name =
    case n of
    | justName(n) -> n
    | nothingName() -> name("p" ++ toString(top.position), location=builtin)
    end;
  top.paramName = paramName.name;
  top.transform = parameterDecl(storage, bty, mty, justName(paramName), attrs);
}
