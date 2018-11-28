grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

synthesized attribute typeParams::Decorated Names;
synthesized attribute instTypereps::([Type] ::= [Type]);

nonterminal PredicateDecl with location, env, pp, errors, defs, errorDefs, paramNames, typereps, typeParams, instTypereps, transform<Decls>, ruleTransformIn, substitutions, substituted<PredicateDecl>;
flowtype PredicateDecl = decorate {env, ruleTransformIn}, pp {}, errors {decorate}, defs {decorate}, typereps {decorate}, typeParams {decorate}, instTypereps {decorate}, transform {decorate}, substituted {substitutions};

abstract production predicateDecl
top::PredicateDecl ::= n::Name typeParams::Names params::Parameters
{
  propagate substituted;
  top.pp = pp"${n.pp}<${ppImplode(text(", "), typeParams.pps)}>(${ppImplode(pp", ", params.pps)});";
  top.errors := params.errors;
  top.defs := params.defs;
  top.errorDefs := top.defs;
  top.paramNames = params.paramNames;
  top.typereps = params.typereps;
  top.typeParams = typeParams;
  top.instTypereps =
    \ ts::[Type] ->
      map(
        \ t::Type -> t.canonicalType,
        decorate params with {
          -- Add type args to global scope so that they are visible within the template instantiation
          env = addEnv([globalDefsDef(typeParamInstDefs(ts, typeParams))], openScopeEnv(top.env));
          returnType = nothing();
          position = 0;
        }.typereps);
  
  local predicateDefs::[Def] = [predicateDef(n.name, predicateItem(top))];
  top.defs <- predicateDefs;
  
  local transName::String = s"_predicate_${n.name}";
  top.errorDefs <- [templateDef(transName, errorTemplateItem())];
  
  -- Add type params to global scope so that they are visible within the template instantiation
  params.env = addEnv([globalDefsDef(typeParams.typeParamDefs)], openScopeEnv(top.env));
  params.returnType = nothing();
  params.position = 0;
  
  top.errors <- n.predicateRedeclarationCheck;
  top.errors <- typeParams.typeParameterErrors;
  top.errors <- params.unifyErrors(top.location, addEnv(params.defs, params.env));
  
  top.transform =
    ableC_Decls {
      proto_typedef unification_trail;
      template<$Names{typeParams}>
      _Bool $name{transName}($Parameters{params.transform}, closure<() -> _Bool> _continuation) {
        unification_trail _trail = new_trail();
        
        $Stmt{foldStmt(lookupAllBy(stringEq, n.name, top.ruleTransformIn))}
        
        delete _trail;
        return 0;
      }
      $Decl{defsDecl(predicateDefs)}
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
    [valueDef(n, typeParamValueItem(extType(nilQualifier(), typeParamType(n)), top.location))];
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
