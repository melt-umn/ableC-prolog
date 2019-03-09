grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

synthesized attribute templateParams::TemplateParameters;
synthesized attribute params::Parameters;

nonterminal PredicateDecl with location, env, pp, errors, defs, errorDefs, paramNames, typereps, templateParams, params, transform<Decls>, ruleTransformIn, substitutions, substituted<PredicateDecl>;
flowtype PredicateDecl = decorate {env, ruleTransformIn}, pp {}, errors {decorate}, defs {decorate}, typereps {decorate}, templateParams {decorate}, params {decorate}, transform {decorate}, substituted {substitutions};

abstract production predicateDecl
top::PredicateDecl ::= n::Name templateParams::TemplateParameters params::Parameters
{
  propagate substituted;
  top.pp = pp"${n.pp}<${ppImplode(text(", "), templateParams.pps)}>(${ppImplode(pp", ", params.pps)});";
  top.errors := templateParams.errors ++ params.errors;
  top.defs := params.defs;
  top.errorDefs := top.defs;
  top.paramNames = params.paramNames;
  top.typereps = params.typereps;
  top.templateParams = templateParams;
  top.params = params;
  
  local predicateDefs::[Def] = [predicateDef(n.name, predicateItem(top))];
  top.defs <- predicateDefs;
  
  local transName::String = s"_predicate_${n.name}";
  top.errorDefs <- [templateDef(transName, errorTemplateItem())];
  
  templateParams.templateParamEnv = globalEnv(top.env);
  
  -- Add type params to global scope so that they are visible within the template instantiation
  params.env = addEnv([globalDefsDef(templateParams.templateParamDefs)], openScopeEnv(top.env));
  params.returnType = nothing();
  params.position = 0;
  
  top.errors <- n.predicateRedeclarationCheck;
  top.errors <- params.unifyErrors(top.location, addEnv(params.defs, params.env));
  
  top.transform =
    ableC_Decls {
      proto_typedef unification_trail, size_t, jmp_buf;
      template<$TemplateParameters{templateParams}>
      _Bool $name{transName}($Parameters{params.transform}, unification_trail _trail, closure<() -> _Bool> _continuation) {
        // The initial length of the trail is the index of the first item that
        // should be undone in case of failure
        size_t _trail_index = _trail.length;
        
        // If a failure after cut occurs, control is returned to this point with longjmp
        jmp_buf _cut_buffer;
        if (setjmp(_cut_buffer)) {
          return 0;
        }
        
        $Stmt{
          foldStmt(
            intersperse(
              -- Undo unification effects from the previous (failed) branch
              ableC_Stmt { undo_trail(_trail, _trail_index); },
              lookupAllBy(stringEq, n.name, top.ruleTransformIn)))}
        
        return 0;
      }
      $Decl{defsDecl(predicateDefs)}
    };
}

synthesized attribute templateParamDefs::[Def] occurs on TemplateParameters, TemplateParameter;
synthesized attribute templateParamInstDefs::[Def] occurs on TemplateParameters, TemplateParameter;
autocopy attribute templateParamEnv::Decorated Env occurs on TemplateParameters, TemplateParameter;
autocopy attribute templateParamInstEnv::Decorated Env occurs on TemplateParameters, TemplateParameter;
inherited attribute instParamArgs::TemplateArgs occurs on TemplateParameters;

aspect production consTemplateParameter
top::TemplateParameters ::= h::TemplateParameter t::TemplateParameters
{
  top.templateParamDefs = h.templateParamDefs ++ t.templateParamDefs;
  top.templateParamInstDefs = h.templateParamInstDefs ++ t.templateParamInstDefs;
  
  h.templateParamEnv = addEnv(h.templateParamDefs, top.templateParamEnv);
  h.templateParamInstEnv = addEnv(h.templateParamInstDefs, top.templateParamInstEnv);
  
  local splitArgs :: Pair<TemplateArg TemplateArgs> =
    case top.instParamArgs of
    | consTemplateArg(t, ts) -> pair(t, ts)
    | nilTemplateArg() -> pair(errorTemplateArg(), nilTemplateArg())
    end;
  h.instParamArg = splitArgs.fst;
  t.instParamArgs = splitArgs.snd;
}

aspect production nilTemplateParameter
top::TemplateParameters ::=
{
  top.templateParamDefs = [];
  top.templateParamInstDefs = [];
}

inherited attribute instParamArg::TemplateArg occurs on TemplateParameter;

aspect production typeTemplateParameter
top::TemplateParameter ::= n::Name
{
  top.templateParamDefs =
    [valueDef(n.name, templateParamValueItem(extType(nilQualifier(), typeParamType(n.name)), true, top.location))];
  top.templateParamInstDefs =
    case top.instParamArg of
    | typeTemplateArg(t) -> [valueDef(n.name, templateParamValueItem(t, true, top.location))]
    | _ -> []
    end;
}

aspect production valueTemplateParameter
top::TemplateParameter ::= bty::BaseTypeExpr n::Name mty::TypeModifierExpr
{
  local bty1::BaseTypeExpr = bty;
  bty1.env = top.templateParamEnv;
  bty1.returnType = nothing();
  bty1.givenRefId = nothing();
  local mty1::TypeModifierExpr = mty;
  mty1.env = top.templateParamEnv;
  mty1.returnType = nothing();
  mty1.typeModifiersIn = bty1.typeModifiers;
  mty1.baseType = bty1.typerep;
  top.templateParamDefs =
    valueDef(n.name, templateParamValueItem(mty1.typerep, false, top.location)) ::
    bty1.defs ++ mty1.defs;
  
  local bty2::BaseTypeExpr = bty;
  bty2.env = top.templateParamInstEnv;
  bty2.returnType = nothing();
  bty2.givenRefId = nothing();
  local mty2::TypeModifierExpr = mty;
  mty2.env = top.templateParamInstEnv;
  mty2.returnType = nothing();
  mty2.typeModifiersIn = bty2.typeModifiers;
  mty2.baseType = bty2.typerep;
  top.templateParamInstDefs = 
    valueDef(n.name, templateParamValueItem(mty2.typerep, false, top.location)) ::
    bty2.defs ++ mty2.defs;
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
  top.paramName =
    case n of
    | justName(n) -> "_" ++ n.name
    | nothingName() -> "_p" ++ toString(top.position)
    end;
  top.transform =
    parameterDecl(storage, bty, mty, justName(name(top.paramName, location=builtin)), attrs);
}
