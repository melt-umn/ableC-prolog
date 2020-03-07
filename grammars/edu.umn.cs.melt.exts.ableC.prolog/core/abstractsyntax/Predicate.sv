grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

synthesized attribute templateParams::TemplateParameters;
synthesized attribute params::Parameters;

nonterminal PredicateDecl with location, env, pp, errors, defs, errorDefs, paramNames, typereps, templateParams, params, transform<Decls>, ruleTransformIn;
flowtype PredicateDecl = decorate {env, ruleTransformIn}, pp {}, errors {decorate}, defs {decorate}, typereps {decorate}, templateParams {decorate}, params {decorate}, transform {decorate};

abstract production predicateDecl
top::PredicateDecl ::= n::Name templateParams::TemplateParameters params::Parameters
{
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
autocopy attribute templateParamEnv::Decorated Env occurs on TemplateParameters, TemplateParameter;

aspect production consTemplateParameter
top::TemplateParameters ::= h::TemplateParameter t::TemplateParameters
{
  top.templateParamDefs = h.templateParamDefs ++ t.templateParamDefs;
  h.templateParamEnv = addEnv(h.templateParamDefs, top.templateParamEnv);
}

aspect production nilTemplateParameter
top::TemplateParameters ::=
{
  top.templateParamDefs = [];
}

aspect production typeTemplateParameter
top::TemplateParameter ::= n::Name
{
  top.templateParamDefs =
    [valueDef(n.name, templateParamValueItem(extType(nilQualifier(), typeParamType(n.name)), true, top.location))];
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
  mty1.typeModifierIn = bty1.typeModifier;
  mty1.baseType = bty1.typerep;
  top.templateParamDefs =
    valueDef(n.name, templateParamValueItem(mty1.typerep, false, top.location)) ::
    bty1.defs ++ mty1.defs;
}

synthesized attribute paramNames::[String] occurs on Parameters;
attribute transform<Parameters> occurs on Parameters;

aspect production consParameters
top::Parameters ::= h::ParameterDecl t::Parameters
{
  top.transform = consParameters(h.transform, t.transform);
  top.paramNames = h.paramName :: t.paramNames;
}

aspect production nilParameters
top::Parameters ::= 
{
  top.transform = nilParameters();
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
