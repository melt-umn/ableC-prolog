grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

synthesized attribute templateParams::TemplateParameters;
synthesized attribute params::Parameters;

tracked nonterminal PredicateDecl with env, pp, errors, defs, functionDefs, errorDefs, paramNames, typereps, templateParams, params, predicateGoalCondParamsIn, cutPredicatesIn, transform<Decls>, ruleTransformIn, labelDefs;
flowtype PredicateDecl = decorate {env, predicateGoalCondParamsIn, cutPredicatesIn, ruleTransformIn}, pp {}, errors {decorate}, defs {decorate}, functionDefs {decorate}, labelDefs {decorate}, typereps {decorate}, templateParams {decorate}, params {decorate}, transform {decorate};

abstract production predicateDecl
top::PredicateDecl ::= n::Name templateParams::TemplateParameters params::Parameters
{
  propagate errors, defs;
  top.pp = pp"${n.pp}<${ppImplode(text(", "), templateParams.pps)}>(${ppImplode(pp", ", params.pps)});";
  top.errorDefs := top.defs;
  top.paramNames = params.paramNames;
  top.typereps = params.typereps;
  top.templateParams = templateParams;
  top.params = params;
  
  local predicateDefs::[Def] = [predicateDef(n.name, predicateItem(top))];
  top.defs <- predicateDefs;
  
  local transName::String = s"_predicate_${n.name}";
  top.errorDefs <- [templateDef(transName, errorTemplateItem())];

  n.env = top.env;
  
  templateParams.templateParamEnv = globalEnv(top.env);
  
  -- Add type params to global scope so that they are visible within the template instantiation
  params.env = addEnv([globalDefsDef(templateParams.templateParamDefs)], openScopeEnv(top.env));
  params.controlStmtContext = initialControlStmtContext;
  params.position = 0;
  
  top.functionDefs := params.functionDefs;
  top.labelDefs := params.labelDefs;
  
  top.errors <- n.predicateRedeclarationCheck;
  top.errors <- params.predicateParamErrors;
  top.errors <- params.unifyErrors(addEnv(params.defs, params.env));
  
  top.transform =
    ableC_Decls {
      // Parser context declarations
      proto_typedef unification_trail, size_t, jmp_buf;
      template<typename a> _Bool is_bound();
      
      template<$TemplateParameters{templateParams}>
      _Bool $name{transName}($Parameters{params.transform}, unification_trail _trail, closure<() -> _Bool> _continuation) {
        // The initial length of the trail is the index of the first item that
        // should be undone in case of failure of the predicate
        size_t _initial_trail_index = _trail.length;
        
        $Stmt{
          if contains(n.name, top.cutPredicatesIn)
          then ableC_Stmt {
            // If a failure after cut occurs, control is returned to this point with longjmp
            jmp_buf _cut_buffer;
            if (setjmp(_cut_buffer)) {
              // Trail has already been undone before the longjmp
              return 0;
            }
          }
          else nullStmt()
        }
        
        // Tail-call optimization returns control to this point
        _pred_start:;
        
        // The first index of the trail that should be undone after a rule
        // fails, which can differ from _initial_trail_index following a tail-
        // recursive call
        size_t _trail_index = _trail.length;

        $Stmt{
          foldStmt(
            map(
              \ p::String -> ableC_Stmt { _Bool $name{s"_${p}_bound"} = is_bound($name{p}); },
              unions(lookupAll(n.name, top.predicateGoalCondParamsIn))))}
        
        $Stmt{
          foldStmt(
            intersperse(
              -- Undo unification effects from the previous (failed) branch
              ableC_Stmt { undo_trail(_trail, _trail_index); },
              lookupAll(n.name, top.ruleTransformIn)))}
        
        undo_trail(_trail, _initial_trail_index);
        return 0;
      }
      $Decl{defsDecl(predicateDefs)}
    };
}

monoid attribute templateParamDefs::[Def] with [], ++;
attribute templateParamDefs occurs on TemplateParameters, TemplateParameter;
inherited attribute templateParamEnv::Decorated Env occurs on TemplateParameters, TemplateParameter;

propagate templateParamDefs on TemplateParameters;

aspect production consTemplateParameter
top::TemplateParameters ::= h::TemplateParameter t::TemplateParameters
{
  h.templateParamEnv = top.templateParamEnv;
  t.templateParamEnv = addEnv(h.templateParamDefs, top.templateParamEnv);
}

aspect production typeTemplateParameter
top::TemplateParameter ::= n::Name
{
  top.templateParamDefs :=
    [valueDef(n.name, templateParamValueItem(extType(nilQualifier(), typeParamType(n.name)), true))];
}

aspect production valueTemplateParameter
top::TemplateParameter ::= bty::BaseTypeExpr n::Name mty::TypeModifierExpr
{
  local bty1::BaseTypeExpr = bty;
  bty1.env = top.templateParamEnv;
  bty1.controlStmtContext = initialControlStmtContext;
  bty1.givenRefId = nothing();
  local mty1::TypeModifierExpr = mty;
  mty1.env = top.templateParamEnv;
  mty1.controlStmtContext = initialControlStmtContext;
  mty1.typeModifierIn = bty1.typeModifier;
  mty1.baseType = bty1.typerep;
  top.templateParamDefs :=
    valueDef(n.name, templateParamValueItem(mty1.typerep, false)) ::
    bty1.defs ++ mty1.defs;
}

monoid attribute predicateParamErrors::[Message] with [], ++;
attribute predicateParamErrors occurs on Parameters;
propagate predicateParamErrors on Parameters;

synthesized attribute paramNames::[String] occurs on Parameters;
attribute transform<Parameters> occurs on Parameters;

inherited attribute tailCallArgs::Exprs occurs on Parameters;
synthesized attribute tailCallTrans::Stmt occurs on Parameters;

aspect production consParameters
top::Parameters ::= h::ParameterDecl t::Parameters
{
  top.transform = consParameters(h.transform, t.transform);
  top.paramNames = h.paramName :: t.paramNames;
  top.tailCallTrans = seqStmt(h.tailCallTrans, t.tailCallTrans);

  h.tailCallArg =
    case top.tailCallArgs of
    | consExpr(h, _) -> h
    | _ -> error("Too few LogicExprs provided for tailCallArg")
    end;
  t.tailCallArgs =
    case top.tailCallArgs of
    | consExpr(_, t) -> t
    | _ -> error("Too few LogicExprs provided for tailCallArg")
    end;
}

aspect production nilParameters
top::Parameters ::= 
{
  top.transform = nilParameters();
  top.paramNames = [];
  top.tailCallTrans = nullStmt();
}

attribute predicateParamErrors occurs on ParameterDecl;

synthesized attribute paramName::String occurs on ParameterDecl;
attribute transform<ParameterDecl> occurs on ParameterDecl;

inherited attribute tailCallArg::Expr occurs on ParameterDecl;
attribute tailCallTrans occurs on ParameterDecl;

aspect production parameterDecl
top::ParameterDecl ::= storage::StorageClasses  bty::BaseTypeExpr  mty::TypeModifierExpr  n::MaybeName  attrs::Attributes
{
  top.predicateParamErrors :=
    if containsQualifier(constQualifier(), top.typerep) -- top.typerep is pre-instantiated but we only care about qualifiers
    then [errFromOrigin(top, "Predicate parameters may not be declared const")]
    else [];
  top.paramName =
    case n of
    | justName(n) -> n.name
    | nothingName() -> "_p" ++ toString(top.position)
    end;
  top.transform =
    parameterDecl(storage, bty, mty, justName(name(top.paramName)), attrs);
  top.tailCallTrans = ableC_Stmt { $name{top.paramName} = $Expr{top.tailCallArg}; };
}
