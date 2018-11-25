grammar edu:umn:cs:melt:exts:ableC:prolog:abstractsyntax;

inherited attribute expectedTypes::[Type];

-- If true, transform.typerep must be unifiable with expectedType
-- If false, transform.typerep must exactly match expectedType
autocopy attribute allowUnificationTypes::Boolean;

autocopy attribute allocator::Expr;

inherited attribute paramNamesIn::[String];
synthesized attribute paramUnifyTransform::Expr;

nonterminal LogicExprs with pps, env, count, expectedTypes, allowUnificationTypes, allocator, errors, defs, transform<Exprs>, paramNamesIn, paramUnifyTransform, substitutions, substituted<LogicExprs>;
flowtype LogicExprs = decorate {env, expectedTypes, allowUnificationTypes, allocator}, pps {}, count {}, errors {decorate}, defs {decorate}, transform {decorate}, paramUnifyTransform {decorate, paramNamesIn}, substituted {substitutions};

abstract production consLogicExpr
top::LogicExprs ::= h::LogicExpr t::LogicExprs
{
  propagate substituted;
  top.pps = h.pp :: t.pps;
  top.count = 1 + t.count;
  top.errors := h.errors ++ t.errors;
  top.defs := h.defs ++ t.defs;
  top.transform = consExpr(h.transform, t.transform);
  
  t.paramNamesIn = tail(top.paramNamesIn);
  top.paramUnifyTransform =
    andExpr(
      unifyExpr(
        ableC_Expr { $name{head(top.paramNamesIn)} },
        h.transform,
        justExpr(ableC_Expr { _trail }),
        location=builtin),
      t.paramUnifyTransform,
      location=builtin);
  
  t.env = addEnv(h.defs, h.env);
  
  local splitTypes :: Pair<Type [Type]> =
    case top.expectedTypes of
    | t::ts -> pair(t, ts)
    | [] -> pair(errorType(), [])
    end;
  h.expectedType = splitTypes.fst;
  t.expectedTypes = splitTypes.snd;
}

abstract production nilLogicExpr
top::LogicExprs ::=
{
  propagate substituted;
  top.pps = [];
  top.count = 0;
  top.errors := [];
  top.defs := [];
  top.transform = nilExpr();
  top.paramUnifyTransform = ableC_Expr { (_Bool)1 };
}

function foldLogicExpr
LogicExprs ::= les::[LogicExpr]
{
  return foldr(consLogicExpr, nilLogicExpr(), les);
}

inherited attribute expectedType::Type;

nonterminal LogicExpr with location, pp, env, expectedType, allowUnificationTypes, allocator, errors, defs, transform<Expr>, substitutions, substituted<LogicExpr>;
flowtype LogicExpr = decorate {env, expectedType, allowUnificationTypes, allocator}, pp {}, errors {decorate}, defs {decorate}, transform {decorate}, substituted {substitutions};

abstract production nameLogicExpr
top::LogicExpr ::= n::Name
{
  propagate substituted;
  top.pp = n.pp;
  forwards to
    case n.valueItem of
    | enumValueItem(_) -> constLogicExpr(declRefExpr(n, location=builtin), location=top.location)
    | _ -> varLogicExpr(n, location=top.location)
    end;
}

abstract production varLogicExpr
top::LogicExpr ::= n::Name
{
  propagate substituted;
  top.pp = n.pp;
  top.errors := [];
  top.defs :=
    if null(n.valueLocalLookup)
    then [valueDef(n.name, varValueItem(extType(nilQualifier(), varType(baseType)), n.location))]
    else [];
  top.transform = ableC_Expr { $name{n.name} };
  
  local baseType::Type =
    case top.expectedType of
    | extType(_, varType(sub)) -> sub
    | errorType() -> errorType()
    | t -> t
    end;
  local expectedType::Type = top.expectedType;
  expectedType.otherType = extType(nilQualifier(), varType(baseType));
  top.errors <-
    if top.allowUnificationTypes
    then expectedType.unifyErrors(n.location, top.env)
    else
      case top.expectedType of
      | extType(_, varType(_)) -> []
      | errorType() -> []
      | t -> [err(n.location, s"Variable expected to unify with a variable type (got ${showType(top.expectedType)})")]
      end;
  top.errors <- n.valueRedeclarationCheck(extType(nilQualifier(), varType(baseType)));
}

abstract production wildcardLogicExpr
top::LogicExpr ::=
{
  propagate substituted;
  top.pp = pp"_";
  top.errors := [];
  top.defs := [];
  top.transform =
    freeVarExpr(
      typeName(directTypeExpr(baseType), baseTypeExpr()),
      top.allocator,
      location=builtin);
  
  local baseType::Type =
    case top.expectedType of
    | extType(_, varType(sub)) -> sub
    | errorType() -> errorType()
    | t -> t
    end;
  local expectedType::Type = top.expectedType;
  expectedType.otherType = extType(nilQualifier(), varType(baseType));
  top.errors <-
    if top.allowUnificationTypes
    then expectedType.unifyErrors(top.location, top.env)
    else
      case top.expectedType of
      | extType(_, varType(_)) -> []
      | errorType() -> []
      | t -> [err(top.location, s"Wildcard expected to unify with a variable type (got ${showType(top.expectedType)})")]
      end;
}

abstract production constLogicExpr
top::LogicExpr ::= e::Expr
{
  propagate substituted;
  top.pp = e.pp;
  top.errors := e.errors;
  top.defs := e.defs;
  top.transform =
    makeVarExpr(top.allocator, top.allowUnificationTypes, top.expectedType, e);
  
  e.returnType = nothing();
  
  local expectedType::Type = top.expectedType;
  expectedType.otherType = e.typerep;
  top.errors <- expectedType.unifyErrors(top.location, top.env);
}

abstract production constructorLogicExpr
top::LogicExpr ::= n::Name les::LogicExprs
{
  propagate substituted;
  top.pp = cat( n.pp, parens( ppImplode(text(","), les.pps) ) );
  
  local adtType::Type =
    case top.expectedType of
    | extType(_, varType(sub)) -> sub
    | t -> t
    end;
  
  local adtName::Maybe<String> = adtType.adtName;
  
  local adtLookup::[RefIdItem] =
    case adtType.maybeRefId of
    | just(rid) -> lookupRefId(rid, top.env)
    | nothing() -> []
    end;
  
  local constructors::[Pair<String Decorated Parameters>] =
    case adtLookup of
    | item :: _ -> item.constructors
    | [] -> []
    end;
  
  local constructorParamLookup::Maybe<Decorated Parameters> =
    lookupBy(stringEq, n.name, constructors);
  
  top.errors := les.errors;
  top.errors <-
    case adtType, adtName, adtLookup, constructorParamLookup of
    | errorType(), _, _, _ -> []
    -- Check that expected type is an ADT of some sort
    | t, nothing(), _, _ -> [err(top.location, s"Constructor pattern expected to match a datatype (got ${showType(t)}).")]
    -- Check that this ADT has a definition
    | _, just(id), [], _ -> [err(top.location, s"datatype ${id} does not have a definition.")]
    -- Check that this is a constructor for the expected ADT type.
    | t, _, _, nothing() -> [err(top.location, s"${showType(t)} does not have constructor ${n.name}.")]
    | _, _, _, just(params) ->
      -- Check that the number of arguments matches number of parameters for this constructor.
      if les.count != params.count
      then [err(top.location, s"This expression has ${toString(les.count)} arguments, but ${toString(params.count)} were expected.")]
      else []
    end;
  
  top.defs := les.defs;
  
  -- Since we know that top.expectedType has already been checked as unifiable, we know the
  -- expected type for all the constructor parameters have already been checked as well.
  les.expectedTypes =
    case constructorParamLookup of
    | just(params) -> params.typereps
    | nothing() -> []
    end;
  les.allowUnificationTypes = false;
  
  top.transform =
    makeVarExpr(
      top.allocator,
      top.allowUnificationTypes,
      top.expectedType,
      -- TODO: Interfering hack to call the constructor for template datatypes
      case adtType of
      | templatedType(_, _, args, _) ->
        ableC_Expr {
          inst $name{n.name}<$TypeNames{
            foldr(
              consTypeName, nilTypeName(),
              map(\ t::Type -> typeName(directTypeExpr(t), baseTypeExpr()), args))
          }>($Exprs{les.transform})
        }
      | _ -> ableC_Expr { $name{n.name}($Exprs{les.transform}) }
      end);
}

-- Ensure that an expression is a unification variable of some sort
function makeVarExpr
Expr ::= allocator::Expr allowUnificationTypes::Boolean t::Type e::Expr
{
  local tmpName::String = s"_tmp_var_${toString(genInt())}";
  return
    case allowUnificationTypes, t of
    | false, extType(_, varType(sub)) ->
      ableC_Expr {
        ({$directTypeExpr{t} $name{tmpName} =
            $Expr{
              freeVarExpr(
                typeName(directTypeExpr(sub), baseTypeExpr()),
                allocator,
                location=builtin)};
          $Expr{unifyExpr(e, ableC_Expr { $name{tmpName} }, nothingExpr(), location=builtin)};
          $name{tmpName};})
      }
    | _, _ -> e
    end;
}
