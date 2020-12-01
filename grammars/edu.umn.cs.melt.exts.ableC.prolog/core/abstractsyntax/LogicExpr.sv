grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

inherited attribute expectedTypes::[Type];

-- If true, transform.typerep must be unifiable with expectedType
-- If false, transform.typerep must exactly match expectedType
autocopy attribute allowUnificationTypes::Boolean;

autocopy attribute allocator::Expr;

inherited attribute isExcludableBy<a>::a;
synthesized attribute isExcludable::[[String]]; -- "product of sums" of parameter boundness -- with [], unionBy(\ e1::[String] e2::[String] -> all(zipWith(stringEq, e1, e2)), _, _);

inherited attribute paramNamesIn::[String];
synthesized attribute paramUnifyTransform::Expr;

synthesized attribute maybeTypereps::[Maybe<Type>];

nonterminal LogicExprs with pps, env, count, expectedTypes, allowUnificationTypes, allocator, refVariables, isExcludable, isExcludableBy<LogicExprs>, errors, defs, maybeTypereps, transform<Exprs>, paramNamesIn, paramUnifyTransform;
flowtype LogicExprs = decorate {env, expectedTypes, allowUnificationTypes, allocator, refVariables}, pps {}, count {}, isExcludable {env, expectedTypes, allowUnificationTypes, isExcludableBy, paramNamesIn}, errors {decorate}, defs {env, expectedTypes, allowUnificationTypes}, maybeTypereps {env, allowUnificationTypes}, transform {decorate}, paramUnifyTransform {decorate, paramNamesIn};

propagate errors, defs on LogicExprs;

abstract production consLogicExpr
top::LogicExprs ::= h::LogicExpr t::LogicExprs
{
  top.pps = h.pp :: t.pps;
  top.count = 1 + t.count;
  top.maybeTypereps = h.maybeTyperep :: newT.maybeTypereps;
  top.transform = consExpr(h.transform, t.transform);
  
  -- Needed to compute maybeTypereps approximatly without using h.defs
  local newT::LogicExprs = t;
  newT.env = top.env;
  newT.allowUnificationTypes = top.allowUnificationTypes;
  
  h.paramNameIn = head(top.paramNamesIn);
  t.paramNamesIn = tail(top.paramNamesIn);
  top.paramUnifyTransform =
    case h of
    | wildcardLogicExpr() -> t.paramUnifyTransform
    | _ ->
      andExpr(
        unifyExpr(
          ableC_Expr { $name{h.paramNameIn} },
          h.transform,
          justExpr(ableC_Expr { _trail }),
          location=builtin),
        t.paramUnifyTransform,
        location=builtin)
    end;
  
  t.env = addEnv(h.defs, h.env);
  
  local splitTypes :: Pair<Type [Type]> =
    case top.expectedTypes of
    | t::ts -> pair(t, ts)
    | [] -> pair(errorType(), [])
    end;
  h.expectedType = splitTypes.fst;
  t.expectedTypes = splitTypes.snd;
  
  h.isExcludableBy =
    case top.isExcludableBy of
    | consLogicExpr(h, t) -> h
    end;
  t.isExcludableBy =
    case top.isExcludableBy of
    | consLogicExpr(h, t) -> t
    end;
  top.isExcludable =
    case h.isExcludable, t.isExcludable of
    | [], e -> []
    | e, [] -> []
    | [e1], [e2] -> [e1 ++ e2]
    end;
}

abstract production nilLogicExpr
top::LogicExprs ::=
{
  top.pps = [];
  top.count = 0;
  top.maybeTypereps = [];
  top.transform = nilExpr();
  top.paramUnifyTransform = ableC_Expr { (_Bool)1 };
  top.isExcludable = [[]];
}

function foldLogicExpr
LogicExprs ::= les::[LogicExpr]
{
  return foldr(consLogicExpr, nilLogicExpr(), les);
}

inherited attribute paramNameIn::String;
inherited attribute expectedType::Type;

closed nonterminal LogicExpr with location, pp, env, expectedType, allowUnificationTypes, allocator, refVariables, paramNameIn, isExcludable, isExcludableBy<LogicExpr>, errors, defs, maybeTyperep, transform<Expr>;
flowtype LogicExpr = decorate {env, expectedType, allowUnificationTypes, allocator, refVariables}, pp {}, isExcludable {env, expectedType, isExcludableBy, paramNameIn}, errors {decorate}, defs {env, expectedType, allowUnificationTypes}, maybeTyperep {env, allowUnificationTypes}, transform {decorate};

propagate errors, defs on LogicExpr;

abstract production decLogicExpr
top::LogicExpr ::= le::Decorated LogicExpr
{
  top.pp = le.pp;
  top.errors := le.errors;
  top.defs := le.defs;
  top.maybeTyperep = le.maybeTyperep;
  top.transform = le.transform;

  forwards to new(le);
}

abstract production nameLogicExpr
top::LogicExpr ::= n::Name
{
  top.pp = n.pp;
  forwards to
    case n.valueItem of
    | enumValueItem(_) -> constLogicExpr(declRefExpr(n, location=builtin), location=top.location)
    | parameterValueItem(_) -> constLogicExpr(declRefExpr(n, location=builtin), location=top.location)
    | _ -> varLogicExpr(n, location=top.location)
    end;
}

abstract production varLogicExpr
top::LogicExpr ::= n::Name
{
  top.pp = n.pp;
  top.defs <-
    if null(n.valueLocalLookup)
    then [valueDef(n.name, varValueItem(extType(nilQualifier(), varType(baseType)), n.location))]
    else [];
  top.maybeTyperep =
    if !null(n.valueLocalLookup)
    then just(n.valueItem.typerep)
    else nothing();
  top.transform =
    case top.expectedType of 
    | extType(_, varType(_)) -> ableC_Expr { $name{n.name} }
    | _ when top.allowUnificationTypes -> ableC_Expr { $name{n.name} }
    | _ -> ableC_Expr {
        inst value_loc<$directTypeExpr{baseType}>($name{n.name}, $stringLiteralExpr{n.location.unparse})
      }
    end;
  
  local baseType::Type =
    case top.expectedType of
    | extType(_, varType(sub)) -> sub
    | t -> t
    end;
  local expectedType::Type = top.expectedType;
  expectedType.otherType = extType(nilQualifier(), varType(baseType));
  top.errors <- expectedType.unifyErrors(n.location, top.env);
  top.errors <- n.valueRedeclarationCheck(extType(nilQualifier(), varType(baseType)));
  top.errors <-
    if null(n.valueLocalLookup) && containsBy(nameEq, n, top.refVariables)
    then [err(n.location, s"Unification variable ${n.name} shares a name with a variable referenced in another goal")]
    else [];
  top.errors <-
    case top.expectedType of
    | extType(_, varType(_)) -> []
    | errorType() -> []
    | _ when null(n.valueLocalLookup) && !top.allowUnificationTypes ->
      [wrn(n.location, s"First occurence of variable ${n.name} is in a non-variable term position (got ${showType(top.expectedType)})")]
    | _ -> []
    end;
  
  top.isExcludable = [[]];
}

abstract production wildcardLogicExpr
top::LogicExpr ::=
{
  top.pp = pp"_";
  top.maybeTyperep = nothing();
  top.transform =
    freeVarExpr(
      typeName(directTypeExpr(baseType), baseTypeExpr()),
      top.allocator,
      location=builtin);
  
  local baseType::Type =
    case top.expectedType of
    | extType(_, varType(sub)) -> sub
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
  top.isExcludable = [[]];
}

abstract production constLogicExpr
top::LogicExpr ::= e::Expr
{
  top.pp = e.pp;
  top.maybeTyperep = just(e.typerep);
  top.transform =
    makeVarExpr(
      top.allocator, top.allowUnificationTypes, top.expectedType,
      case baseType.defaultFunctionArrayLvalueConversion, e.typerep.defaultFunctionArrayLvalueConversion of
      | extType(_, stringType()), pointerType(_, builtinType(_, signedType(charType()))) ->
        strExpr(e, location=builtin)
      | t, _ -> ableC_Expr { ($directTypeExpr{t})$Expr{e} }
      end);
  
  e.returnType = nothing();
  
  local baseType::Type =
    case top.expectedType of
    | extType(_, varType(sub)) -> sub
    | errorType() -> errorType()
    | t -> t
    end;
  local expectedType::Type = top.expectedType;
  expectedType.otherType =
    case baseType.defaultFunctionArrayLvalueConversion, e.typerep.defaultFunctionArrayLvalueConversion of
    | extType(_, stringType()), pointerType(_, builtinType(_, signedType(charType()))) ->
      extType(nilQualifier(), stringType())
    | t1, t2 ->
      if compatibleTypes(t1, t2, true, true)
      then t1 -- Value is cast to expected type
      else e.typerep
    end;
  top.errors <- expectedType.unifyErrors(top.location, top.env);

  top.isExcludable =
    case e, decorate top.isExcludableBy with {env = top.env;} of
    | stringLiteral(s1), constLogicExpr(stringLiteral(s2)) when s1 != s2 ->
      case top.expectedType of
      | extType(_, varType(_)) -> [[top.paramNameIn]]
      | _ -> []
      end
    | e1, constLogicExpr(e2)
      when case e1.integerConstantValue, e2.integerConstantValue of
        | just(i1), just(i2) -> i1 != i2
        | _, _ -> false
        end ->
      case top.expectedType of
      | extType(_, varType(_)) -> [[top.paramNameIn]]
      | _ -> []
      end
    | _, _ -> [[]]
    end;
}

abstract production constructorLogicExpr
top::LogicExpr ::= n::Name les::LogicExprs
{
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
  
  top.errors <-
    case adtType, adtName, adtLookup, constructorParamLookup of
    | errorType(), _, _, _ -> []
    -- Check that expected type is an ADT of some sort
    | _, nothing(), _, _ -> [err(top.location, s"Constructor expected to unify with a datatype (got ${showType(top.expectedType)}).")]
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
  
  top.errors <-
    case lookupValue(n.name, top.env) of
    -- Check that this constructor isn't otherwise shadowed
    | parameterValueItem(item) :: _ -> [err(n.location, s"Constructor ${n.name} is shadowed by a predicate parameter (declared at ${item.sourceLocation.unparse})")]
    | _ -> []
    end;
  
  -- Infer type for non-templated ADTs by looking up the constructor return type
  top.maybeTyperep =
    case n.valueItem.typerep of
    | functionType(res, _, _) -> just(res)
    | _ -> nothing()
    end;
  
  -- Since we know that top.expectedType has already been checked as unifiable, we know the
  -- expected type for all the constructor parameters have already been checked as well.
  les.expectedTypes =
    case constructorParamLookup of
    | just(params) -> map(\ t::Type -> t.canonicalType, params.typereps)
    | nothing() -> []
    end;
  les.allowUnificationTypes = false;
  
  top.transform =
    makeVarExpr(
      top.allocator,
      top.allowUnificationTypes,
      top.expectedType,
      case adtType of
      -- Avoid calling constructors when we know there is something wrong with the type
      | errorType() -> errorExpr([], location=builtin)
      -- TODO: Interfering hack to call the constructor for template datatypes
      | templatedType(_, _, args, _) ->
        ableC_Expr {
          inst $name{n.name}<$TemplateArgNames{args.argNames}>($Exprs{les.transform})
        }
      | _ -> ableC_Expr { $name{n.name}($Exprs{les.transform}) }
      end);

  top.isExcludable =
    case decorate top.isExcludableBy with {env = top.env;} of
    | constructorLogicExpr(n2, _) when n.name != n2.name ->
      case top.expectedType of
      | extType(_, varType(_)) -> [[top.paramNameIn]]
      | _ -> []
      end
    | _ -> [[]]
    end;
}

-- Ensure that an expression is a unification variable of some sort
function makeVarExpr
Expr ::= allocator::Expr allowUnificationTypes::Boolean t::Type e::Expr
{
  local tmpName::String = s"_tmp_var_${toString(genInt())}";
  return
    case allowUnificationTypes, t of
    | false, extType(_, varType(_)) -> boundVarExpr(allocator, e, location=builtin)
    | _, _ -> e
    end;
}
