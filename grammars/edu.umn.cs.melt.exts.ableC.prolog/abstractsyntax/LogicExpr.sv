grammar edu:umn:cs:melt:exts:ableC:prolog:abstractsyntax;

inherited attribute expectedTypes::[Type];

inherited attribute paramNamesIn::[String];
synthesized attribute paramUnifyTransform::Expr;

nonterminal LogicExprs with pps, env, count, expectedTypes, errors, defs, transform<Exprs>, paramNamesIn, paramUnifyTransform, substitutions, substituted<LogicExprs>;

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
  top.paramUnifyTransform = ableC_Expr { 1 };
}

function foldLogicExpr
LogicExprs ::= les::[LogicExpr]
{
  return foldr(consLogicExpr, nilLogicExpr(), les);
}

inherited attribute expectedType::Type;

nonterminal LogicExpr with location, pp, env, expectedType, errors, defs, transform<Expr>, substitutions, substituted<LogicExpr>;

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
    then [valueDef(n.name, varValueItem(subType, n.location))]
    else [];
  top.transform = declRefExpr(n, location=builtin);
  
  local subType::Type = varSubType(top.expectedType);
  top.errors <-
    case top.expectedType of
    | extType(_, varType(_)) -> []
    | errorType() -> []
    | t -> [err(n.location, s"Variable expected to unify with a variable type (got ${showType(top.expectedType)})")]
    end;
  top.errors <- n.valueRedeclarationCheck(extType(nilQualifier(), varType(subType)));
}

abstract production constLogicExpr
top::LogicExpr ::= e::Expr
{
  propagate substituted;
  top.pp = e.pp;
  top.errors := e.errors;
  top.defs := e.defs;
  top.transform = makeVarExpr(top.expectedType, e);
  
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
    case top.expectedType.maybeRefId of
    | just(rid) -> lookupRefId(rid, top.env)
    | nothing() -> []
    end;
  
  local constructors::[Pair<String Decorated Parameters>] =
    case adtLookup of
    | item :: _ -> item.constructors
    | [] -> []
    end;
  
  local constructorParamLookup::Maybe<Decorated Parameters> = lookupBy(stringEq, n.name, constructors);
  
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
  
  top.transform = makeVarExpr(top.expectedType, ableC_Expr { $Name{n}($Exprs{les.transform}) });
}

function makeVarExpr
Expr ::= t::Type e::Expr
{
  return
    case t of
    | extType(_, varType(sub)) ->
      ableC_Expr {
        ({$directTypeExpr{t} _tmp_var =
            $Expr{
              freeVarExpr(
                typeName(directTypeExpr(sub), baseTypeExpr()),
              ableC_Expr { alloca },
              location=builtin)};
          $Expr{
            unifyExpr(
              e,
              freeVarExpr(
                typeName(directTypeExpr(sub), baseTypeExpr()),
                ableC_Expr { alloca },
                location=builtin),
              nothingExpr(),
              location=builtin)};
          _tmp_var;})
      }
    | _ -> e
    end;
}
