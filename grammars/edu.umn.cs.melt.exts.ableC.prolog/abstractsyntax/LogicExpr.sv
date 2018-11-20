grammar edu:umn:cs:melt:exts:ableC:prolog:abstractsyntax;

inherited attribute expectedTypes::[Type];

inherited attribute paramNamesIn::[String];
synthesized attribute paramUnifyTransform::Expr;

nonterminal LogicExprs with pps, env, expectedTypes, errors, defs, transform<Exprs>, paramNamesIn, paramUnifyTransform, substituted<LogicExprs>;

abstract production consLogicExpr
top::LogicExprs ::= h::LogicExpr t::LogicExprs
{
  propagate substituted;
  top.pps = h.pp :: t.pps;
  top.errors := h.errors ++ t.errors;
  top.defs := h.defs ++ t.defs;
  top.transform = consExpr(h.transform, t.transform);
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
  top.errors := [];
  top.defs := [];
  top.transform = nilExpr();
  top.paramUnifyTransform = ableC_Expr { 1 };
}

inherited attribute expectedType::Type;

nonterminal LogicExpr with location, pp, env, expectedType, errors, defs, transform<Expr>, substituted<LogicExpr>;

{-abstract production
-}

-- TODO: Reminder for constructors: Ensure all type params are unifyable 
