grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

synthesized attribute partialInferredTypes::[Pair<String Type>] occurs on Parameters;
inherited attribute partialArgumentTypes::[Maybe<Type>] occurs on Parameters;

aspect production consParameters
top::Parameters ::= h::ParameterDecl  t::Parameters
{
  top.partialInferredTypes =
    case top.partialArgumentTypes of
    | [] -> []
    | just(_) :: _ -> newH.inferredTypes ++ t.partialInferredTypes
    | nothing() :: _ -> t.partialInferredTypes
    end;
    
  local newH::ParameterDecl = h;
  newH.env = h.env;
  newH.returnType = h.returnType;
  newH.position = h.position;
  newH.argumentType = head(top.partialArgumentTypes).fromJust;
  t.partialArgumentTypes = tail(top.partialArgumentTypes);
}

aspect production nilParameters
top::Parameters ::=
{
  top.partialInferredTypes = [];
}
