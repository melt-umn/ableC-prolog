grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

synthesized attribute partialInferredArgs::[Pair<String TemplateArg>] occurs on Parameters;
inherited attribute partialArgumentTypes::[Maybe<Type>] occurs on Parameters;

aspect production consParameters
top::Parameters ::= h::ParameterDecl  t::Parameters
{
  top.partialInferredArgs =
    case top.partialArgumentTypes of
    | [] -> []
    | just(_) :: _ -> newH.inferredArgs ++ t.partialInferredArgs
    | nothing() :: _ -> t.partialInferredArgs
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
  top.partialInferredArgs = [];
}
