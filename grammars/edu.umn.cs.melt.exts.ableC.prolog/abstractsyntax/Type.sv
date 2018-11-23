grammar edu:umn:cs:melt:exts:ableC:prolog:abstractsyntax;

abstract production typeVarType
top::ExtType ::= n::String
{
  propagate substituted;
  top.pp = text(n);
  top.host = error("typeVarType shouldn't occur in host tree!");
  top.mangledName = n;
  top.isEqualTo =
    \ other::ExtType ->
      case other of
      | typeVarType(n2) -> n == n2
      | _ -> false
      end;
  
  top.unifyErrors =
    \ l::Location env::Decorated Env ->
      case top.otherType of
      | extType(_, typeVarType(n2)) ->
        if n == n2
        then []
        else [err(l, s"Unification type variables must match (got ${n}, ${n2})")]
      | extType(_, varType(extType(_, typeVarType(n2)))) ->
        if n == n2
        then []
        else [err(l, s"Unification value and variable type variables must match (got ${n}, ${n2})")]
      | t -> [err(l, s"Unification is not defined for type variable ${n} and ${showType(t)}")]
      end;
}

