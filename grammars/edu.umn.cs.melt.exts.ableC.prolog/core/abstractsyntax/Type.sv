grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

abstract production typeParamType
top::ExtType ::= n::String
{
  propagate canonicalType;
  top.pp = text(n);
  top.host = error("typeParamType shouldn't occur in host tree!");
  top.baseTypeExpr = typedefTypeExpr(top.givenQualifiers, name(n));
  top.mangledName = n;
  top.isEqualTo =
    \ other::ExtType ->
      case other of
      | typeParamType(n2) -> n == n2
      | _ -> false
      end;
  
  top.unifyErrors =
    \ env::Decorated Env ->
      case top.otherType of
      | extType(_, typeParamType(n2)) ->
        if n == n2
        then []
        else [errFromOrigin(ambientOrigin(), s"Unification type variables must match (got ${n}, ${n2})")]
      | extType(_, varType(extType(_, typeParamType(n2)))) ->
        if n == n2
        then []
        else [errFromOrigin(ambientOrigin(), s"Unification value and variable type variables must match (got ${n}, ${n2})")]
      | t -> [errFromOrigin(ambientOrigin(), s"Unification is not defined for type variable ${n} and ${showType(t)}")]
      end;
}

