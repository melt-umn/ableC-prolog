grammar edu:umn:cs:melt:exts:ableC:prolog:core:abstractsyntax;

abstract production termExpr
top::Expr ::= ty::TypeName allocator::Expr le::LogicExpr
{
  propagate substituted;
  top.pp = pp"term<${ty.pp}>(${allocator.pp}) {${le.pp}}";
  
  local expectedAllocatorType::Type =
    functionType(
      pointerType(
        nilQualifier(),
        builtinType(nilQualifier(), voidType())),
      protoFunctionType([builtinType(nilQualifier(), unsignedType(longType()))], false),
      nilQualifier());
  
  local localErrors::[Message] =
    ty.errors ++ allocator.errors ++ le.errors ++
    (if !ty.typerep.isCompleteType(top.env)
     then [err(top.location, s"term type parameter has incomplete type ${showType(ty.typerep)}")]
     else []) ++
    (if !compatibleTypes(expectedAllocatorType, allocator.typerep, true, false)
     then [err(allocator.location, s"Allocator must have type void *(unsigned long) (got ${showType(allocator.typerep)})")]
     else []) ++
    checkUnificationHeaderTemplateDef("_var_d", top.location, top.env);
  
  le.env = addEnv(ty.defs, ty.env);
  le.expectedType = ty.typerep;
  le.allowUnificationTypes = false;
  le.allocator = allocator;
  
  local fwrd::Expr =
    ableC_Expr {
      ({$Stmt{makeVarDecls(le.defs)}
        $Expr{le.transform};})
    };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}