grammar edu:umn:cs:melt:exts:ableC:prolog:abstractsyntax;

abstract production logicDecl
top::Decl ::= lss::LogicStmts
{
  top.pp = pp"logic ${braces(terminate(line(), lss.pps))}";
  
  --local fwrd::Decls;
}
