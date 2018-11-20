grammar edu:umn:cs:melt:exts:ableC:prolog:abstractsyntax;

abstract production logicDecl
top::Decl ::= lss::LogicStmts
{
  propagate substituted;
  top.pp = pp"logic ${braces(terminate(line(), lss.pps))}";
  
  lss.env = openScopeEnv(top.env);
  
  forwards to
    if !null(lss.errors)
    then warnDecl(lss.errors)
    else decls(foldDecl(lss.transform));
}
