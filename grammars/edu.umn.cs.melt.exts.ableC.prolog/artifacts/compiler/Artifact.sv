grammar edu:umn:cs:melt:exts:ableC:prolog:artifacts:compiler;

{- This Silver specification does litte more than list the desired
   extensions, albeit in a somewhat stylized way.

   Files like this can easily be generated automatically from a simple
   list of the desired extensions.
 -}

import edu:umn:cs:melt:ableC:concretesyntax as cst;
import edu:umn:cs:melt:ableC:abstractsyntax:host;
import edu:umn:cs:melt:ableC:drivers:compile;
import edu:umn:cs:melt:ableC:drivers:codeProber as cpr;


parser extendedParser :: cst:Root {
  edu:umn:cs:melt:ableC:concretesyntax;
  edu:umn:cs:melt:exts:ableC:prolog;
  edu:umn:cs:melt:exts:ableC:string;
} 

fun main IO<Integer> ::= args::[String] = driver(args, extendedParser);

fun codeProberParse IO<Decorated Compilation> ::= args::[String] =
  cpr:driver(args, extendedParser);
