grammar determinism;

{- This Silver specification does not generate a useful working 
   compiler, it only serves as a grammar for running the modular
   determinism analysis.
 -}

import edu:umn:cs:melt:ableC:host;

copper_mda testCore(ablecParser) {
  edu:umn:cs:melt:exts:ableC:prolog:core:concretesyntax;
}

copper_mda testList(ablecParser) {
  edu:umn:cs:melt:exts:ableC:prolog:core:concretesyntax;
  edu:umn:cs:melt:exts:ableC:prolog:list:concretesyntax;
}

