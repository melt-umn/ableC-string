grammar determinism;

{- This Silver specification does not generate a useful working 
   compiler, it only serves as a grammar for running the modular
   determinism analysis.
 -}

import edu:umn:cs:melt:ableC:host;

copper_mda testTypeExpr(ablecParser) {
  edu:umn:cs:melt:exts:ableC:string:concretesyntax:typeExpr;
}

copper_mda testStr(ablecParser) {
  edu:umn:cs:melt:exts:ableC:string:concretesyntax:str;
}

copper_mda testShow(ablecParser) {
  edu:umn:cs:melt:exts:ableC:string:concretesyntax:show;
}

