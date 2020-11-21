grammar edu:umn:cs:melt:exts:ableC:string:concretesyntax;

import edu:umn:cs:melt:ableC:abstractsyntax:construction;
import silver:langutil;

marking terminal Show_t 'show' lexer classes {Keyword, Global};
terminal With_t 'with' lexer classes {Keyword};

concrete production showWithDecl_c
top::Declaration_c ::= 'show' '(' ty::TypeName_c ')' 'with' show::Identifier_t
{
  top.ast = showWithDecl(ty.ast, fromId(show));
}
