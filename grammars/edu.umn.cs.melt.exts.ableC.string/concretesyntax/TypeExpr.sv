grammar edu:umn:cs:melt:exts:ableC:string:concretesyntax;

marking terminal String_t 'string' lexer classes {Ctype, Ckeyword};

concrete productions top::TypeSpecifier_c
| 'string'
    { top.realTypeSpecifiers = [stringTypeExpr(top.givenQualifiers, top.location)];
      top.preTypeSpecifiers = []; }
