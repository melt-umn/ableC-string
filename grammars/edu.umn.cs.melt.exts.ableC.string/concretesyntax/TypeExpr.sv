grammar edu:umn:cs:melt:exts:ableC:string:concretesyntax;

imports edu:umn:cs:melt:ableC:concretesyntax;
imports edu:umn:cs:melt:ableC:abstractsyntax:host;

imports edu:umn:cs:melt:exts:ableC:string;

marking terminal String_t 'string' lexer classes {Type, Global};

concrete productions top::TypeSpecifier_c
| 'string'
    { top.realTypeSpecifiers = [stringTypeExpr(top.givenQualifiers)];
      top.preTypeSpecifiers = []; }
