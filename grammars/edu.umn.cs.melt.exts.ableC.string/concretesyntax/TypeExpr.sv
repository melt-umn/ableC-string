grammar edu:umn:cs:melt:exts:ableC:string:concretesyntax;

aspect parser attribute context
  action {
    context = addIdentsToScope([name("string", location=builtin)], String_t, context);
  };

marking terminal String_t 'string' lexer classes {Ctype, Cidentifier};

concrete productions top::TypeSpecifier_c
| 'string'
    { top.realTypeSpecifiers = [stringTypeExpr(top.givenQualifiers, top.location)];
      top.preTypeSpecifiers = []; }
