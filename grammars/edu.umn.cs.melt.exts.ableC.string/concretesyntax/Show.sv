grammar edu:umn:cs:melt:exts:ableC:string:concretesyntax;

marking terminal Show_t 'show' lexer classes {Ckeyword};

-- Someday, we may overload function application instead
concrete productions top::PrimaryExpr_c
| 'show' '(' s::Expr_c ')'
  { top.ast = showExpr(s.ast, location=top.location); }
