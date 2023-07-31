grammar edu:umn:cs:melt:exts:ableC:string:concretesyntax;

import edu:umn:cs:melt:ableC:abstractsyntax:construction;
import silver:langutil;

marking terminal Show_t 'show' lexer classes {Keyword, Global};
terminal With_t 'with' lexer classes {Keyword};

concrete productions top::ExternalDeclaration_c
| 'show' '(' ty::TypeName_c ')' 'with' show::Identifier_t
    { top.ast = showWithDecl(ty.ast, fromId(show)); }
| 'show' id::TypeName_t 'with' show::Identifier_t
    { local ty::TypeName = typeName(typedefTypeExpr(nilQualifier(), fromTy(id)), baseTypeExpr());
      top.ast = showWithDecl(ty, fromId(show)); }
| 'show' kwd::TagKeyword_c id::TypeName_t 'with' show::Identifier_t
    { local ty::TypeName = typeName(kwd.ast(fromTy(id)), baseTypeExpr());
      top.ast = showWithDecl(ty, fromId(show)); }

closed tracked nonterminal TagKeyword_c with ast<(BaseTypeExpr ::= Name)>;

concrete productions top::TagKeyword_c
| 'enum'
    { top.ast = tagReferenceTypeExpr(nilQualifier(), enumSEU(), _); }
| 'struct'
    { top.ast = tagReferenceTypeExpr(nilQualifier(), structSEU(), _); }
| 'union'
    { top.ast = tagReferenceTypeExpr(nilQualifier(), unionSEU(), _); }
