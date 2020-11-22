grammar edu:umn:cs:melt:exts:ableC:string:concretesyntax;

import edu:umn:cs:melt:ableC:abstractsyntax:construction;
import silver:langutil;

marking terminal Show_t 'show' lexer classes {Keyword, Global};
terminal With_t 'with' lexer classes {Keyword};

concrete productions top::Declaration_c
| 'show' '(' ty::TypeName_c ')' 'with' show::Identifier_t
    { top.ast = showWithDecl(ty.ast, fromId(show)); }
| 'show' id::TypeName_t 'with' show::Identifier_t
    { local ty::TypeName = typeName(typedefTypeExpr(nilQualifier(), fromTy(id)), baseTypeExpr());
      top.ast = showWithDecl(ty, fromId(show)); }
| 'show' kwd::StructOrEnumOrUnionKeyword_c id::TypeName_t 'with' show::Identifier_t
    { local ty::TypeName = typeName(kwd.lookupType(id), baseTypeExpr());
      top.ast = showWithDecl(ty, fromId(show)); }

synthesized attribute lookupType :: (BaseTypeExpr ::= TypeName_t);
nonterminal StructOrEnumOrUnionKeyword_c with lookupType;

concrete productions top::StructOrEnumOrUnionKeyword_c
| 'enum'
    { top.lookupType = \id::TypeName_t ->
        tagReferenceTypeExpr(nilQualifier(), enumSEU(), fromTy(id)); }
| 'struct'
    { top.lookupType = \id::TypeName_t ->
        tagReferenceTypeExpr(nilQualifier(), structSEU(), fromTy(id)); }
| 'union'
    { top.lookupType = \id::TypeName_t ->
        tagReferenceTypeExpr(nilQualifier(), unionSEU(), fromTy(id)); }
