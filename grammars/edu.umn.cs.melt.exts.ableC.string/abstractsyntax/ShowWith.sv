grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

abstract production showWithDecl
top::Decl ::= ty::TypeName  showFunctionName::Name
{
  top.pp = pp"show ${ty.pp} with ${showFunctionName.pp};";
  local type::Type = ty.typerep.defaultFunctionArrayLvalueConversion;
  forwards to defsDecl([customShowDef(type.mangledName, showFunctionName)]);
}
