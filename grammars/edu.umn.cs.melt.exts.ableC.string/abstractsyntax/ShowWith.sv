grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

abstract production showWithDecl
top::Decl ::= ty::TypeName  showFunctionName::Name
{
  top.pp = pp"show ${ty.pp} with ${showFunctionName.pp};";
  local type::Type = ty.typerep.defaultFunctionArrayLvalueConversion;
  local localErrors::[Message] = type.errors ++
    case getCustomShow(type, top.env) of
    | just(_) -> [err(showFunctionName.location,
                      show(80, pp"show for ${ty.pp} already defined"))]
    | nothing() -> []
    end;
  forwards to
    if null(localErrors)
      then defsDecl([customShowDef(type.mangledName, showFunctionName)])
      else warnDecl(localErrors);
}
