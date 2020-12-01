grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

abstract production showWithDecl
top::Decl ::= ty::TypeName  showFunctionName::Name
{
  top.pp = pp"show ${ty.pp} with ${showFunctionName.pp};";
  local type::Type = ty.typerep.defaultFunctionArrayLvalueConversion;
  local fnType::Type = showFunctionName.valueItem.typerep;
  local expectedFnType::Type =
    functionType(extType(nilQualifier(), stringType()), protoFunctionType([ty.typerep], false), nilQualifier());
  local localErrors::[Message] = type.errors ++ showFunctionName.valueLookupCheck ++
    case getCustomShow(type, top.env) of
    | just(_) -> [err(showFunctionName.location,
                      show(80, pp"show for ${ty.pp} already defined"))]
    | nothing() -> []
    end ++
    if !compatibleTypes(fnType, expectedFnType, false, false)
    then [err(showFunctionName.location, s"show function for ${showType(type)} must have type ${showType(expectedFnType)} (got ${showType(fnType)})")]
    else [];
  forwards to
    if null(localErrors)
      then defsDecl([customShowDef(type.mangledName, showFunctionName)])
      else warnDecl(localErrors);
}
