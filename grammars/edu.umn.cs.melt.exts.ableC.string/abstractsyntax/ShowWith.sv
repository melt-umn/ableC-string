grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

abstract production showWithDecl
top::Decl ::= ty::TypeName  func::Name
{
  top.pp = pp"show ${ty.pp} with ${func.pp};";
  propagate env, controlStmtContext;

  local type::Type = ty.typerep.defaultFunctionArrayLvalueConversion;
  local fnType::Type = func.valueItem.typerep;
  local expectedFnType::Type =
    functionType(extType(nilQualifier(), stringType()), protoFunctionType([ty.typerep], false), nilQualifier());
  local localErrors::[Message] = type.errors ++ func.valueLookupCheck ++
    case getCustomShow(type, top.env) of
    | just(_) -> [errFromOrigin(func,
                      show(80, pp"show for ${ty.pp} already defined"))]
    | nothing() -> []
    end ++
    if !compatibleTypes(fnType, expectedFnType, false, false)
    then [errFromOrigin(func, s"show function for ${showType(type)} must have type ${showType(expectedFnType)} (got ${showType(fnType)})")]
    else [];
  forwards to
    if null(localErrors)
      then defsDecl([customShowDef(type, func)])
      else warnDecl(localErrors);
}
