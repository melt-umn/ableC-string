grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

abstract production showWithDecl
top::Decl ::= ty::TypeName  sizeFunc::Name func::Name
{
  top.pp = pp"show ${ty.pp} with ${func.pp};";
  attachNote extensionGenerated("ableC-string");
  propagate env, controlStmtContext;

  nondecorated local type::Type = ty.typerep.defaultFunctionArrayLvalueConversion;
  nondecorated local sizeFnType::Type = sizeFunc.valueItem.typerep;
  nondecorated local fnType::Type = func.valueItem.typerep;
  nondecorated local sizeType::Type =
    case lookupValue("size_t", top.env) of
    | v :: _ -> v.typerep
    | [] -> errorType()
    end;
  nondecorated local expectedSizeFnType::Type =
    functionType(sizeType, protoFunctionType([ty.typerep], false), nilQualifier());
  nondecorated local expectedFnType::Type =
    functionType(sizeType, protoFunctionType([pointerType(nilQualifier(), builtinType(nilQualifier(), signedType(charType()))), ty.typerep], false), nilQualifier());
  local localErrors::[Message] = type.errors ++ func.valueLookupCheck ++
    case getCustomShow(type, top.env) of
    | just(_) -> [errFromOrigin(func, show(80, pp"show for ${ty.pp} already defined"))]
    | nothing() -> []
    end ++
    if !compatibleTypes(sizeFnType, expectedSizeFnType, false, false)
    then [errFromOrigin(func, s"show length function for ${show(80, type)} must have type ${show(80, expectedSizeFnType)} (got ${show(80, sizeFnType)})")]
    else [] ++
    if !compatibleTypes(fnType, expectedFnType, false, false)
    then [errFromOrigin(func, s"show function for ${show(80, type)} must have type ${show(80, expectedFnType)} (got ${show(80, fnType)})")]
    else [];
  forwards to
    if null(localErrors)
      then defsDecl([customShowDef(type, ^sizeFunc, ^func)])
      else warnDecl(localErrors);
}
