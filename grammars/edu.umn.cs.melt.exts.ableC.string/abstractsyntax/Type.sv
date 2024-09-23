grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

abstract production stringTypeExpr
top::BaseTypeExpr ::= q::Qualifiers
{
  top.pp = pp"string";
  attachNote extensionGenerated("ableC-string");
  forwards to
    if !null(lookupRefId("edu:umn:cs:melt:exts:ableC:string:string", top.env))
    then extTypeExpr(@q, stringType())
    else errorTypeExpr([errFromOrigin(top, "Missing include of string.xh")]);
}

abstract production stringType
top::ExtType ::=
{
  propagate canonicalType;
  top.pp = pp"string";
  top.host =
    extType(
      top.givenQualifiers,
      refIdExtType(structSEU(), just("_string_s"),
        s"edu:umn:cs:melt:exts:ableC:string:string"));
  top.mangledName = "string";
  top.isEqualTo =
    \ other::ExtType -> case other of stringType() -> true | _ -> false end;
  
  top.eqProd = just(assignString);
  top.lAddProd = just(concatString);
  top.rAddProd = just(concatString);
  top.lMulProd = just(repeatString);
  -- TODO: Overloads for +=, *=, automatically inferred from above
  top.lEqualsProd = just(equalsString);
  top.rEqualsProd = just(equalsString);
  -- TODO: Overload for != automatically inferred from above
  top.arraySubscriptProd = just(subscriptString);
  -- Better error message than default one about not being an lvalue
  top.addressOfArraySubscriptProd =
    just(\ Expr Expr -> errorExpr([errFromOrigin(ambientOrigin(), "strings are immutable, cannot assign to index")]));
  top.callMemberProd = just(callMemberString);
  top.memberProd = just(memberString);
  top.exprInitProd = just(initString);
}

-- Compute the errors for showing/converting a type to a string.
monoid attribute showErrors::([Message] ::= Env) with \ _ -> [], joinShowErrors occurs on Type, BuiltinType, ExtType;
monoid attribute strErrors::([Message] ::= Env) with \ _ -> [], joinShowErrors occurs on Type, BuiltinType, ExtType;

fun joinShowErrors ([Message] ::= Env) ::= e1::([Message] ::= Env) e2::([Message] ::= Env) =
  \ env::Env -> e1(env) ++ e2(env);

-- Coerce a value of some type to a string.
synthesized attribute strProd::(Expr ::= Expr) occurs on Type, BuiltinType, ExtType;

-- Compute the maximum length of the string for a value of some type.
synthesized attribute showMaxLenProd::(Expr ::= Expr) occurs on Type, BuiltinType, ExtType;

-- Write a string representation of a value of some type to a buffer, returning the string length.
synthesized attribute showProd::(Expr ::= Expr Expr) occurs on Type, BuiltinType, ExtType;

aspect default production
top::Type ::=
{
  top.showErrors :=
    \ env::Env ->
      [errFromOrigin(ambientOrigin(), s"show is not defined for type ${show(80, ^top)}")];
  top.strErrors :=
    \ env::Env ->
      [errFromOrigin(ambientOrigin(), s"str is not defined for type ${show(80, ^top)}")];
  top.strProd = error("Undefined");
  top.showMaxLenProd = error("Undefined");
  top.showProd = error("Undefined");
}

aspect production errorType
top::Type ::= 
{
  propagate showErrors, strErrors;
  top.strProd = \ _ -> errorExpr([]);
  top.showMaxLenProd = \ _ -> errorExpr([]);
  top.showProd = \ _ _ -> errorExpr([]);
}

aspect production pointerType
top::Type ::= quals::Qualifiers sub::Type
{
  top.showErrors :=
    \ env::Env ->
      checkStringHeaderDef("show_char_pointer", env) ++
      case sub of
      | builtinType(_, voidType()) -> []
      | functionType(_, _, _) -> []
      | _ -> showErrors(env, ^sub)
      end;
  top.strErrors :=
    \ env::Env ->
      checkStringHeaderDef("MAX_POINTER_STR_LEN", env) ++ sub.strErrors(env);
  top.strProd =
    case sub of
    | builtinType(_, signedType(charType())) -> strCharPointer
    | builtinType(_, unsignedType(charType())) -> strCharPointer
    | _ -> strPointer
    end;
  top.showMaxLenProd =
    case sub of
    | builtinType(_, signedType(charType())) -> showCharPointerMaxLen
    | builtinType(_, unsignedType(charType())) -> showCharPointerMaxLen
    | builtinType(_, voidType()) -> showOpaquePointerMaxLen
    | functionType(_, _, _) -> showOpaquePointerMaxLen
    | _ -> showCharPointerMaxLen
    end;
  top.showProd =
    case sub of
    | builtinType(_, signedType(charType())) -> showCharPointer
    | builtinType(_, unsignedType(charType())) -> showCharPointer
    | builtinType(_, voidType()) -> showOpaquePointer
    | functionType(_, _, _) -> showOpaquePointer
    | _ -> showPointer
    end;
}

aspect production builtinType
top::Type ::= quals::Qualifiers sub::BuiltinType
{
  propagate showErrors, strErrors;
  top.showMaxLenProd = sub.showMaxLenProd;
  top.showProd = sub.showProd;
  top.strProd = sub.strProd;
}

aspect default production
top::BuiltinType ::=
{
  top.showErrors :=
    \ env::Env ->
      [errFromOrigin(ambientOrigin(), s"show is not defined for type ${show(80, builtinType(nilQualifier(), top))}")];
  top.strErrors :=
    \ env::Env ->
      [errFromOrigin(ambientOrigin(), s"str is not defined for type ${show(80, builtinType(nilQualifier(), top))}")];
  top.strProd = error("Undefined");
  top.showMaxLenProd = error("Undefined");
  top.showProd = error("Undefined");
}

aspect production boolType
top::BuiltinType ::=
{
  top.showErrors := checkStringHeaderDef("TRUE_STR", _);
  top.strErrors := checkStringHeaderDef("show_bool", _);
  top.strProd = strBool;
  top.showMaxLenProd = \ _ -> mkIntConst(5);
  top.showProd = showBool;
}

aspect production realType
top::BuiltinType ::= sub::RealType
{
  top.showErrors := checkStringHeaderDef("show_float", _);
  top.strErrors := checkStringHeaderDef("MAX_FLOAT_STR_LEN", _);
  top.strProd = strNum(_, sub.maxStrWidth, s"%${sub.formatSizeChars}f");
  top.showMaxLenProd = \ _ -> sub.maxStrWidth;
  top.showProd = showNum(_, _, s"%${sub.formatSizeChars}f");
}

aspect production signedType
top::BuiltinType ::= sub::IntegerType
{
  top.showErrors := checkStringHeaderDef("show_int", _);
  top.strErrors := checkStringHeaderDef("MAX_INT_STR_LEN", _);
  top.strProd = strNum(_, sub.maxStrWidth, s"%${sub.formatSizeChars}d");
  top.showMaxLenProd = \ _ ->
    case sub of
    | charType() -> mkIntConst(5)
    | _ -> sub.maxStrWidth
    end;
  top.showProd =
    case sub of
    | charType() ->
      \ buf::Expr e::Expr ->
        directCallExpr(
          name("show_char"),
          consExpr(buf, consExpr(e, nilExpr())))
    | _ -> showNum(_, _, s"%${sub.formatSizeChars}d")
    end;
}

aspect production unsignedType
top::BuiltinType ::= sub::IntegerType
{
  top.showErrors := checkStringHeaderDef("show_int", _);
  top.strErrors := checkStringHeaderDef("MAX_INT_STR_LEN", _);
  top.strProd = strNum(_, sub.maxStrWidth, s"%${sub.formatSizeChars}u");
  top.showMaxLenProd = \ _ ->
    case sub of
    | charType() -> mkIntConst(5)
    | _ -> sub.maxStrWidth
    end;
  top.showProd =
    case sub of
    | charType() ->
      \ buf::Expr e::Expr ->
        directCallExpr(
          name("show_char"),
          consExpr(buf, consExpr(e, nilExpr())))
    | _ -> showNum(_, _, s"%${sub.formatSizeChars}u")
    end;
}

synthesized attribute maxStrWidth::Expr occurs on RealType, IntegerType;
synthesized attribute formatSizeChars::String occurs on RealType, IntegerType;

aspect production floatType
top::RealType ::=
{
  top.maxStrWidth = ableC_Expr { MAX_FLOAT_STR_LEN };
  top.formatSizeChars = "";
}

aspect production doubleType
top::RealType ::=
{
  top.maxStrWidth = ableC_Expr { MAX_DOUBLE_STR_LEN };
  top.formatSizeChars = "";
}

aspect production longdoubleType
top::RealType ::=
{
  top.maxStrWidth = ableC_Expr { MAX_LONG_DOUBLE_STR_LEN };
  top.formatSizeChars = "L";
}

aspect production charType
top::IntegerType ::=
{
  top.maxStrWidth = ableC_Expr { MAX_CHAR_STR_LEN };
  top.formatSizeChars = "hh";
}

aspect production shortType
top::IntegerType ::=
{
  top.maxStrWidth = ableC_Expr { MAX_SHORT_STR_LEN };
  top.formatSizeChars = "h";
}

aspect production intType
top::IntegerType ::=
{
  top.maxStrWidth = ableC_Expr { MAX_INT_STR_LEN };
  top.formatSizeChars = "";
}

aspect production longType
top::IntegerType ::=
{
  top.maxStrWidth = ableC_Expr { MAX_LONG_STR_LEN };
  top.formatSizeChars = "l";
}

aspect production longlongType
top::IntegerType ::=
{
  top.maxStrWidth = ableC_Expr { MAX_LONGLONG_STR_LEN };
  top.formatSizeChars = "ll";
}

aspect production int128Type
top::IntegerType ::=
{
  top.maxStrWidth = ableC_Expr { MAX_LONGLONG_STR_LEN };
  top.formatSizeChars = "128";
}

aspect production extType
top::Type ::= quals::Qualifiers sub::ExtType
{
  propagate showErrors, strErrors;
  top.showMaxLenProd = sub.showMaxLenProd;
  top.showProd = sub.showProd;
  top.strProd = sub.strProd;
}

aspect default production
top::ExtType ::=
{
  top.showErrors :=
    \ env::Env ->
      [errFromOrigin(ambientOrigin(), s"show is not defined for type ${show(80, extType(nilQualifier(), ^top))}")];
  top.strErrors :=
    \ env::Env->
      [errFromOrigin(ambientOrigin(), s"str is not defined for type ${show(80, extType(nilQualifier(), ^top))}")];
  top.showMaxLenProd = error("Undefined");
  top.showProd = error("Undefined");
  top.strProd = error("Undefined");
}

aspect production stringType
top::ExtType ::=
{
  top.showErrors := checkStringHeaderDef("show_string", _);
  top.strErrors := \ _ -> [];
  top.showMaxLenProd =
    \ e::Expr ->
      directCallExpr(
        name("show_string_max_len"),
        consExpr(e, nilExpr()));
  top.showProd =
    \ buf::Expr e::Expr ->
      directCallExpr(
        name("show_string"),
        consExpr(buf, consExpr(e, nilExpr())));
  top.strProd = id;
}

aspect production refIdExtType
top::ExtType ::= kwd::StructOrEnumOrUnion  mn::Maybe<String>  refId::String
{
  local topType::Type = extType(top.givenQualifiers, ^top);
  top.showErrors :=
    \ env::Env ->
      checkStringHeaderDef("concat_string", env) ++
      case kwd, lookupRefId(refId, globalEnv(env)) of
      | structSEU(), structRefIdItem(decl) :: _ -> decl.showDeclErrors(env)
      | unionSEU(), unionRefIdItem(decl) :: _ -> decl.showDeclErrors(env)
      | structSEU(), _ -> [errFromOrigin(ambientOrigin(), s"struct ${tagName} does not have a (global) definition.")]
      | unionSEU(), _ -> [errFromOrigin(ambientOrigin(), s"union ${tagName} does not have a (global) definition.")]
      | _, _ -> error("Unexpected refIdExtType")
      end;
  top.showProd =
    case kwd of
    | structSEU() -> showStruct
    | unionSEU() -> showUnion
    | _ -> error("refIdExtType not a struct or union")
    end;
}

aspect production enumExtType
top::ExtType ::= ref::Decorated EnumDecl
{
  top.showErrors := checkStringHeaderDef("show_char_pointer", _);
  top.strErrors := checkStringHeaderDef("show_int", _);
  top.showMaxLenProd = \ _ -> mkIntConst(ref.maxEnumItemLen);
  top.showProd = ref.showProd;
  top.strProd = ref.strProd;
}
