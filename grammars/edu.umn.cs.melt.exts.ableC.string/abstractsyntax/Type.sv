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
  top.lEqualsProd = just(equalsString);
  top.rEqualsProd = just(equalsString);
  top.arraySubscriptProd = just(subscriptString);
  -- Better error message than default one about not being an lvalue
  top.addressOfArraySubscriptProd =
    just(\ Expr Expr -> errorExpr([errFromOrigin(ambientOrigin(), "strings are immutable, cannot assign to index")]));
  top.memberProd = just(memberString);
  top.memberCallProd = just(memberCallString);
  top.exprInitProd = just(initString);
}

-- Compute the errors for showing/converting a type to a string.
monoid attribute showErrors::([Message] ::= Env) with \ _ -> [], joinShowErrors occurs on Type, BuiltinType, ExtType;
monoid attribute strErrors::([Message] ::= Env) with \ _ -> [], joinShowErrors occurs on Type, BuiltinType, ExtType;

fun joinShowErrors ([Message] ::= Env) ::= e1::([Message] ::= Env) e2::([Message] ::= Env) =
  \ env::Env -> e1(env) ++ e2(env);

-- Directly coerce a value of some type to a string.
synthesized attribute directStrProd::(Expr ::= Expr) occurs on Type, BuiltinType, ExtType;

-- Compute the maximum length of the string coerced from a value.
synthesized attribute strMaxLenProd::(Expr ::= Expr) occurs on Type, BuiltinType, ExtType;

-- Write a string coerced from a value to a buffer, returning the string length.
synthesized attribute strProd::(Expr ::= Expr Expr) occurs on Type, BuiltinType, ExtType;

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
  top.directStrProd = directStrExpr(_, top.strMaxLenProd, top.strProd);
  top.strMaxLenProd = error("Undefined");
  top.strProd = error("Undefined");
  top.showMaxLenProd = error("Undefined");
  top.showProd = error("Undefined");
}

aspect production errorType
top::Type ::= 
{
  propagate showErrors, strErrors;
  top.directStrProd = \ _ -> errorExpr([]);
  top.strMaxLenProd = \ _ -> errorExpr([]);
  top.strProd = \ _ _ -> errorExpr([]);
  top.showMaxLenProd = \ _ -> errorExpr([]);
  top.showProd = \ _ _ -> errorExpr([]);
}

aspect production pointerType
top::Type ::= quals::Qualifiers sub::Type
{
  top.showErrors :=
    \ env::Env ->
      checkStringHeaderDef(env) ++
      case sub of
      | builtinType(_, voidType()) -> []
      | functionType(_, _, _) -> []
      | _ -> showErrors(env, ^sub)
      end;
  top.strErrors :=
    \ env::Env ->
      checkStringHeaderDef(env) ++ sub.strErrors(env);
  top.directStrProd =
    case sub of
    | builtinType(_, signedType(charType())) -> directStrCharPointer
    | builtinType(_, unsignedType(charType())) -> directStrCharPointer
    | _ -> directStrExpr(_, top.strMaxLenProd, top.strProd)
    end;
  top.strMaxLenProd =
    case sub of
    | builtinType(_, signedType(charType())) -> strCharPointerMaxLen
    | builtinType(_, unsignedType(charType())) -> strCharPointerMaxLen
    | _ -> \ _ -> ableC_Expr { MAX_POINTER_STR_LEN }
    end;
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
    | _ -> showPointerMaxLen
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
  top.directStrProd = sub.directStrProd;
  top.strMaxLenProd = sub.strMaxLenProd;
  top.strProd = sub.strProd;
  top.showMaxLenProd = sub.showMaxLenProd;
  top.showProd = sub.showProd;
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
  top.directStrProd = directStrExpr(_, top.strMaxLenProd, top.strProd);
  top.strMaxLenProd = error("Undefined");
  top.strProd = error("Undefined");
  top.showMaxLenProd = error("Undefined");
  top.showProd = error("Undefined");
}

aspect production boolType
top::BuiltinType ::=
{
  top.showErrors := checkStringHeaderDef;
  top.strErrors := checkStringHeaderDef;
  top.directStrProd = directStrBool;
  top.strMaxLenProd = \ _ -> mkIntConst(5);
  top.strProd = strBool;
  top.showMaxLenProd = top.strMaxLenProd;
  top.showProd = top.strProd;
}

aspect production realType
top::BuiltinType ::= sub::RealType
{
  top.showErrors := checkStringHeaderDef;
  top.strErrors := checkStringHeaderDef;
  top.strMaxLenProd = \ _ -> sub.maxStrWidth;
  top.strProd = strNum(_, _, s"%${sub.formatSizeChars}g");
  top.showMaxLenProd = top.strMaxLenProd;
  top.showProd = top.strProd;
}

aspect production signedType
top::BuiltinType ::= sub::IntegerType
{
  top.showErrors := checkStringHeaderDef;
  top.strErrors := checkStringHeaderDef;
  top.strMaxLenProd = \ _ ->
    case sub of
    | charType() -> mkIntConst(1)
    | _ -> sub.maxStrWidth
    end;
  top.strProd = 
    case sub of
    | charType() -> strChar
    | _ -> strNum(_, _, s"%${sub.formatSizeChars}d")
    end;
  top.showMaxLenProd =
    case sub of
    | charType() -> \ _ -> mkIntConst(5)
    | _ -> top.strMaxLenProd
    end;
  top.showProd =
    case sub of
    | charType() ->
      \ buf::Expr e::Expr ->
        directCallExpr(
          name("show_char"),
          consExpr(buf, consExpr(e, nilExpr())))
    | _ -> top.strProd
    end;
}

aspect production unsignedType
top::BuiltinType ::= sub::IntegerType
{
  top.showErrors := checkStringHeaderDef;
  top.strErrors := checkStringHeaderDef;
  top.strMaxLenProd = \ _ ->
    case sub of
    | charType() -> mkIntConst(1)
    | _ -> sub.maxStrWidth
    end;
  top.strProd = 
    case sub of
    | charType() -> strChar
    | _ -> strNum(_, _, s"%${sub.formatSizeChars}u")
    end;
  top.showMaxLenProd =
    case sub of
    | charType() -> \ _ -> mkIntConst(5)
    | _ -> top.strMaxLenProd
    end;
  top.showProd =
    case sub of
    | charType() ->
      \ buf::Expr e::Expr ->
        directCallExpr(
          name("show_char"),
          consExpr(buf, consExpr(e, nilExpr())))
    | _ -> top.strProd
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
  top.directStrProd = sub.directStrProd;
  top.strMaxLenProd = sub.strMaxLenProd;
  top.strProd = sub.strProd;
  top.showMaxLenProd = sub.showMaxLenProd;
  top.showProd = sub.showProd;
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
  top.directStrProd = directStrExpr(_, top.strMaxLenProd, top.strProd);
  top.strMaxLenProd = error("Undefined");
  top.strProd = error("Undefined");
  top.showMaxLenProd = error("Undefined");
  top.showProd = error("Undefined");
}

aspect production stringType
top::ExtType ::=
{
  top.showErrors := checkStringHeaderDef;
  top.strErrors := \ _ -> [];
  top.directStrProd = id;
  top.strMaxLenProd = strStringMaxLen;
  top.strProd = strString;
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
}

aspect production refIdExtType
top::ExtType ::= kwd::StructOrEnumOrUnion  mn::Maybe<String>  refId::String
{
  local topType::Type = extType(top.givenQualifiers, ^top);
  top.showErrors :=
    \ env::Env ->
      checkStringHeaderDef(env) ++
      case kwd, lookupRefId(refId, globalEnv(env)) of
      | structSEU(), structRefIdItem(decl) :: _ -> decl.showDeclErrors(env)
      | unionSEU(), unionRefIdItem(decl) :: _ -> decl.showDeclErrors(env)
      | structSEU(), _ -> [errFromOrigin(ambientOrigin(), s"struct ${tagName} does not have a (global) definition.")]
      | unionSEU(), _ -> [errFromOrigin(ambientOrigin(), s"union ${tagName} does not have a (global) definition.")]
      | _, _ -> error("Unexpected refIdExtType")
      end;
  top.showMaxLenProd =
    case kwd of
    | structSEU() -> showStructMaxLen
    | unionSEU() -> showUnionMaxLen
    | _ -> error("refIdExtType not a struct or union")
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
  top.showErrors := checkStringHeaderDef;
  top.strErrors := checkStringHeaderDef;
  top.directStrProd = ref.directStrProd;
  top.strMaxLenProd = \ _ -> mkIntConst(ref.maxEnumItemLen);
  top.strProd = \ buf::Expr e::Expr -> ableC_Expr { sprintf($Expr{buf}, "%s", ref.directStrProd(e)) };
  top.showMaxLenProd = \ _ -> mkIntConst(ref.maxEnumItemLen);
  top.showProd = ref.showProd;
}
