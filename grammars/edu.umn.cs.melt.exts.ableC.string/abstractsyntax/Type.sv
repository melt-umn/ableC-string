grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

import edu:umn:cs:melt:ableC:abstractsyntax:overloadable;

abstract production stringTypeExpr
top::BaseTypeExpr ::= q::Qualifiers
{
  top.pp = pp"string";
  forwards to
    if !null(lookupRefId("edu:umn:cs:melt:exts:ableC:string:string", top.env))
    then extTypeExpr(q, stringType())
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
  
  top.lEqProd = just(assignString);
  top.lAddProd = just(concatString);
  top.rAddProd = just(concatString);
  top.lSubProd = just(removeString);
  top.lMulProd = just(repeatString);
  -- Overloads for +=, -=, *=, automatically inferred from above
  top.lEqualsProd = just(equalsString);
  top.rEqualsProd = just(equalsString);
  -- Overload for != automatically inferred from above
  top.arraySubscriptProd = just(subscriptString);
  -- Better error message than default one about not being an lvalue
  top.addressOfArraySubscriptProd =
    just(\ Expr Expr -> errorExpr([errFromOrigin(ambientOrigin(), "strings are immutable, cannot assign to index")]));
  top.callMemberProd = just(callMemberString);
  top.memberProd = just(memberString);
  top.exprInitProd = just(initString);
}

synthesized attribute showErrors::([Message] ::= Decorated Expr with {env}) occurs on Type, BuiltinType, ExtType;
synthesized attribute strErrors::([Message] ::= Decorated Expr with {env}) occurs on Type, BuiltinType, ExtType;
synthesized attribute showProd::(Expr ::= Expr) occurs on Type, BuiltinType, ExtType;
synthesized attribute strProd::(Expr ::= Expr) occurs on Type, BuiltinType, ExtType;

aspect default production
top::Type ::=
{
  top.showErrors =
    \ e::Decorated Expr with {env} ->
      [errFromOrigin(e, s"show is not defined for type ${showType(top)}")];
  top.strErrors =
    \ e::Decorated Expr with {env} ->
      [errFromOrigin(e, s"str is not defined for type ${showType(top)}")];
  top.showProd = error("Undefined");
  top.strProd = error("Undefined");
}

aspect production errorType
top::Type ::= 
{
  top.showErrors = \ e::Decorated Expr with {env} -> [];
  top.strErrors = \ e::Decorated Expr with {env} -> [];
  top.showProd = \ e::Expr -> errorExpr([]);
  top.strProd = \ e::Expr -> errorExpr([]);
}

aspect production pointerType
top::Type ::= quals::Qualifiers sub::Type
{
  top.showErrors =
    \ e::Decorated Expr with {env} ->
      checkStringHeaderDef("show_char_pointer", e.env) ++
      case sub of
      | builtinType(_, voidType()) -> []
      | functionType(_, _, _) -> []
      | _ -> showErrors(e, sub)
      end;
  top.strErrors =
    \ e::Decorated Expr with {env} ->
      checkStringHeaderDef("str_char_pointer", e.env) ++ sub.strErrors(e);
  top.showProd =
    case sub of
    | builtinType(_, signedType(charType())) -> showCharPointer
    | builtinType(_, unsignedType(charType())) -> showCharPointer
    | builtinType(_, voidType()) -> showOpaquePointer
    | functionType(_, _, _) -> showOpaquePointer
    | _ -> showPointer
    end;
  top.strProd =
    case sub of
    | builtinType(_, signedType(charType())) -> strCharPointer
    | builtinType(_, unsignedType(charType())) -> strCharPointer
    | _ ->
      \ e::Expr ->
        directCallExpr(
          name("str_pointer"),
          consExpr(e, nilExpr()))
    end;
}

aspect production builtinType
top::Type ::= quals::Qualifiers sub::BuiltinType
{
  top.showErrors = sub.showErrors;
  top.strErrors = sub.strErrors;
  top.showProd = sub.showProd;
  top.strProd = sub.strProd;
}

aspect default production
top::BuiltinType ::=
{
  top.showErrors =
    \ e::Decorated Expr with {env} ->
      [errFromOrigin(e, s"show is not defined for type ${showType(builtinType(nilQualifier(), top))}")];
  top.strErrors =
    \ e::Decorated Expr with {env} ->
      [errFromOrigin(e, s"str is not defined for type ${showType(builtinType(nilQualifier(), top))}")];
  top.showProd = error("Undefined");
  top.strProd = error("Undefined");
}

aspect production boolType
top::BuiltinType ::=
{
  top.showErrors = \ e::Decorated Expr with {env} -> checkStringHeaderDef("show_bool", e.env);
  top.strErrors = \ e::Decorated Expr with {env} -> checkStringHeaderDef("show_bool", e.env);
  top.showProd =
    \ e::Expr ->
      directCallExpr(
        name("show_bool"),
        consExpr(e, nilExpr()));
  top.strProd =
    \ e::Expr ->
      directCallExpr(
        name("show_bool"),
        consExpr(e, nilExpr()));
}

aspect production realType
top::BuiltinType ::= sub::RealType
{
  top.showErrors = \ e::Decorated Expr with {env} -> checkStringHeaderDef("show_float", e.env);
  top.strErrors = \ e::Decorated Expr with {env} -> checkStringHeaderDef("show_float", e.env);
  top.showProd =
    \ e::Expr ->
      directCallExpr(
        name("show_float"),
        consExpr(e, nilExpr()));
  top.strProd =
    \ e::Expr ->
      directCallExpr(
        name("show_float"),
        consExpr(e, nilExpr()));
}

aspect production signedType
top::BuiltinType ::= sub::IntegerType
{
  top.showErrors = \ e::Decorated Expr with {env} -> checkStringHeaderDef("show_int", e.env);
  top.strErrors = \ e::Decorated Expr with {env} -> checkStringHeaderDef("show_int", e.env);
  top.showProd =
    case sub of
    | charType() ->
      \ e::Expr ->
        directCallExpr(
          name("show_char"),
          consExpr(e, nilExpr()))
    | _ ->
      \ e::Expr ->
        directCallExpr(
          name("show_int"),
          consExpr(e, nilExpr()))
    end;
  top.strProd =
    case sub of
    | charType() ->
      \ e::Expr ->
        directCallExpr(
          name("str_char"),
          consExpr(e, nilExpr()))
    | _ ->
      \ e::Expr ->
        directCallExpr(
          name("show_int"),
          consExpr(e, nilExpr()))
    end;
}

aspect production unsignedType
top::BuiltinType ::= sub::IntegerType
{
  top.showErrors = \ e::Decorated Expr with {env} -> checkStringHeaderDef("show_int", e.env);
  top.strErrors = \ e::Decorated Expr with {env} -> checkStringHeaderDef("show_int", e.env);
  top.showProd =
    case sub of
    | charType() ->
      \ e::Expr ->
        directCallExpr(
          name("show_char"),
          consExpr(e, nilExpr()))
    | _ ->
      \ e::Expr ->
        directCallExpr(
          name("show_int"),
          consExpr(e, nilExpr()))
    end;
  top.strProd =
    case sub of
    | charType() ->
      \ e::Expr ->
        directCallExpr(
          name("str_char"),
          consExpr(e, nilExpr()))
    | _ ->
      \ e::Expr ->
        directCallExpr(
          name("show_int"),
          consExpr(e, nilExpr()))
    end;
}

aspect production extType
top::Type ::= quals::Qualifiers sub::ExtType
{
  top.showErrors = sub.showErrors;
  top.strErrors = sub.strErrors;
  top.showProd = sub.showProd;
  top.strProd = sub.strProd;
}

aspect default production
top::ExtType ::=
{
  top.showErrors =
    \ e::Decorated Expr with {env} ->
      [errFromOrigin(e, s"show is not defined for type ${showType(extType(nilQualifier(), top))}")];
  top.strErrors =
    \ e::Decorated Expr with {env}->
      [errFromOrigin(e, s"str is not defined for type ${showType(extType(nilQualifier(), top))}")];
  top.showProd = error("Undefined");
  top.strProd = error("Undefined");
}

aspect production stringType
top::ExtType ::=
{
  top.showErrors = \ e::Decorated Expr with {env} -> checkStringHeaderDef("show_string", e.env);
  top.strErrors = \ Decorated Expr with {env} -> [];
  top.showProd =
    \ e::Expr ->
      directCallExpr(
        name("show_string"),
        consExpr(e, nilExpr()));
  top.strProd = \ e::Expr -> e;
}

aspect production refIdExtType
top::ExtType ::= kwd::StructOrEnumOrUnion  mn::Maybe<String>  refId::String
{
  local topType::Type = extType(top.givenQualifiers, top);
  top.showErrors =
    \ e::Decorated Expr with {env} ->
      checkStringHeaderDef("concat_string", e.env) ++
      case kwd, lookupRefId(refId, globalEnv(e.env)) of
      | structSEU(), structRefIdItem(decl) :: _ -> decl.showDeclErrors(e)
      | unionSEU(), unionRefIdItem(decl) :: _ -> decl.showDeclErrors(e)
      | structSEU(), _ -> [errFromOrigin(e, s"struct ${tagName} does not have a (global) definition.")]
      | unionSEU(), _ -> [errFromOrigin(e, s"union ${tagName} does not have a (global) definition.")]
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
  top.showErrors = \ e::Decorated Expr with {env} -> checkStringHeaderDef("show_char_pointer", e.env);
  top.strErrors = \ e::Decorated Expr with {env} -> checkStringHeaderDef("show_int", e.env);
  top.showProd =
    \ e::Expr ->
      ableC_Expr {
        ({$directTypeExpr{extType(nilQualifier(), top)} _enum_val = $Expr{e};
          $Expr{ref.showTransform};})
      };
  top.strProd =
    \ e::Expr ->
      ableC_Expr {
        ({$directTypeExpr{extType(nilQualifier(), top)} _enum_val = $Expr{e};
          $Expr{ref.strTransform};})
      };
}
