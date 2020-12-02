grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

import edu:umn:cs:melt:ableC:abstractsyntax:overloadable;

abstract production stringTypeExpr
top::BaseTypeExpr ::= q::Qualifiers loc::Location
{
  top.pp = pp"string";
  forwards to
    if !null(lookupRefId("edu:umn:cs:melt:exts:ableC:string:string", top.env))
    then extTypeExpr(q, stringType())
    else errorTypeExpr([err(loc, "Missing include of string.xh")]);
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
  
  top.lEqProd = just(assignString(_, _, location=_));
  top.lAddProd = just(concatString(_, _, location=_));
  top.rAddProd = just(concatString(_, _, location=_));
  top.lSubProd = just(removeString(_, _, location=_));
  top.lMulProd = just(repeatString(_, _, location=_));
  -- Overloads for +=, -=, *=, automatically inferred from above
  top.lEqualsProd = just(equalsString(_, _, location=_));
  top.rEqualsProd = just(equalsString(_, _, location=_));
  -- Overload for != automatically inferred from above
  top.arraySubscriptProd = just(subscriptString(_, _, location=_));
  -- Better error message than default one about not being an lvalue
  top.addressOfArraySubscriptProd =
    just(\ Expr Expr loc::Location -> errorExpr([err(loc, "strings are immutable, cannot assign to index")], location=loc));
  top.callMemberProd = just(callMemberString(_, _, _, _, location=_));
  top.memberProd = just(memberString(_, _, _, location=_));
  top.exprInitProd = just(initString(_, location=_));
}

synthesized attribute showErrors::([Message] ::= Location Decorated Env) occurs on Type, BuiltinType, ExtType;
synthesized attribute strErrors::([Message] ::= Location Decorated Env) occurs on Type, BuiltinType, ExtType;
synthesized attribute showProd::(Expr ::= Expr) occurs on Type, BuiltinType, ExtType;
synthesized attribute strProd::(Expr ::= Expr) occurs on Type, BuiltinType, ExtType;

aspect default production
top::Type ::=
{
  top.showErrors =
    \ l::Location Decorated Env ->
      [err(l, s"show is not defined for type ${showType(top)}")];
  top.strErrors =
    \ l::Location Decorated Env ->
      [err(l, s"str is not defined for type ${showType(top)}")];
  top.showProd = error("Undefined");
  top.strProd = error("Undefined");
}

aspect production errorType
top::Type ::= 
{
  top.showErrors = \ l::Location Decorated Env -> [];
  top.strErrors = \ l::Location Decorated Env -> [];
  top.showProd = \ e::Expr -> errorExpr([], location=builtin);
  top.strProd = \ e::Expr -> errorExpr([], location=builtin);
}

aspect production pointerType
top::Type ::= quals::Qualifiers sub::Type
{
  top.showErrors =
    \ l::Location env::Decorated Env ->
      checkStringHeaderDef("show_char_pointer", l, env) ++
      case sub of
      | builtinType(_, voidType()) -> []
      | _ -> showErrors(l, env, sub)
      end;
  top.strErrors =
    \ l::Location env::Decorated Env ->
      checkStringHeaderDef("str_char_pointer", l, env) ++ sub.strErrors(l, env);
  top.showProd =
    case sub of
    | builtinType(_, signedType(charType())) -> showCharPointer(_, location=builtin)
    | builtinType(_, unsignedType(charType())) -> showCharPointer(_, location=builtin)
    | builtinType(_, voidType()) ->
      \ e::Expr ->
        directCallExpr(
          name("str_pointer", location=builtin),
          consExpr(e, nilExpr()),
          location=builtin)
    | _ -> showPointer(_, location=builtin)
    end;
  top.strProd =
    case sub of
    | builtinType(_, signedType(charType())) -> strCharPointer(_, location=builtin)
    | builtinType(_, unsignedType(charType())) -> strCharPointer(_, location=builtin)
    | _ ->
      \ e::Expr ->
        directCallExpr(
          name("str_pointer", location=builtin),
          consExpr(e, nilExpr()),
          location=builtin)
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
    \ l::Location Decorated Env ->
      [err(l, s"show is not defined for type ${showType(builtinType(nilQualifier(), top))}")];
  top.strErrors =
    \ l::Location Decorated Env ->
      [err(l, s"str is not defined for type ${showType(builtinType(nilQualifier(), top))}")];
  top.showProd = error("Undefined");
  top.strProd = error("Undefined");
}

aspect production boolType
top::BuiltinType ::=
{
  top.showErrors = checkStringHeaderDef("show_bool", _, _);
  top.strErrors = checkStringHeaderDef("show_bool", _, _);
  top.showProd =
    \ e::Expr ->
      directCallExpr(
        name("show_bool", location=builtin),
        consExpr(e, nilExpr()),
        location=builtin);
  top.strProd =
    \ e::Expr ->
      directCallExpr(
        name("show_bool", location=builtin),
        consExpr(e, nilExpr()),
        location=builtin);
}

aspect production realType
top::BuiltinType ::= sub::RealType
{
  top.showErrors = checkStringHeaderDef("show_float", _, _);
  top.strErrors = checkStringHeaderDef("show_float", _, _);
  top.showProd =
    \ e::Expr ->
      directCallExpr(
        name("show_float", location=builtin),
        consExpr(e, nilExpr()),
        location=builtin);
  top.strProd =
    \ e::Expr ->
      directCallExpr(
        name("show_float", location=builtin),
        consExpr(e, nilExpr()),
        location=builtin);
}

aspect production signedType
top::BuiltinType ::= sub::IntegerType
{
  top.showErrors = checkStringHeaderDef("show_int", _, _);
  top.strErrors = checkStringHeaderDef("show_int", _, _);
  top.showProd =
    case sub of
    | charType() ->
      \ e::Expr ->
        directCallExpr(
          name("show_char", location=builtin),
          consExpr(e, nilExpr()),
          location=builtin)
    | _ ->
      \ e::Expr ->
        directCallExpr(
          name("show_int", location=builtin),
          consExpr(e, nilExpr()),
          location=builtin)
    end;
  top.strProd =
    case sub of
    | charType() ->
      \ e::Expr ->
        directCallExpr(
          name("str_char", location=builtin),
          consExpr(e, nilExpr()),
          location=builtin)
    | _ ->
      \ e::Expr ->
        directCallExpr(
          name("show_int", location=builtin),
          consExpr(e, nilExpr()),
          location=builtin)
    end;
}

aspect production unsignedType
top::BuiltinType ::= sub::IntegerType
{
  top.showErrors = checkStringHeaderDef("show_int", _, _);
  top.strErrors = checkStringHeaderDef("show_int", _, _);
  top.showProd =
    case sub of
    | charType() ->
      \ e::Expr ->
        directCallExpr(
          name("show_char", location=builtin),
          consExpr(e, nilExpr()),
          location=builtin)
    | _ ->
      \ e::Expr ->
        directCallExpr(
          name("show_int", location=builtin),
          consExpr(e, nilExpr()),
          location=builtin)
    end;
  top.strProd =
    case sub of
    | charType() ->
      \ e::Expr ->
        directCallExpr(
          name("str_char", location=builtin),
          consExpr(e, nilExpr()),
          location=builtin)
    | _ ->
      \ e::Expr ->
        directCallExpr(
          name("show_int", location=builtin),
          consExpr(e, nilExpr()),
          location=builtin)
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
    \ l::Location Decorated Env ->
      [err(l, s"show is not defined for type ${showType(extType(nilQualifier(), top))}")];
  top.strErrors =
    \ l::Location Decorated Env ->
      [err(l, s"str is not defined for type ${showType(extType(nilQualifier(), top))}")];
  top.showProd = error("Undefined");
  top.strProd = error("Undefined");
}

aspect production stringType
top::ExtType ::=
{
  top.showErrors = checkStringHeaderDef("show_string", _, _);
  top.strErrors = \ Location Decorated Env -> [];
  top.showProd =
    \ e::Expr ->
      directCallExpr(
        name("show_string", location=builtin),
        consExpr(e, nilExpr()),
        location=builtin);
  top.strProd = \ e::Expr -> e;
}

aspect production refIdExtType
top::ExtType ::= kwd::StructOrEnumOrUnion  mn::Maybe<String>  refId::String
{
  local topType::Type = extType(top.givenQualifiers, top);
  top.showErrors =
    \ l::Location env::Decorated Env ->
      checkStringHeaderDef("concat_string", l, env) ++
      case kwd, lookupRefId(refId, globalEnv(env)) of
      | structSEU(), structRefIdItem(decl) :: _ -> decl.showDeclErrors(l, env)
      | unionSEU(), unionRefIdItem(decl) :: _ -> decl.showDeclErrors(l, env)
      | structSEU(), _ -> [err(l, s"struct ${tagName} does not have a (global) definition.")]
      | unionSEU(), _ -> [err(l, s"union ${tagName} does not have a (global) definition.")]
      | _, _ -> error("Unexpected refIdExtType")
      end;
  top.showProd =
    case kwd of
    | structSEU() -> showStruct(_, location=builtin)
    | unionSEU() -> showUnion(_, location=builtin)
    end;
}

aspect production enumExtType
top::ExtType ::= ref::Decorated EnumDecl
{
  top.showErrors = checkStringHeaderDef("show_char_pointer", _, _);
  top.strErrors = checkStringHeaderDef("show_int", _, _);
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
