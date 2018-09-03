grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

import edu:umn:cs:melt:ableC:abstractsyntax:overloadable;

abstract production stringTypeExpr
top::BaseTypeExpr ::= q::Qualifiers loc::Location
{
  propagate substituted;
  forwards to
    if !null(lookupRefId("edu:umn:cs:melt:exts:ableC:string:string", top.env))
    then extTypeExpr(q, stringType())
    else errorTypeExpr([err(loc, "Missing include of string.xh")]);
}

abstract production stringType
top::ExtType ::=
{
  propagate substituted;
  top.pp = pp"string";
  top.host =
    tagType(
      top.givenQualifiers,
      refIdTagType(structSEU(), "_string_s",
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
  top.addressOfArraySubscriptProd =
    just(\ Expr Expr loc::Location -> errorExpr([err(loc, "strings are immutable, cannot assign to index")], location=loc));
  top.callMemberProd = just(callMemberString(_, _, _, _, location=_));
  top.memberProd = just(memberString(_, _, _, location=_));
}

synthesized attribute showProd::Maybe<(Expr ::= Expr Location)> occurs on Type, BuiltinType, ExtType;
synthesized attribute pointerShowProd::Maybe<(Expr ::= Expr Location)> occurs on Type, BuiltinType;
synthesized attribute strProd::Maybe<(Expr ::= Expr Location)> occurs on Type, BuiltinType, ExtType;
synthesized attribute pointerStrProd::Maybe<(Expr ::= Expr Location)> occurs on Type, BuiltinType;

aspect default production
top::Type ::=
{
  top.showProd = nothing();
  top.pointerShowProd = nothing();
  top.strProd = nothing();
  top.pointerStrProd = nothing();
}

aspect production errorType
top::Type ::= 
{
  top.showProd = just(\ e::Expr l::Location -> errorExpr([], location=l));
  top.strProd = just(\ e::Expr l::Location -> errorExpr([], location=l));
}

aspect production pointerType
top::Type ::= quals::Qualifiers sub::Type
{
  top.showProd =
    case sub.pointerShowProd of
      just(prod) -> just(prod)
    | nothing() -> just(showPointer(_, location=_))
    end;
  top.strProd =
    case sub.pointerStrProd of
      just(prod) -> just(prod)
    | nothing() -> just(strPointer(_, location=_))
    end;
}

aspect default production
top::BuiltinType ::=
{
  top.showProd = nothing();
  top.pointerShowProd = nothing();
  top.strProd = nothing();
  top.pointerStrProd = nothing();
}

aspect production builtinType
top::Type ::= quals::Qualifiers sub::BuiltinType
{
  top.showProd = sub.showProd;
  top.pointerShowProd = sub.pointerShowProd;
  top.strProd = sub.strProd;
  top.pointerStrProd = sub.pointerStrProd;
}

aspect production realType
top::BuiltinType ::= sub::RealType
{
  top.showProd = just(showFloat(_, location=_));
  top.strProd = just(showFloat(_, location=_));
}

aspect production signedType
top::BuiltinType ::= sub::IntegerType
{
  top.showProd =
    case sub of
      charType() -> just(showChar(_, location=_))
    | _ -> just(showInt(_, location=_))
    end;
  top.pointerShowProd =
    case sub of
      charType() -> just(showCharPointer(_, location=_))
    | _ -> nothing()
    end;
  top.strProd =
    case sub of
      charType() -> just(strChar(_, location=_))
    | _ -> just(showInt(_, location=_))
    end;
  top.pointerStrProd =
    case sub of
      charType() -> just(strCharPointer(_, location=_))
    | _ -> nothing()
    end;
}

aspect production unsignedType
top::BuiltinType ::= sub::IntegerType
{
  top.showProd =
    case sub of
      charType() -> just(showChar(_, location=_))
    | _ -> just(showInt(_, location=_))
    end;
  top.pointerShowProd =
    case sub of
      charType() -> just(showCharPointer(_, location=_))
    | _ -> nothing()
    end;
  top.strProd =
    case sub of
      charType() -> just(strChar(_, location=_))
    | _ -> just(showInt(_, location=_))
    end;
  top.pointerStrProd =
    case sub of
      charType() -> just(strCharPointer(_, location=_))
    | _ -> nothing()
    end;
}

aspect default production
top::ExtType ::=
{
  top.showProd = nothing();
  top.strProd = nothing();
}

aspect production extType
top::Type ::= quals::Qualifiers sub::ExtType
{
  top.showProd = sub.showProd;
  top.strProd = sub.strProd;
}

aspect production stringType
top::ExtType ::=
{
  top.showProd = just(showString(_, location=_));
  top.strProd = just(strString(_, location=_));
}
