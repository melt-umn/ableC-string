grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;
imports edu:umn:cs:melt:ableC:abstractsyntax:substitution;
imports edu:umn:cs:melt:ableC:abstractsyntax:overloadable as ovrld;
--imports edu:umn:cs:melt:ableC:abstractsyntax:debug;

abstract production showExpr
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local localErrors::[Message] = e.errors;
  local fwrd::Expr =
    case e.typerep.showProd of
      just(p) -> p(e, top.location)
    | nothing() -> errorExpr([err(e.location, s"show of ${showType(e.typerep)} not defined")], location=builtin)
    end;
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production showString
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local localErrors::[Message] =
    checkStringType(e.typerep, "show", top.location) ++
    checkStringHeaderDef("showString", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("showString", location=builtin),
      consExpr(e, nilExpr()),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production showCharPointer
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local localErrors::[Message] =
    checkStringHeaderDef("showCharPointer", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("showCharPointer", location=builtin),
      consExpr(e, nilExpr()),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production showChar
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local localErrors::[Message] =
    checkStringHeaderDef("showChar", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("showChar", location=builtin),
      consExpr(e, nilExpr()),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production showInt
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local localErrors::[Message] =
    checkStringHeaderDef("showInt", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("showInt", location=builtin),
      consExpr(e, nilExpr()),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production showFloat
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local localErrors::[Message] =
    checkStringHeaderDef("showFloat", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("showFloat", location=builtin),
      consExpr(e, nilExpr()),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production showPointer
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local localErrors::[Message] =
    checkStringHeaderDef("_showPointer", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("_showPointer", location=builtin),
      consExpr(
        stringLiteral(s"\"${showType(e.typerep)}\"", location=builtin),
        consExpr(
          e,
          nilExpr())),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production strExpr
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"str(${e.pp})";
  
  local localErrors::[Message] = e.errors;
  local fwrd::Expr =
    case e.typerep.strProd of
      just(p) -> p(e, top.location)
    | nothing() -> errorExpr([err(e.location, s"str of ${showType(e.typerep)} not defined")], location=builtin)
    end;
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production strString
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"str(${e.pp})";
  
  forwards to e;
}

abstract production strCharPointer
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"str(${e.pp})";
  
  local localErrors::[Message] =
    checkStringHeaderDef("strCharPointer", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("strCharPointer", location=builtin),
      consExpr(e, nilExpr()),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production strChar
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"str(${e.pp})";
  
  local localErrors::[Message] =
    checkStringHeaderDef("strChar", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("strChar", location=builtin),
      consExpr(e, nilExpr()),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production strPointer
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"str(${e.pp})";
  
  local localErrors::[Message] =
    checkStringHeaderDef("strPointer", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("strPointer", location=builtin),
      consExpr(e, nilExpr()),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production assignString
top::Expr ::= lhs::Expr rhs::Expr
{
  propagate substituted;
  top.pp = pp"${lhs.pp} = ${rhs.pp}";
  
  forwards to
    eqExpr(
      lhs,
      strExpr(rhs, location=builtin),
      location=builtin);
}

abstract production appendString
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp} + ${e2.pp}";
  
  local localErrors::[Message] =
    checkStringHeaderDef("_append_string", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("_append_string", location=builtin),
      consExpr(
        strExpr(e1, location=builtin),
        consExpr(
          strExpr(e2, location=builtin),
          nilExpr())),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production removeString
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp} - ${e2.pp}";
  
  local localErrors::[Message] =
    checkStringHeaderDef("_remove_string", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("_remove_string", location=builtin),
      consExpr(
        strExpr(e1, location=builtin),
        consExpr(
          strExpr(e2, location=builtin),
          nilExpr())),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production repeatString
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp} * ${e2.pp}";
  
  local localErrors::[Message] =
    checkStringHeaderDef("_repeat_string", top.location, top.env) ++
    checkStringType(e1.typerep, "*", top.location) ++
    if e2.typerep.isIntegerType
    then []
    else [err(e2.location, s"string repeat must have integer type, but got ${showType(e2.typerep)}")];
  local fwrd::Expr =
    directCallExpr(
      name("_repeat_string", location=builtin),
      consExpr(e1, consExpr(e2, nilExpr())),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production equalsString
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp} == ${e2.pp}";
  
  local localErrors::[Message] =
    checkStringHeaderDef("_equals_string", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("_equals_string", location=builtin),
      consExpr(
        strExpr(e1, location=builtin),
        consExpr(
          strExpr(e2, location=builtin),
          nilExpr())),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production subscriptString
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp}[${e2.pp}]";
  
  local localErrors::[Message] =
    checkStringHeaderDef("_index_string", top.location, top.env) ++
    checkStringType(e1.typerep, "[]", top.location) ++
    if e2.typerep.isIntegerType
    then []
    else [err(e2.location, s"string index must have integer type, but got ${showType(e2.typerep)}")];
  local fwrd::Expr =
    directCallExpr(
      name("_index_string", location=builtin),
      consExpr(e1, consExpr(e2, nilExpr())),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production callMemberString
top::Expr ::= lhs::Expr deref::Boolean rhs::Name a::Exprs
{
  propagate substituted;
  
  forwards to
    case rhs.name of
      "substring" -> substringString(lhs, a, location=top.location)
    | n -> errorExpr([err(rhs.location, s"string does not have field ${n}")], location=builtin)
    end;
}

abstract production memberString
top::Expr ::= lhs::Expr deref::Boolean rhs::Name
{
  propagate substituted;
  top.pp = parens(ppConcat([lhs.pp, text(if deref then "->" else "."), rhs.pp]));

  local localErrors::[Message] =
    (if !null(lookupRefId("edu:umn:cs:melt:exts:ableC:string:string", top.env))
     then []
     else [err(top.location, "Missing include of string.xh")]) ++
    checkStringType(lhs.typerep, ".", top.location) ++
    (if rhs.name == "length" || rhs.name == "text"
     then []
     else [err(rhs.location, s"string does not have member ${rhs.name}")]);
  local fwrd::Expr =
    memberExpr(
      explicitCastExpr(
        typeName(
          tagReferenceTypeExpr(
            consQualifier(constQualifier(location=builtin), nilQualifier()), structSEU(),
            name("_string_s", location=builtin)),
          baseTypeExpr()),
        lhs,
        location=builtin),
      false, rhs,
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production substringString
top::Expr ::= e1::Expr a::Exprs
{
  propagate substituted;
  top.pp = pp"${e1.pp}.substring(${ppImplode(pp", ", a.pps)}";
  
  a.expectedTypes = -- size_t
    [builtinType(nilQualifier(), unsignedType(longType())),
     builtinType(nilQualifier(), unsignedType(longType()))];
  a.argumentPosition = 1;
  a.callExpr = top; -- Doesn't really matter, just needs location
  a.callVariadic = false;
  local localErrors::[Message] =
    checkStringHeaderDef("_substring", top.location, top.env) ++
    checkStringType(e1.typerep, "substring", top.location) ++
    a.argumentErrors;
  local fwrd::Expr =
    directCallExpr(
      name("_substring", location=builtin),
      consExpr(e1, a),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

-- Check the given env for the given function name
function checkStringHeaderDef
[Message] ::= n::String loc::Location env::Decorated Env
{
  return
    if !null(lookupValue(n, env))
    then []
    else [err(loc, "Missing include of string.xh")];
}

-- Check that operand has string type
function checkStringType
[Message] ::= t::Type op::String loc::Location
{
  return
    if typeAssignableTo(extType(nilQualifier(), stringType()), t)
    then []
    else [err(loc, s"Operand to ${op} expected string type (got ${showType(t)})")];
}

global builtin::Location = builtinLoc("string");
