grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;
imports edu:umn:cs:melt:ableC:abstractsyntax:substitution;
imports edu:umn:cs:melt:ableC:abstractsyntax:builtins;
imports edu:umn:cs:melt:ableC:abstractsyntax:overloadable as ovrld;
--imports edu:umn:cs:melt:ableC:abstractsyntax:debug;

aspect function getInitialEnvDefs
[Def] ::=
{
  d <-
    [valueDef(
       "show",
       builtinFunctionValueItem(
         functionType(extType(nilQualifier(), stringType()), noProtoFunctionType(), nilQualifier()),
         singleArgExtCallExpr(showExpr(_, location=_), _, _, location=_))),
     valueDef(
       "str",
       builtinFunctionValueItem(
         functionType(extType(nilQualifier(), stringType()), noProtoFunctionType(), nilQualifier()),
         singleArgExtCallExpr(strExpr(_, location=_), _, _, location=_)))];
}

abstract production singleArgExtCallExpr
top::Expr ::= handler::(Expr ::= Expr Location) f::Name a::Exprs
{
  propagate substituted;
  top.pp = pp"${f.pp}(${ppImplode(pp", ", a.pps)})";
  local localErrors::[Message] =
    a.errors ++
    if a.count != 1
    then [err(top.location, s"${f.name} expected only 1 argument, got ${toString(a.count)}")]
    else [];
  local fwrd::Expr =
    case a of
    | consExpr(e, _) -> handler(decExpr(e, location=e.location), top.location)
    end;
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production showExpr
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local type::Type = e.typerep.defaultFunctionArrayLvalueConversion;
  local localErrors::[Message] = e.errors ++ type.showErrors(e.location, e.env);
  local fwrd::Expr = type.showProd(decExpr(e, location=builtin));
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production showCharPointer
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  forwards to
    ableC_Expr {
      // Cast in case argument is const char *
      show_char_pointer((char *)$Expr{e})
    };
}

synthesized attribute showTransform::Expr;

attribute showTransform occurs on EnumDecl, EnumItemList;

aspect production enumDecl
top::EnumDecl ::= name::MaybeName  dcls::EnumItemList
{
  top.showTransform = dcls.showTransform;
}

aspect production consEnumItem
top::EnumItemList ::= h::EnumItem  t::EnumItemList
{
  top.showTransform =
    ableC_Expr {
      _enum_val == $name{h.name}?
        $Expr{strExpr(mkStringConst(h.name, builtin), location=builtin)} :
        $Expr{t.showTransform}
    };
}

aspect production nilEnumItem
top::EnumItemList ::=
{
  top.showTransform =
    ableC_Expr {
      "<" +
      ($stringLiteralExpr{showType(top.containingEnum)} +
       (" " +
        (show_int((unsigned)_enum_val) +
         ">")))
    };
}

abstract production showPointer
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local subType::Type =
    case e.typerep of
    | pointerType(_, t) -> t
    | _ -> errorType()
    end;
  forwards to
    ableC_Expr {
      ({$directTypeExpr{e.typerep} _ptr = $Expr{e};
        $directTypeExpr{subType.withoutTypeQualifiers} _ptr_val;
        _Bool _illegal = 0;
        
        // Hacky way of testing if a pointer can be dereferenced validly
        // TODO: This isn't remotely thread safe, but I don't know of a better way
        _set_segv_handler();
        if (!setjmp(_jump)) {
          _ptr_val = *_ptr;
        } else {
          _illegal = 1;
        }
        _clear_segv_handler();
        
        !_illegal?
          "&" + $Expr{
            -- Preserve locations for error checking
            showExpr(
              declRefExpr(name("_ptr_val", location=builtin), location=e.location),
              location=top.location)} :
          ({char *_baseTypeName = $stringLiteralExpr{showType(e.typerep)};
            char *_text = GC_malloc(strlen(_baseTypeName) + 17);
            sprintf(_text, "<%s at 0x%lx>", _baseTypeName, (unsigned long)_ptr);
            ($directTypeExpr{extType(nilQualifier(), stringType())}){strlen(_text), _text};});})
    };
}

abstract production showStruct
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local decl::Decorated StructDecl =
    case lookupRefId(e.typerep.maybeRefId.fromJust, top.env) of
    | structRefIdItem(decl) :: _ -> decl
    end;
  
  forwards to
    injectGlobalDeclsExpr(
      foldDecl([maybeValueDecl(decl.showFnName, decls(decl.showFnDecls))]),
      ableC_Expr { $name{decl.showFnName}($Expr{e}) },
      location=builtin);
}

abstract production showUnion
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local decl::Decorated UnionDecl =
    case lookupRefId(e.typerep.maybeRefId.fromJust, top.env) of
    | unionRefIdItem(decl) :: _ -> decl
    end;
  
  forwards to
    injectGlobalDeclsExpr(
      foldDecl([maybeValueDecl(decl.showFnName, decls(decl.showFnDecls))]),
      ableC_Expr { $name{decl.showFnName}($Expr{e}) },
      location=builtin);
}

synthesized attribute showDeclErrors::([Message] ::= Location Decorated Env) occurs on StructDecl, UnionDecl;
synthesized attribute showFnName::String occurs on StructDecl, UnionDecl;
synthesized attribute showFnDecls::Decls occurs on StructDecl, UnionDecl;
attribute showErrors occurs on StructDecl, UnionDecl, StructItemList, StructItem, StructDeclarators, StructDeclarator;
attribute showTransform occurs on StructDecl, UnionDecl;
synthesized attribute showTransforms::[Expr] occurs on StructItemList, StructItem, StructDeclarators, StructDeclarator;

global foldShowTransform::(Expr ::= [Expr]) =
  \ es::[Expr] ->
    if null(es)
    then ableC_Expr { "" }
    else foldr1(\ e1::Expr e2::Expr -> ableC_Expr { $Expr{e1} + ", " + $Expr{e2} }, es);

aspect production structDecl
top::StructDecl ::= attrs::Attributes  name::MaybeName  dcls::StructItemList
{
  local n::String = name.maybename.fromJust.name;
  top.showDeclErrors =
    \ l::Location env::Decorated Env ->
      if !name.maybename.isJust
      then [err(l, "Cannot show anonymous struct")]
      else if null(lookupValue(top.showFnName, env))
      then
        case top.showErrors(top.location, addEnv([valueDef(top.showFnName, errorValueItem())], env)) of
        | [] -> []
        | m -> [nested(l, s"In showing struct ${n}", m)]
        end
      else [];
  top.showFnName = s"_show_${n}";
  top.showFnDecls =
    ableC_Decls {
      static $BaseTypeExpr{stringTypeExpr(nilQualifier(), builtin)} $name{top.showFnName}(struct $name{n});
      static $BaseTypeExpr{stringTypeExpr(nilQualifier(), builtin)} $name{top.showFnName}(struct $name{n} s) {
        return $Expr{top.showTransform};
      }
    };
  top.showErrors = dcls.showErrors;
  top.showTransform = ableC_Expr { "{" + $Expr{foldShowTransform(dcls.showTransforms)} + "}" };
}

aspect production unionDecl
top::UnionDecl ::= attrs::Attributes  name::MaybeName  dcls::StructItemList
{
  local n::String = name.maybename.fromJust.name;
  top.showDeclErrors =
    \ l::Location env::Decorated Env ->
      if !name.maybename.isJust
      then [err(l, "Cannot show anonymous union")]
      else if null(lookupValue(top.showFnName, env))
      then
        case top.showErrors(top.location, addEnv([valueDef(top.showFnName, errorValueItem())], env)) of
        | [] -> []
        | m -> [nested(l, s"In showing union ${n}", m)]
        end
      else [];
  top.showFnName = s"_show_${n}";
  top.showFnDecls =
    ableC_Decls {
      static $BaseTypeExpr{stringTypeExpr(nilQualifier(), builtin)} $name{top.showFnName}(union $name{n});
      static $BaseTypeExpr{stringTypeExpr(nilQualifier(), builtin)} $name{top.showFnName}(union $name{n} s) {
        return $Expr{top.showTransform};
      }
    };
  top.showErrors = dcls.showErrors;
  top.showTransform = ableC_Expr { "{" + $Expr{foldShowTransform(dcls.showTransforms)} + "}" };
}

aspect production consStructItem
top::StructItemList ::= h::StructItem  t::StructItemList
{
  top.showErrors =
    \ l::Location env::Decorated Env -> h.showErrors(l, env) ++ t.showErrors(l, env);
  top.showTransforms = h.showTransforms ++ t.showTransforms;
}
aspect production nilStructItem
top::StructItemList ::=
{
  top.showErrors = \ l::Location env::Decorated Env -> [];
  top.showTransforms = [];
}

aspect production structItem
top::StructItem ::= attrs::Attributes  ty::BaseTypeExpr  dcls::StructDeclarators
{
  top.showErrors = dcls.showErrors;
  top.showTransforms = dcls.showTransforms;
}
aspect production structItems
top::StructItem ::= dcls::StructItemList
{
  top.showErrors = dcls.showErrors;
  top.showTransforms = dcls.showTransforms;
}
aspect production anonStructStructItem
top::StructItem ::= d::StructDecl
{
  top.showErrors = d.showErrors;
  top.showTransforms = [d.showTransform];
}
aspect production anonUnionStructItem
top::StructItem ::= d::UnionDecl
{
  top.showErrors = d.showErrors;
  top.showTransforms = [d.showTransform];
}
aspect production warnStructItem
top::StructItem ::= msg::[Message]
{
  top.showErrors = \ l::Location env::Decorated Env -> [];
  top.showTransforms = [];
}

aspect production consStructDeclarator
top::StructDeclarators ::= h::StructDeclarator  t::StructDeclarators
{
  top.showErrors =
    \ l::Location env::Decorated Env -> h.showErrors(l, env) ++ t.showErrors(l, env);
  top.showTransforms = h.showTransforms ++ t.showTransforms;
}
aspect production nilStructDeclarator
top::StructDeclarators ::=
{
  top.showErrors = \ l::Location env::Decorated Env -> [];
  top.showTransforms = [];
}

aspect production structField
top::StructDeclarator ::= name::Name  ty::TypeModifierExpr  attrs::Attributes
{
  top.showErrors =
    \ Location env::Decorated Env -> top.typerep.showErrors(top.sourceLocation, env);
  top.showTransforms =
    [ableC_Expr {
       $stringLiteralExpr{"." ++ name.name ++ " = "} +
         $Expr{
           showExpr(
             parenExpr(ableC_Expr { s.$Name{name} }, location=name.location),
             location=name.location)}
     }];
}
aspect production structBitfield
top::StructDeclarator ::= name::MaybeName  ty::TypeModifierExpr  e::Expr  attrs::Attributes
{
  top.showErrors =
    \ Location env::Decorated Env -> top.typerep.showErrors(top.sourceLocation, env);
  top.showTransforms =
    case name of
    | justName(n) ->
     [ableC_Expr {
         $stringLiteralExpr{"." ++ n.name ++ " = "} +
           $Expr{
             showExpr(
               parenExpr(ableC_Expr { s.$Name{n} }, location=n.location),
               location=n.location)}
       }]
    | nothingName() -> []
    end;
}
aspect production warnStructField
top::StructDeclarator ::= msg::[Message]
{
  top.showErrors = \ l::Location env::Decorated Env -> [];
  top.showTransforms = [];
}

abstract production strExpr
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"str(${e.pp})";
  
  local type::Type = e.typerep.defaultFunctionArrayLvalueConversion;
  local localErrors::[Message] = e.errors ++ type.strErrors(e.location, e.env);
  local fwrd::Expr = type.strProd(decExpr(e, location=builtin));
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production strCharPointer
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"str(${e.pp})";
  
  forwards to
    ableC_Expr {
      // Cast in case argument is const char *
      str_char_pointer((char *)$Expr{e})
    };
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

abstract production concatString
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp} + ${e2.pp}";
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    e1.typerep.strErrors(e1.location, e1.env) ++
    e2.typerep.strErrors(e2.location, e2.env) ++
    checkStringHeaderDef("concat_string", top.location, top.env);
  
  e2.env = addEnv(e1.defs, e1.env);
  
  local fwrd::Expr =
    directCallExpr(
      name("concat_string", location=builtin),
      consExpr(
        strExpr(decExpr(e1, location=builtin), location=builtin),
        consExpr(
          strExpr(decExpr(e2, location=builtin), location=builtin),
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
    e1.errors ++ e2.errors ++
    e1.typerep.strErrors(e1.location, e1.env) ++
    e2.typerep.strErrors(e2.location, e2.env) ++
    checkStringHeaderDef("remove_string", top.location, top.env);
  
  e2.env = addEnv(e1.defs, e1.env);
  
  local fwrd::Expr =
    directCallExpr(
      name("remove_string", location=builtin),
      consExpr(
        strExpr(decExpr(e1, location=builtin), location=builtin),
        consExpr(
          strExpr(decExpr(e2, location=builtin), location=builtin),
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
    e1.errors ++ e2.errors ++
    checkStringHeaderDef("repeat_string", top.location, top.env) ++
    checkStringType(e1.typerep, "*", top.location) ++
    if e2.typerep.isIntegerType
    then []
    else [err(e2.location, s"string repeat must have integer type, but got ${showType(e2.typerep)}")];
  
  e2.env = addEnv(e1.defs, e1.env);
  
  local fwrd::Expr =
    directCallExpr(
      name("repeat_string", location=builtin),
      consExpr(
        decExpr(e1, location=builtin),
        consExpr(
          decExpr(e2, location=builtin),
          nilExpr())),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production equalsString
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp} == ${e2.pp}";
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    e1.typerep.strErrors(e1.location, e1.env) ++
    e2.typerep.strErrors(e2.location, e2.env) ++
    checkStringHeaderDef("equals_string", top.location, top.env);
  
  e2.env = addEnv(e1.defs, e1.env);
  
  local fwrd::Expr =
    directCallExpr(
      name("equals_string", location=builtin),
      consExpr(
        strExpr(decExpr(e1, location=builtin), location=builtin),
        consExpr(
          strExpr(decExpr(e2, location=builtin), location=builtin),
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
    e1.errors ++ e2.errors ++
    checkStringHeaderDef("subscript_string", top.location, top.env) ++
    checkStringType(e1.typerep, "[]", top.location) ++
    if e2.typerep.isIntegerType
    then []
    else [err(e2.location, s"string index must have integer type, but got ${showType(e2.typerep)}")];
  
  e2.env = addEnv(e1.defs, e1.env);
  
  local fwrd::Expr =
    directCallExpr(
      name("subscript_string", location=builtin),
      consExpr(
        strExpr(decExpr(e1, location=builtin), location=builtin),
        consExpr(
          decExpr(e2, location=builtin),
          nilExpr())),
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
    ableC_Expr {
      ((const struct _string_s)$Expr{decExpr(lhs, location=builtin)}).$Name{rhs}
    };
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production substringString
top::Expr ::= e1::Expr a::Exprs
{
  propagate substituted;
  top.pp = pp"${e1.pp}.substring(${ppImplode(pp", ", a.pps)}";
  
  a.env = addEnv(e1.defs, e1.env);
  a.expectedTypes = -- size_t
    [builtinType(nilQualifier(), unsignedType(longType())),
     builtinType(nilQualifier(), unsignedType(longType()))];
  a.argumentPosition = 1;
  a.callExpr = top; -- Doesn't really matter, just needs location
  a.callVariadic = false;
  local localErrors::[Message] =
    e1.errors ++ a.errors ++
    checkStringHeaderDef("substring", top.location, top.env) ++
    checkStringType(e1.typerep, "substring", top.location) ++
    a.argumentErrors;
  local fwrd::Expr =
    directCallExpr(
      name("substring", location=builtin),
      consExpr(decExpr(e1, location=builtin), a),
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
