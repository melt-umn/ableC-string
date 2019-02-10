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
  
  local localErrors::[Message] = e.errors;
  local fwrd::Expr =
    case e.typerep.defaultFunctionArrayLvalueConversion.showProd of
      just(p) -> p(decExpr(e, location=e.location), top.location)
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
    checkStringHeaderDef("show_string", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("show_string", location=builtin),
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
    checkStringHeaderDef("show_char_pointer", top.location, top.env);
  local fwrd::Expr =
    ableC_Expr {
      // Cast in case argument is const char *
      show_char_pointer((char *)$Expr{e})
    };
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production showChar
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local localErrors::[Message] =
    checkStringHeaderDef("show_char", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("show_char", location=builtin),
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
    checkStringHeaderDef("show_int", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("show_int", location=builtin),
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
    checkStringHeaderDef("show_float", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("show_float", location=builtin),
      consExpr(e, nilExpr()),
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

synthesized attribute showTransform::Expr;

abstract production showEnum
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local decl::Decorated EnumDecl =
    case e.typerep of
    | extType(_, enumExtType(decl)) -> decl
    end;
  
  local localErrors::[Message] =
    checkStringHeaderDef("str_char_pointer", top.location, top.env) ++
    case e.typerep of
    | extType(_, enumExtType(_)) -> []
    | _ -> [err(e.location, s"Expected an enum type (got ${showType(e.typerep)})")]
    end;
  local fwrd::Expr =
    ableC_Expr {
      ({$directTypeExpr{e.typerep} _enum_val = $Expr{e};
        $Expr{decl.showTransform};})
    };
  forwards to mkErrorCheck(localErrors, fwrd);
}

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
        ($Expr{strExpr(ableC_Expr {(unsigned)_enum_val}, location=builtin)} +
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
  local localErrors::[Message] =
    e.errors ++
    -- TODO: Hack for computing sub-type show errors
    decorate
      showExpr(
        dereferenceExpr(decExpr(e, location=builtin), location=e.location),
        location=top.location)
    with {
      env = top.env;
      returnType = top.returnType;
    }.errors ++
    checkStringHeaderDef("_handle_segv", top.location, top.env);
  local fwrd::Expr =
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
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production showStructUnion
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local structLookup::[RefIdItem] =
    case e.typerep.maybeRefId of
    | just(rid) -> lookupRefId(rid, top.env)
    | nothing() -> []
    end;
  
  local items::Decorated StructItemList =
    case structLookup of
    | structRefIdItem(structDecl(_, _, items)) :: _ -> items
    | unionRefIdItem(unionDecl(_, _, items)) :: _ -> items
    end;
  
  local showTransform::Expr =
    case structLookup of
    | structRefIdItem(d) :: _ -> d.showTransform
    | unionRefIdItem(d) :: _ -> d.showTransform
    end;
  local showFnName::String = s"_show_${e.typerep.mangledName}";
  local showFnDecls::Decls =
    ableC_Decls {
      $BaseTypeExpr{stringTypeExpr(nilQualifier(), builtin)} $name{showFnName}(
          $directTypeExpr{e.typerep});
      $BaseTypeExpr{stringTypeExpr(nilQualifier(), builtin)} $name{showFnName}(
          $directTypeExpr{e.typerep} s) {
        return $Expr{showTransform};
      }
    };
  local decl::Decl = showDecl(showFnName, showFnDecls);
  decl.env = globalEnv(top.env);
  decl.returnType = nothing();
  decl.isTopLevel = false;
  
  local headerCheck::[Message] = checkStringHeaderDef("concat_string", top.location, top.env);
  local localErrors::[Message] =
    if !null(headerCheck)
    then headerCheck
    else case e.typerep, structLookup of
    | errorType(), _ -> []
    | extType(_, refIdExtType(structSEU(), "<anon>", _)), _ ->
      [err(top.location, s"Can't show anonymous struct")]
    | extType(_, refIdExtType(unionSEU(), "<anon>", _)), _ ->
      [err(top.location, s"Can't show anonymous union")]
    | extType(_, refIdExtType(structSEU(), id, _)), [] ->
      [err(top.location, s"struct ${id} does not have a definition.")]
    | extType(_, refIdExtType(unionSEU(), id, _)), [] ->
      [err(top.location, s"union ${id} does not have a definition.")]
    | extType(_, refIdExtType(structSEU(), id, _)), _ ->
      if !null(decl.errors)
      then [nested(e.location, s"In showing struct ${id}", decl.errors)]
      else []
    | extType(_, refIdExtType(unionSEU(), id, _)), _ ->
      if !null(decl.errors)
      then [nested(e.location, s"In showing union ${id}", decl.errors)]
      else []
    | _, _ -> [err(e.location, s"Expected a struct/union type (got ${showType(e.typerep)})")]
    end;
  
  local fwrd::Expr =
    injectGlobalDeclsExpr(
      foldDecl([decDecl(decl)]),
      ableC_Expr { $name{showFnName}($Expr{e}) },
      location=builtin);
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production showDecl
top::Decl ::= showFnName::String showFnDecls::Decls
{
  propagate substituted;
  top.pp = pp"showDecl {${nestlines(2, terminate(line(), showFnDecls.pps))}}";
  forwards to
    if !null(lookupValue(showFnName, top.env))
    then decls(nilDecl())
    else decls(showFnDecls);
}

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
  top.showTransform = ableC_Expr { "{" + $Expr{foldShowTransform(dcls.showTransforms)} + "}" };
}

aspect production unionDecl
top::UnionDecl ::= attrs::Attributes  name::MaybeName  dcls::StructItemList
{
  top.showTransform = ableC_Expr { "{" + $Expr{foldShowTransform(dcls.showTransforms)} + "}" };
}

aspect production consStructItem
top::StructItemList ::= h::StructItem  t::StructItemList
{
  top.showTransforms = h.showTransforms ++ t.showTransforms;
}
aspect production nilStructItem
top::StructItemList ::=
{
  top.showTransforms = [];
}

aspect production structItem
top::StructItem ::= attrs::Attributes  ty::BaseTypeExpr  dcls::StructDeclarators
{
  top.showTransforms = dcls.showTransforms;
}
aspect production structItems
top::StructItem ::= dcls::StructItemList
{
  top.showTransforms = dcls.showTransforms;
}
aspect production anonStructStructItem
top::StructItem ::= d::StructDecl
{
  top.showTransforms = [d.showTransform];
}
aspect production anonUnionStructItem
top::StructItem ::= d::UnionDecl
{
  top.showTransforms = [d.showTransform];
}
aspect production warnStructItem
top::StructItem ::= msg::[Message]
{
  top.showTransforms = [];
}

aspect production consStructDeclarator
top::StructDeclarators ::= h::StructDeclarator  t::StructDeclarators
{
  top.showTransforms = h.showTransforms ++ t.showTransforms;
}
aspect production nilStructDeclarator
top::StructDeclarators ::=
{
  top.showTransforms = [];
}

aspect production structField
top::StructDeclarator ::= name::Name  ty::TypeModifierExpr  attrs::Attributes
{
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
  top.showTransforms = [];
}

abstract production strExpr
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"str(${e.pp})";
  
  local localErrors::[Message] = e.errors;
  local fwrd::Expr =
    case e.typerep.defaultFunctionArrayLvalueConversion.strProd of
      just(p) -> p(decExpr(e, location=e.location), top.location)
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
    checkStringHeaderDef("str_char_pointer", top.location, top.env);
  local fwrd::Expr =
    ableC_Expr {
      // Cast in case argument is const char *
      str_char_pointer((char *)$Expr{e})
    };
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production strChar
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"str(${e.pp})";
  
  local localErrors::[Message] =
    checkStringHeaderDef("str_char", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("str_char", location=builtin),
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
    checkStringHeaderDef("str_pointer", top.location, top.env);
  local fwrd::Expr =
    directCallExpr(
      name("str_pointer", location=builtin),
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

abstract production concatString
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp} + ${e2.pp}";
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
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
        strExpr(decExpr(e1, location=builtin), location=builtin),
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
