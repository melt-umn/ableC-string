grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

imports silver:core hiding equalsString;

imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;
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
         singleArgExtCallExpr(showExpr, _, _))),
     valueDef(
       "str",
       builtinFunctionValueItem(
         functionType(extType(nilQualifier(), stringType()), noProtoFunctionType(), nilQualifier()),
         singleArgExtCallExpr(strExpr, _, _)))];
}

abstract production singleArgExtCallExpr
top::Expr ::= handler::(Expr ::= Expr) f::Name a::Exprs
{
  top.pp = pp"${f.pp}(${ppImplode(pp", ", a.pps)})";
  forwards to
    case a of
    | consExpr(e, nilExpr()) -> handler(e)
    | _ -> errorExpr([errFromOrigin(top, s"${f.name} expected exactly 1 argument, got ${toString(a.count)}")])
    end;
}

abstract production showExpr
top::Expr ::= e::Expr
{
  top.pp = pp"show(${e.pp})";
  attachNote extensionGenerated("ableC-string");
  propagate env, controlStmtContext;
  
  local type::Type = e.typerep.defaultFunctionArrayLvalueConversion;
  local localErrors::[Message] = e.errors ++ showErrors(e, type);
  local fwrd::Expr =
    case getCustomShow(type, top.env) of
    | just(func) -> ableC_Expr{ $Name{func}($Expr{decExpr(e)}) }
    | nothing() -> type.showProd(e) -- Unavoidable re-decoration here, since we don't know what env showProd will provide to e
    end;
  forwards to mkErrorCheck(localErrors, fwrd);
}

function showErrors
[Message] ::= e::Decorated Expr with {env}  type::Type
{
  return case getCustomShow(type, e.env) of
  | just(_) -> []
  | nothing() -> type.showErrors(e)
  end;
}

abstract production showCharPointer
top::Expr ::= e::Expr
{
  top.pp = pp"show(${e.pp})";
  attachNote extensionGenerated("ableC-string");
  
  forwards to
    ableC_Expr {
      // Cast in case argument is const char *
      show_char_pointer((char *)$Expr{e})
    };
}

synthesized attribute showTransform::Expr;
synthesized attribute strTransform::Expr;

attribute showTransform occurs on EnumDecl, EnumItemList;
attribute strTransform occurs on EnumDecl, EnumItemList;

aspect production enumDecl
top::EnumDecl ::= name::MaybeName  dcls::EnumItemList
{
  top.showTransform = dcls.showTransform;
  top.strTransform = dcls.strTransform;
}

aspect production consEnumItem
top::EnumItemList ::= h::EnumItem  t::EnumItemList
{
  attachNote extensionGenerated("ableC-string");

  top.showTransform =
    ableC_Expr {
      _enum_val == $name{h.name}?
        $Expr{strExpr(mkStringConst(h.name))} :
        $Expr{t.showTransform}
    };
  top.strTransform =
    ableC_Expr {
      _enum_val == $name{h.name}?
        $Expr{strExpr(mkStringConst(h.name))} :
        $Expr{t.strTransform}
    };
}

aspect production nilEnumItem
top::EnumItemList ::=
{
  attachNote extensionGenerated("ableC-string");

  top.showTransform =
    ableC_Expr {
      "<" +
      ($stringLiteralExpr{showType(top.containingEnum)} +
       (" " +
        (show_int((unsigned)_enum_val) +
         ">")))
    };
  top.strTransform =
    ableC_Expr {
      show_int((unsigned)_enum_val)
    };
}

abstract production showPointer
top::Expr ::= e::Expr
{
  top.pp = pp"show(${e.pp})";
  attachNote extensionGenerated("ableC-string");
  propagate env, controlStmtContext;
  
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
        if(_ptr) {
          _set_handler();
          if (!setjmp(_jump)) {
            _ptr_val = *_ptr;
          } else {
            _illegal = 1;
          }
          _clear_handler();
        } else {
          _illegal = 1;
        }
        
        !_illegal?
          "&" + $Expr{
            -- Preserve locations for error checking
            showExpr(
              declRefExpr(name("_ptr_val")))} :
          ({char *_baseTypeName = $stringLiteralExpr{showType(e.typerep)};
            char *_text = GC_malloc(strlen(_baseTypeName) + 17);
            sprintf(_text, "<%s at 0x%lx>", _baseTypeName, (unsigned long)_ptr);
            ($directTypeExpr{extType(nilQualifier(), stringType())})(struct _string_s){strlen(_text), _text};});})
    };
}

abstract production showOpaquePointer
top::Expr ::= e::Expr
{
  top.pp = pp"show(${e.pp})";
  attachNote extensionGenerated("ableC-string");
  propagate env, controlStmtContext;
  
  local subType::Type =
    case e.typerep of
    | pointerType(_, t) -> t
    | _ -> errorType()
    end;
  forwards to
    ableC_Expr {
      ({char *_baseTypeName = $stringLiteralExpr{showType(e.typerep)};
        char *_text = GC_malloc(strlen(_baseTypeName) + 17);
        sprintf(_text, "<%s at 0x%lx>", _baseTypeName, (unsigned long)$Expr{e});
        ($directTypeExpr{extType(nilQualifier(), stringType())})(struct _string_s){strlen(_text), _text};})
    };
}

abstract production showStruct
top::Expr ::= e::Expr
{
  top.pp = pp"show(${e.pp})";
  attachNote extensionGenerated("ableC-string");
  propagate env, controlStmtContext;
  
  local decl::Decorated StructDecl =
    case lookupRefId(e.typerep.maybeRefId.fromJust, top.env) of
    | structRefIdItem(decl) :: _ -> decl
    | _ -> error("struct refId not found")
    end;
  
  forwards to
    injectGlobalDeclsExpr(
      foldDecl([maybeValueDecl(decl.showFnName, decls(decl.showFnDecls))]),
      ableC_Expr { $name{decl.showFnName}($Expr{e}) });
}

abstract production showUnion
top::Expr ::= e::Expr
{
  top.pp = pp"show(${e.pp})";
  attachNote extensionGenerated("ableC-string");
  propagate env, controlStmtContext;
  
  local decl::Decorated UnionDecl =
    case lookupRefId(e.typerep.maybeRefId.fromJust, top.env) of
    | unionRefIdItem(decl) :: _ -> decl
    | _ -> error("union refId not found")
    end;
  
  forwards to
    injectGlobalDeclsExpr(
      foldDecl([maybeValueDecl(decl.showFnName, decls(decl.showFnDecls))]),
      ableC_Expr { $name{decl.showFnName}($Expr{e}) });
}

synthesized attribute showDeclErrors::([Message] ::= Decorated Expr with {env}) occurs on StructDecl, UnionDecl;
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
  attachNote extensionGenerated("ableC-string");
  local n::String = name.maybename.fromJust.name;
  local checkExpr::Expr = errorExpr([]); -- Expr that gets decorated to pass the right origin and env
  top.showDeclErrors =
    \ e::Decorated Expr with {env} ->
      if !name.maybename.isJust
      then [errFromOrigin(e, "Cannot show anonymous struct")]
      else if null(lookupValue(top.showFnName, e.env))
      then
        case top.showErrors(decorate checkExpr with {env = addEnv([valueDef(top.showFnName, errorValueItem())], e.env);}) of
        | [] -> []
        | m -> [nested(getParsedOriginLocationOrFallback(e), s"In showing struct ${n}", m)]
        end
      else [];
  top.showFnName = s"_show_${n}";
  top.showFnDecls =
    ableC_Decls {
      static $BaseTypeExpr{stringTypeExpr(nilQualifier())} $name{top.showFnName}(struct $name{n});
      static $BaseTypeExpr{stringTypeExpr(nilQualifier())} $name{top.showFnName}(struct $name{n} s) {
        return $Expr{top.showTransform};
      }
    };
  top.showErrors = dcls.showErrors;
  top.showTransform = ableC_Expr { "{" + $Expr{foldShowTransform(dcls.showTransforms)} + "}" };
}

aspect production unionDecl
top::UnionDecl ::= attrs::Attributes  name::MaybeName  dcls::StructItemList
{
  attachNote extensionGenerated("ableC-string");
  local n::String = name.maybename.fromJust.name;
  local checkExpr::Expr = errorExpr([]); -- Expr that gets decorated to pass the right origin and env
  top.showDeclErrors =
    \ e::Decorated Expr with {env} ->
      if !name.maybename.isJust
      then [errFromOrigin(e, "Cannot show anonymous union")]
      else if null(lookupValue(top.showFnName, e.env))
      then
        case top.showErrors(decorate checkExpr with {env = addEnv([valueDef(top.showFnName, errorValueItem())], e.env);}) of
        | [] -> []
        | m -> [nested(getParsedOriginLocationOrFallback(e), s"In showing union ${n}", m)]
        end
      else [];
  top.showFnName = s"_show_${n}";
  top.showFnDecls =
    ableC_Decls {
      static $BaseTypeExpr{stringTypeExpr(nilQualifier())} $name{top.showFnName}(union $name{n});
      static $BaseTypeExpr{stringTypeExpr(nilQualifier())} $name{top.showFnName}(union $name{n} s) {
        return $Expr{top.showTransform};
      }
    };
  top.showErrors = dcls.showErrors;
  top.showTransform = ableC_Expr { "{" + $Expr{foldShowTransform(dcls.showTransforms)} + "}" };
}

aspect production consStructItem
top::StructItemList ::= h::StructItem  t::StructItemList
{
  top.showErrors = \ e::Decorated Expr with {env} -> h.showErrors(e) ++ t.showErrors(e);
  top.showTransforms = h.showTransforms ++ t.showTransforms;
}
aspect production nilStructItem
top::StructItemList ::=
{
  top.showErrors = \ Decorated Expr with {env} -> [];
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
  top.showErrors = \ Decorated Expr with {env} -> [];
  top.showTransforms = [];
}

aspect production consStructDeclarator
top::StructDeclarators ::= h::StructDeclarator  t::StructDeclarators
{
  top.showErrors = \ e::Decorated Expr with {env} -> h.showErrors(e) ++ t.showErrors(e);
  top.showTransforms = h.showTransforms ++ t.showTransforms;
}
aspect production nilStructDeclarator
top::StructDeclarators ::=
{
  top.showErrors = \ Decorated Expr with {env} -> [];
  top.showTransforms = [];
}

aspect production structField
top::StructDeclarator ::= name::Name  ty::TypeModifierExpr  attrs::Attributes
{
  attachNote extensionGenerated("ableC-string");
  local checkExpr::Expr = errorExpr([]);
  top.showErrors =
    \ e::Decorated Expr with {env} -> showErrors(decorate checkExpr with {env = e.env;}, top.typerep);
  top.showTransforms =
    [ableC_Expr {
       $stringLiteralExpr{"." ++ name.name ++ " = "} +
         $Expr{
           showExpr(
             parenExpr(ableC_Expr { s.$Name{name} }))}
     }];
}
aspect production structBitfield
top::StructDeclarator ::= name::MaybeName  ty::TypeModifierExpr  e::Expr  attrs::Attributes
{
  attachNote extensionGenerated("ableC-string");
  local checkExpr::Expr = errorExpr([]);
  top.showErrors =
    \ e::Decorated Expr with {env} -> showErrors(decorate checkExpr with {env = e.env;}, top.typerep);
  top.showTransforms =
    case name of
    | justName(n) ->
     [ableC_Expr {
         $stringLiteralExpr{"." ++ n.name ++ " = "} +
           $Expr{
             showExpr(
               parenExpr(ableC_Expr { s.$Name{n} }))}
       }]
    | nothingName() -> []
    end;
}
aspect production warnStructField
top::StructDeclarator ::= msg::[Message]
{
  top.showErrors = \ Decorated Expr with {env} -> [];
  top.showTransforms = [];
}

abstract production strExpr
top::Expr ::= e::Expr
{
  top.pp = pp"str(${e.pp})";
  propagate env, controlStmtContext;
  
  local type::Type = e.typerep.defaultFunctionArrayLvalueConversion;
  local localErrors::[Message] = e.errors ++ type.strErrors(e);
  local fwrd::Expr = type.strProd(e); -- Unavoidable re-decoration here, since we don't know what env strProd will provide to e
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production strCharPointer
top::Expr ::= e::Expr
{
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
  top.pp = pp"${lhs.pp} = ${rhs.pp}";
  
  forwards to
    eqExpr(
      lhs,
      strExpr(rhs));
}

abstract production concatString
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"${e1.pp} + ${e2.pp}";
  attachNote extensionGenerated("ableC-string");
  propagate controlStmtContext;
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    e1.typerep.defaultFunctionArrayLvalueConversion.strErrors(e1) ++
    e2.typerep.defaultFunctionArrayLvalueConversion.strErrors(e2) ++
    checkStringHeaderDef("concat_string", top.env);
  
  e1.env = top.env;
  e2.env = addEnv(e1.defs, e1.env);
  
  local fwrd::Expr =
    directCallExpr(
      name("concat_string"),
      consExpr(
        strExpr(decExpr(e1)),
        consExpr(
          strExpr(decExpr(e2)),
          nilExpr())));
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production removeString
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"${e1.pp} - ${e2.pp}";
  attachNote extensionGenerated("ableC-string");
  propagate controlStmtContext;
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    e1.typerep.defaultFunctionArrayLvalueConversion.strErrors(e1) ++
    e2.typerep.defaultFunctionArrayLvalueConversion.strErrors(e2) ++
    checkStringHeaderDef("remove_string", top.env);
  
  e1.env = top.env;
  e2.env = addEnv(e1.defs, e1.env);
  
  local fwrd::Expr =
    directCallExpr(
      name("remove_string"),
      consExpr(
        strExpr(decExpr(e1)),
        consExpr(
          strExpr(decExpr(e2)),
          nilExpr())));
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production repeatString
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"${e1.pp} * ${e2.pp}";
  attachNote extensionGenerated("ableC-string");
  propagate controlStmtContext;
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    checkStringHeaderDef("repeat_string", top.env) ++
    checkStringType(e1.typerep, "*") ++
    if e2.typerep.isIntegerType
    then []
    else [errFromOrigin(e2, s"string repeat must have integer type, but got ${showType(e2.typerep)}")];
  
  e1.env = top.env;
  e2.env = addEnv(e1.defs, e1.env);
  
  local fwrd::Expr =
    directCallExpr(
      name("repeat_string"),
      consExpr(
        decExpr(e1),
        consExpr(
          decExpr(e2),
          nilExpr())));
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production equalsString
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"${e1.pp} == ${e2.pp}";
  attachNote extensionGenerated("ableC-string");
  propagate controlStmtContext;
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    e1.typerep.defaultFunctionArrayLvalueConversion.strErrors(e1) ++
    e2.typerep.defaultFunctionArrayLvalueConversion.strErrors(e2) ++
    checkStringHeaderDef("equals_string", top.env);
  
  e1.env = top.env;
  e2.env = addEnv(e1.defs, e1.env);
  
  local fwrd::Expr =
    directCallExpr(
      name("equals_string"),
      consExpr(
        strExpr(decExpr(e1)),
        consExpr(
          strExpr(decExpr(e2)),
          nilExpr())));
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production subscriptString
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"${e1.pp}[${e2.pp}]";
  attachNote extensionGenerated("ableC-string");
  propagate controlStmtContext;
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    checkStringHeaderDef("subscript_string", top.env) ++
    checkStringType(e1.typerep, "[]") ++
    if e2.typerep.isIntegerType
    then []
    else [errFromOrigin(e2, s"string index must have integer type, but got ${showType(e2.typerep)}")];
  
  e1.env = top.env;
  e2.env = addEnv(e1.defs, e1.env);
  
  local fwrd::Expr =
    directCallExpr(
      name("subscript_string"),
      consExpr(
        strExpr(decExpr(e1)),
        consExpr(
          decExpr(e2),
          nilExpr())));
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production callMemberString
top::Expr ::= lhs::Expr deref::Boolean rhs::Name a::Exprs
{
  
  forwards to
    case rhs.name of
      "substring" -> substringString(lhs, a)
    | n -> errorExpr([errFromOrigin(rhs, s"string does not have field ${n}")])
    end;
}

abstract production memberString
top::Expr ::= lhs::Expr deref::Boolean rhs::Name
{
  top.pp = parens(ppConcat([lhs.pp, text(if deref then "->" else "."), rhs.pp]));
  attachNote extensionGenerated("ableC-string");
  propagate env, controlStmtContext;

  local localErrors::[Message] =
    (if !null(lookupRefId("edu:umn:cs:melt:exts:ableC:string:string", top.env))
     then []
     else [errFromOrigin(top, "Missing include of string.xh")]) ++
    checkStringType(lhs.typerep, ".") ++
    (if rhs.name == "length" || rhs.name == "text"
     then []
     else [errFromOrigin(rhs, s"string does not have member ${rhs.name}")]);
  local fwrd::Expr =
    ableC_Expr {
      ((const struct _string_s)$Expr{decExpr(lhs)}).$Name{rhs}
    };
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production substringString
top::Expr ::= e1::Expr a::Exprs
{
  top.pp = pp"${e1.pp}.substring(${ppImplode(pp", ", a.pps)}";
  attachNote extensionGenerated("ableC-string");
  propagate controlStmtContext;
  
  e1.env = top.env;
  a.env = addEnv(e1.defs, e1.env);
  a.expectedTypes = -- size_t
    [builtinType(nilQualifier(), unsignedType(longType())),
     builtinType(nilQualifier(), unsignedType(longType()))];
  a.argumentPosition = 1;
  a.callExpr = top; -- Doesn't really matter, just needs location
  a.callVariadic = false;
  local localErrors::[Message] =
    e1.errors ++ a.errors ++
    checkStringHeaderDef("substring", top.env) ++
    checkStringType(e1.typerep, "substring") ++
    a.argumentErrors;
  local fwrd::Expr =
    directCallExpr(
      name("substring"),
      consExpr(decExpr(e1), a));
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production initString
top::Initializer ::= e::Expr
{
  forwards to exprInitializer(strExpr(e));
}

-- Check the given env for the given function name
function checkStringHeaderDef
[Message] ::= n::String env::Decorated Env
{
  return
    if !null(lookupValue(n, env))
    then []
    else [errFromOrigin(ambientOrigin(), "Missing include of string.xh")];
}

-- Check that operand has string type
function checkStringType
[Message] ::= t::Type op::String
{
  return
    if typeAssignableTo(extType(nilQualifier(), stringType()), t)
    then []
    else [errFromOrigin(ambientOrigin(), s"Operand to ${op} expected string type (got ${showType(t)})")];
}
