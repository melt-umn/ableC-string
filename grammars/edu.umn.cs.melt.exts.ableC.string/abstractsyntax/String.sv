grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

imports silver:core hiding equalsString;

imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;
imports edu:umn:cs:melt:ableC:abstractsyntax:builtins;
--imports edu:umn:cs:melt:ableC:abstractsyntax:debug;

imports edu:umn:cs:melt:exts:ableC:allocation:abstractsyntax;

synthesized attribute buildStr::((Stmt, Expr, Stmt) ::= Name Name) occurs on Expr;

function wrapBuildStr
Expr ::= buildStr::((Stmt, Expr, Stmt) ::= Name Name)
{
  nondecorated local bufName::Name = freshName("buf");
  nondecorated local lenName::Name = freshName("len");
  local impls::(Stmt, Expr, Stmt) = buildStr(bufName, lenName);
  
  return ableC_Expr {
    proto_typedef size_t;
    ({$Stmt{impls.1}
      char *$Name{bufName} = allocate($Expr{impls.2} + 1);
      size_t $Name{lenName} = 0;
      $Stmt{impls.3}
      ($directTypeExpr{extType(nilQualifier(), stringType())})(struct _string_s){
        $Name{lenName}, $Name{bufName}
      };})
  };
}

function defaultBuildStr
(Stmt, Expr, Stmt) ::= top::Decorated Expr buf::Name len::Name
{
  local type::Type = top.typerep.defaultFunctionArrayLvalueConversion;
  nondecorated local tmpName::Name = freshName("str");
  nondecorated local tmpRef::Expr = if top.isSimple then ^top else declRefExpr(tmpName);
  return (
    if top.isSimple then nullStmt() else declStmt(autoDecl(tmpName, ^top)),
    type.strMaxLenProd(tmpRef),
    ableC_Stmt { $Name{^len} += $Expr{type.strProd(ableC_Expr { $Name{^buf} + $Name{^len} }, tmpRef)}; });
}

aspect default production
top::Expr ::=
{
  top.buildStr = defaultBuildStr(top, _, _);
}

aspect production stmtExpr
top::Expr ::= s::Stmt e::Expr
{
  top.buildStr = \ buf::Name len::Name ->
    let buildE::(Stmt, Expr, Stmt) = e.buildStr(buf, len)
    in (seqStmt(^s, buildE.1), buildE.2, buildE.3)
    end;
}

aspect function getInitialEnvDefs
[Def] ::=
{
  d <-
    [valueDef(
       "show",
       builtinFunctionValueItem(
         functionType(extType(nilQualifier(), stringType()), noProtoFunctionType(), nilQualifier()),
         singleArgExtCallExpr(showExpr))),
     valueDef(
       "str",
       builtinFunctionValueItem(
         functionType(extType(nilQualifier(), stringType()), noProtoFunctionType(), nilQualifier()),
         singleArgExtCallExpr(strExpr)))];
}

production singleArgExtCallExpr implements ReferenceCall
top::Expr ::= f::Name a::Exprs handler::(Expr ::= Expr)
{
  top.pp = pp"${f.pp}(${ppImplode(pp", ", a.pps)})";
  forwards to bindDirectCallExpr(@f, @a,
    case a.bindRefExprs of
    | [e] -> handler(e)
    | _ -> errorExpr([errFromOrigin(top, s"${f.name} expected exactly 1 argument, got ${toString(a.count)}")])
    end);
}

production strExpr
top::Expr ::= e::Expr
{
  top.pp = pp"str(${e.pp})";
  propagate env, controlStmtContext;
  top.typerep = extType(nilQualifier(), stringType());

  top.buildStr = \ buf::Name len::Name -> (
    nullStmt(), type.strMaxLenProd(^e),
    ableC_Stmt {
      $Name{len} += $Expr{type.strProd(ableC_Expr { $Name{buf} + $Name{len} }, ^e)};
    });

  local type::Type = e.typerep.defaultFunctionArrayLvalueConversion;
  local localErrors::[Message] = e.errors ++ type.strErrors(e.env) ++
    checkStringHeaderDef(top.env) ++
    case top.env.allocContext of
    | unspecifiedAllocContext() :: _ -> [errFromOrigin(top, "An allocator to use must be specfied (e.g. `allocate_using heap;`)")]
    | _ -> []
    end;
  local fwrd::Expr = type.directStrProd(^e);
  forwards to mkErrorCheck(localErrors, @fwrd);
}

production directStrExpr
top::Expr ::= e::Expr strMaxLenProd::(Expr ::= Expr) strProd::(Expr ::= Expr Expr)
{
  attachNote extensionGenerated("ableC-string");
  propagate env, controlStmtContext;
  nondecorated local bufName::Name = freshName("buf");
  forwards to ableC_Expr {
    proto_typedef size_t;
    ({char *$Name{bufName} = allocate($Expr{strMaxLenProd(^e)} + 1);
      ($directTypeExpr{extType(nilQualifier(), stringType())})(struct _string_s){
        $Expr{strProd(directRefExpr(bufName), ^e)}, $Name{bufName}
      };})
  };
}

production strStringMaxLen
top::Expr ::= e::Expr
{
  attachNote extensionGenerated("ableC-string");
  forwards to ableC_Expr { $Expr{@e}.length };
}

production strString
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  forwards to ableC_Expr { sprintf($Expr{@buf}, "%s", $Expr{@e}.text) };
}

production directStrCharPointer
top::Expr ::= e::Expr
{
  top.pp = pp"strCharPointer(${e.pp})";
  attachNote extensionGenerated("ableC-string");

  forward nonConst = directStrExpr(@e, strCharPointerMaxLen, strCharPointer);
  forwards to
    case e of
    | stringLiteral(l) -> ableC_Expr {
        ($directTypeExpr{extType(nilQualifier(), stringType())})(struct _string_s){
          $Expr{mkIntConst(length(unescapeString(l)) - 2)}, $Expr{^e}
        }
      }
    | _ -> @nonConst
    end;
}

production strCharPointerMaxLen
top::Expr ::= e::Expr
{
  attachNote extensionGenerated("ableC-string");
  forwards to ableC_Expr { strlen($Expr{@e}) };
}

production strCharPointer
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  forwards to ableC_Expr { sprintf($Expr{@buf}, "%s", $Expr{@e}) };
}

production strChar
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  forwards to
    ableC_Expr {
      $Expr{@buf}[0] = $Expr{^e},
      $Expr{^buf}[1] = '\0',
      1
    };
}

production strPointer
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  forwards to
    ableC_Expr {
      sprintf($Expr{@buf}, "%p", (void*)$Expr{@e})
    };
}

production directStrBool
top::Expr ::= e::Expr
{
  attachNote extensionGenerated("ableC-string");
  forwards to explicitCastExpr(
    typeName(stringTypeExpr(nilQualifier()), baseTypeExpr()),
    ableC_Expr {
      $Expr{@e}? TRUE_STR : FALSE_STR
    });
}

production strBool
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  forwards to
    ableC_Expr {
      sprintf($Expr{@buf}, "%s", $Expr{@e}? "true" : "false")
    };
}

production strNum
top::Expr ::= buf::Expr e::Expr fmt::String
{
  attachNote extensionGenerated("ableC-string");
  forwards to
    ableC_Expr {
      sprintf($Expr{@buf}, $stringLiteralExpr{fmt}, $Expr{@e})
    };
}

production showExpr
top::Expr ::= e::Expr
{
  top.pp = pp"show(${e.pp})";
  attachNote extensionGenerated("ableC-string");
  propagate env, controlStmtContext;
  top.typerep = extType(nilQualifier(), stringType());
  
  nondecorated local type::Type = e.typerep.defaultFunctionArrayLvalueConversion;
  local localErrors::[Message] = e.errors ++ showErrors(top.env, type) ++
    checkStringHeaderDef(top.env) ++
    case top.env.allocContext of
    | unspecifiedAllocContext() :: _ -> [errFromOrigin(top, "An allocator to use must be specfied (e.g. `allocate_using heap;`)")]
    | _ -> []
    end;

  top.buildStr = \ buf::Name len::Name -> (
    nullStmt(), getShowMaxLen(^e, top.env, type),
    ableC_Stmt {
      $Name{len} += $Expr{getShow(ableC_Expr { $Name{buf} + $Name{len} }, ^e, top.env, type)};
    });

  forwards to mkErrorCheck(localErrors, wrapBuildStr(top.buildStr));
}

fun showErrors [Message] ::= env::Env type::Type =
  case getCustomShow(type, env) of
  | just(_) -> []
  | nothing() -> type.showErrors(env)
  end;

fun getShowMaxLen Expr ::= e::Expr env::Env type::Type =
  case getCustomShow(type, env) of
  | just((func, _)) -> ableC_Expr { $Name{func}($Expr{e}) }
  | nothing() -> type.showMaxLenProd(e)
  end;

fun getShow Expr ::= buf::Expr e::Expr env::Env type::Type =
  case getCustomShow(type, env) of
  | just((_, func)) -> ableC_Expr { $Name{func}($Expr{buf}, $Expr{e}) }
  | nothing() -> type.showProd(buf, e)
  end;

production showCharPointerMaxLen
top::Expr ::= e::Expr
{
  attachNote extensionGenerated("ableC-string");
  forwards to
    ableC_Expr {
      // Cast in case argument is const char *
      show_char_pointer_max_len((char *)$Expr{@e})
    };
}

production showCharPointer
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  forwards to
    ableC_Expr {
      // Cast in case argument is const char *
      show_char_pointer($Expr{@buf}, (char *)$Expr{@e})
    };
}

synthesized attribute maxEnumItemLen::Integer;
attribute directStrProd, maxEnumItemLen, showProd occurs on EnumDecl, EnumItemList;

aspect production enumDecl
top::EnumDecl ::= name::MaybeName  dcls::EnumItemList
{
  top.directStrProd = dcls.directStrProd;
  top.maxEnumItemLen = dcls.maxEnumItemLen;
  top.showProd = dcls.showProd;
}

aspect production consEnumItem
top::EnumItemList ::= h::EnumItem  t::EnumItemList
{
  attachNote extensionGenerated("ableC-string");

  top.directStrProd = \ e::Expr ->
    ableC_Expr {
      $Expr{e} == $name{h.name}?
        $Expr{strExpr(mkStringConst(h.name))} :
        $Expr{t.directStrProd(e)}
    };
  top.maxEnumItemLen = max(length(h.name), t.maxEnumItemLen);
  top.showProd = \ buf::Expr e::Expr ->
    ableC_Expr {
      $Expr{e} == $name{h.name}?
        strcpy($Expr{buf}, $stringLiteralExpr{h.name}), $intLiteralExpr{length(h.name)} :
        $Expr{t.showProd(buf, e)}
    };
}

aspect production nilEnumItem
top::EnumItemList ::=
{
  attachNote extensionGenerated("ableC-string");

  top.directStrProd = signedType(intType()).directStrProd;
  top.maxEnumItemLen = length(show(80, top.containingEnum)) + 24;
  top.showProd = \ buf::Expr e::Expr ->
    ableC_Expr {
      sprintf($Expr{buf}, "<%s %d>", $stringLiteralExpr{show(80, top.containingEnum)}, $Expr{e})
    };
}

production showPointerMaxLen
top::Expr ::= e::Expr
{
  attachNote extensionGenerated("ableC-string");
  top.pp = pp"showPointerMaxLen(${e})";
  e.env = top.env;
  e.controlStmtContext = top.controlStmtContext;
  
  local subType::Type =
    case e.typerep of
    | pointerType(_, t) -> ^t
    | _ -> errorType()
    end;
  nondecorated local ptrValName::Name = freshName("ptr_val");
  forwards to
    ableC_Expr {
      ({$directTypeExpr{subType.withoutTypeQualifiers} $Name{ptrValName};
        safe_memcpy(&$Name{ptrValName}, $Expr{^e}, sizeof($directTypeExpr{subType.withoutTypeQualifiers}))?
          $Expr{subType.showMaxLenProd(ableC_Expr { $Name{ptrValName} })} + 1 :
          $intLiteralExpr{length(show(80, e.typerep)) + 6} + MAX_POINTER_STR_LEN;})
    };
}

production showPointer
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  top.pp = pp"showPointer(${buf}, ${e})";
  e.env = top.env;
  e.controlStmtContext = top.controlStmtContext;
  
  local subType::Type =
    case e.typerep of
    | pointerType(_, t) -> ^t
    | _ -> errorType()
    end;
  nondecorated local ptrValName::Name = freshName("ptr_val");
  forwards to
    ableC_Expr {
      ({$directTypeExpr{subType.withoutTypeQualifiers} $Name{ptrValName};
        safe_memcpy(&$Name{ptrValName}, $Expr{^e}, sizeof($directTypeExpr{subType.withoutTypeQualifiers}))?
          ($Expr{^buf}[0] = '&',
           1 + $Expr{subType.showProd(ableC_Expr { $Expr{^buf} + 1 }, declRefExpr(ptrValName))}) :
          sprintf($Expr{@buf}, "<%s at %p>", $stringLiteralExpr{show(80, e.typerep)}, (void*)$Expr{^e});
      })
    };
}

production showOpaquePointerMaxLen
top::Expr ::= e::Expr
{
  attachNote extensionGenerated("ableC-string");
  top.pp = pp"showOpaquePointerMaxLen(${e})";

  propagate env, controlStmtContext;

  local subType::Type =
    case e.typerep of
    | pointerType(_, t) -> ^t
    | _ -> errorType()
    end;
  forwards to
    ableC_Expr {
      $intLiteralExpr{length(show(80, e.typerep)) + 6} + MAX_POINTER_STR_LEN
    };
}

production showOpaquePointer
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  top.pp = pp"showOpaquePointer(${buf}, ${e})";

  local subType::Type =
    case e.typerep of
    | pointerType(_, t) -> ^t
    | _ -> errorType()
    end;
  forwards to
    ableC_Expr {
      sprintf($Expr{@buf}, "<%s at %p>", $stringLiteralExpr{show(80, e.typerep)}, (void*)$Expr{@e})
    };
}

production showStructMaxLen
top::Expr ::= e::Expr
{
  attachNote extensionGenerated("ableC-string");
  top.pp = pp"showStructMaxLen(${e})";
  propagate env, controlStmtContext;

  local decl::Decorated StructDecl =
    case lookupRefId(e.typerep.maybeRefId.fromJust, top.env) of
    | structRefIdItem(decl) :: _ -> decl
    | _ -> error("struct refId not found")
    end;
  
  forwards to
    injectGlobalDeclsExpr(
      foldDecl([maybeValueDecl(decl.showMaxLenFnName, decls(decl.showMaxLenFnDecls))]),
      ableC_Expr { $name{decl.showMaxLenFnName}($Expr{^e}) });
}

production showStruct
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  top.pp = pp"showStruct(${buf}, ${e})";
  propagate env, controlStmtContext;

  local decl::Decorated StructDecl =
    case lookupRefId(e.typerep.maybeRefId.fromJust, top.env) of
    | structRefIdItem(decl) :: _ -> decl
    | _ -> error("struct refId not found")
    end;
  
  forwards to
    injectGlobalDeclsExpr(
      foldDecl([maybeValueDecl(decl.showFnName, decls(decl.showFnDecls))]),
      ableC_Expr { $name{decl.showFnName}($Expr{@buf}, $Expr{^e}) });
}

production showUnionMaxLen
top::Expr ::= e::Expr
{
  attachNote extensionGenerated("ableC-string");
  top.pp = pp"showUnionMaxLen(${e})";
  propagate env, controlStmtContext;
  
  local decl::Decorated UnionDecl =
    case lookupRefId(e.typerep.maybeRefId.fromJust, top.env) of
    | unionRefIdItem(decl) :: _ -> decl
    | _ -> error("union refId not found")
    end;
  
  forwards to
    injectGlobalDeclsExpr(
      foldDecl([maybeValueDecl(decl.showMaxLenFnName, decls(decl.showMaxLenFnDecls))]),
      ableC_Expr { $name{decl.showMaxLenFnName}($Expr{^e}) });
}

production showUnion
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  top.pp = pp"showUnion(${buf}, ${e})";
  propagate env, controlStmtContext;
  
  local decl::Decorated UnionDecl =
    case lookupRefId(e.typerep.maybeRefId.fromJust, top.env) of
    | unionRefIdItem(decl) :: _ -> decl
    | _ -> error("union refId not found")
    end;
  
  forwards to
    injectGlobalDeclsExpr(
      foldDecl([maybeValueDecl(decl.showFnName, decls(decl.showFnDecls))]),
      ableC_Expr { $name{decl.showFnName}($Expr{@buf}, $Expr{^e}) });
}

synthesized attribute showDeclErrors::([Message] ::= Env) occurs on StructDecl, UnionDecl;
synthesized attribute showMaxLenFnName::String occurs on StructDecl, UnionDecl;
synthesized attribute showFnName::String occurs on StructDecl, UnionDecl;
synthesized attribute showMaxLenFnDecls::Decls occurs on StructDecl, UnionDecl;
synthesized attribute showFnDecls::Decls occurs on StructDecl, UnionDecl;
monoid attribute showMaxLenTransform::(Expr ::= Expr) with pure(mkIntConst(0)), lift2(joinMaxLens, _, _);
monoid attribute showTransform::([Stmt] ::= Expr);
attribute showErrors, showMaxLenTransform, showTransform occurs on StructDecl, UnionDecl, StructItemList, StructItem, StructDeclarators, StructDeclarator;
propagate showErrors, showMaxLenTransform on StructDecl, UnionDecl;
propagate showErrors, showMaxLenTransform, showTransform on StructItemList, StructItem, StructDeclarators;

fun joinMaxLens Expr ::= e1::Expr e2::Expr =
  ableC_Expr { $Expr{e1} + 2 + $Expr{e2} };

fun foldShowItems Stmt ::= ss::[Stmt] =
  if null(ss) then nullStmt()
  else foldr1(\ s1 s2 ->
    ableC_Stmt {
      $Stmt{s1}
      buf[bufIndex++] = ',';
      buf[bufIndex++] = ' ';
      $Stmt{s2}
    }, ss);

aspect production structDecl
top::StructDecl ::= attrs::Attributes  name::MaybeName  dcls::StructItemList
{
  attachNote extensionGenerated("ableC-string");
  local n::String = name.maybename.fromJust.name;
  top.showDeclErrors =
    \ env::Env ->
      if !name.maybename.isJust
      then [errFromOrigin(ambientOrigin(), "Cannot show anonymous struct")]
      else if null(lookupValue(top.showFnName, env))
      then
        case attachNote logicalLocationFromOrigin(top) on
            top.showErrors(addEnv([valueDef(top.showFnName, errorValueItem())], env))
          end of
        | [] -> []
        | m -> [nested(getParsedOriginLocationOrFallback(ambientOrigin()), s"In showing struct ${n}", m)]
        end
      else [];
  top.showMaxLenFnName = s"_show_${n}_max_len";
  top.showFnName = s"_show_${n}";
  top.showMaxLenFnDecls =
    ableC_Decls {
      proto_typedef size_t;
      static size_t $name{top.showMaxLenFnName}(struct $name{n});
      static size_t $name{top.showMaxLenFnName}(struct $name{n} val) {
        return $Expr{top.showMaxLenTransform(ableC_Expr { val })};
      }
    };
  top.showFnDecls =
    ableC_Decls {
      proto_typedef size_t;
      static size_t $name{top.showFnName}(char *, struct $name{n});
      static size_t $name{top.showFnName}(char *buf, struct $name{n} val) {
        size_t bufIndex = 0;
        $Stmt{foldShowItems(top.showTransform(ableC_Expr { val }))}
        buf[bufIndex] = '\0';
        return bufIndex;
      }
    };
  top.showMaxLenTransform <- \ _ -> mkIntConst(2);
  top.showTransform := \ e::Expr -> [ableC_Stmt {
    buf[bufIndex++] = '{';
    $Stmt{foldShowItems(dcls.showTransform(e))};
    buf[bufIndex++] = '}';
  }];
}

aspect production unionDecl
top::UnionDecl ::= attrs::Attributes  name::MaybeName  dcls::StructItemList
{
  attachNote extensionGenerated("ableC-string");
  local n::String = name.maybename.fromJust.name;
  local checkExpr::Expr = errorExpr([]); -- Expr that gets decorated to pass the right origin and env
  top.showDeclErrors =
    \ env::Env ->
      if !name.maybename.isJust
      then [errFromOrigin(ambientOrigin(), "Cannot show anonymous union")]
      else if null(lookupValue(top.showFnName, env))
      then
        case attachNote logicalLocationFromOrigin(top) on
            top.showErrors(addEnv([valueDef(top.showFnName, errorValueItem())], env))
          end of
        | [] -> []
        | m -> [nested(getParsedOriginLocationOrFallback(ambientOrigin()), s"In showing union ${n}", m)]
        end
      else [];
  top.showMaxLenFnName = s"_show_${n}_max_len";
  top.showFnName = s"_show_${n}";
  top.showMaxLenFnDecls =
    ableC_Decls {
      proto_typedef size_t;
      static size_t $name{top.showMaxLenFnName}(struct $name{n});
      static size_t $name{top.showMaxLenFnName}(struct $name{n} val) {
        return $Expr{top.showMaxLenTransform(ableC_Expr { val })};
      }
    };
  top.showFnDecls =
    ableC_Decls {
      proto_typedef size_t;
      static size_t $name{top.showFnName}(char *, union $name{n});
      static size_t $name{top.showFnName}(char *buf, union $name{n} val) {
        size_t bufIndex = 0;
        $Stmt{foldShowItems(top.showTransform(ableC_Expr { val }))}
        buf[bufIndex] = '\0';
        return bufIndex;
      }
    };
  top.showMaxLenTransform <- \ _ -> mkIntConst(2);
  top.showTransform := \ e::Expr -> [ableC_Stmt {
    buf[bufIndex++] = '{';
    $Stmt{foldShowItems(dcls.showTransform(e))};
    buf[bufIndex++] = '}';
  }];
}

aspect production structField
top::StructDeclarator ::= name::Name  ty::TypeModifierExpr  attrs::Attributes
{
  attachNote extensionGenerated("ableC-string");
  local checkExpr::Expr = errorExpr([]);
  top.showErrors := \ env::Env ->
    attachNote logicalLocationFromOrigin(top) on showErrors(env, top.typerep) end;
  local fieldStrLen::Integer = length("." ++ name.name ++ " = ");
  top.showMaxLenTransform := \ e::Expr ->
    addExpr(
      mkIntConst(fieldStrLen),
      getShowMaxLen(ableC_Expr { $Expr{e}.$Name{^name} }, top.env, top.typerep));
  top.showTransform := \ e::Expr -> [ableC_Stmt {
    strcpy(buf + bufIndex, $stringLiteralExpr{"." ++ name.name ++ " = "});
    bufIndex += $intLiteralExpr{fieldStrLen};
    bufIndex += $Expr{getShow(ableC_Expr { buf + bufIndex }, ableC_Expr { $Expr{e}.$Name{^name} }, top.env, top.typerep)};
  }];
}
aspect production structBitfield
top::StructDeclarator ::= name::MaybeName  ty::TypeModifierExpr  e::Expr  attrs::Attributes
{
  attachNote extensionGenerated("ableC-string");
  local checkExpr::Expr = errorExpr([]);
  top.showErrors := \ env::Env ->
    attachNote logicalLocationFromOrigin(top) on showErrors(env, top.typerep) end;
  local fieldStrLen::Integer = length("." ++ name.maybename.fromJust.name ++ " = ");
  top.showMaxLenTransform := \ e::Expr ->
    case name.maybename of
    | just(n) -> addExpr(
        mkIntConst(fieldStrLen),
        getShowMaxLen(ableC_Expr { $Expr{e}.$Name{n} }, top.env, top.typerep))
    | nothing() -> mkIntConst(0)
    end;
  top.showTransform := \ e::Expr ->
    case name.maybename of
    | just(n) -> [ableC_Stmt {
        strcpy(buf + bufIndex, $stringLiteralExpr{"." ++ n.name ++ " = "});
        bufIndex += $intLiteralExpr{fieldStrLen};
        bufIndex += $Expr{getShow(ableC_Expr { buf + bufIndex }, ableC_Expr { $Expr{e}.$Name{n} }, top.env, top.typerep)};
      }]
    | nothing() -> []
    end;
}
aspect production warnStructField
top::StructDeclarator ::= msg::[Message]
{
  propagate showErrors, showMaxLenTransform, showTransform;
}

production assignString implements AssignOp
top::Expr ::= @lhs::Expr @rhs::Expr
{
  top.pp = pp"${lhs.pp} = ${rhs.pp}";
  forwards to bindAssignOp(lhs, rhs,
    hostEqExpr(lhs.bindLhsRefExpr, strExpr(rhs.bindRefExpr)));
}

production concatString implements BinaryOp
top::Expr ::= @e1::Expr @e2::Expr
{
  top.pp = pp"${e1.pp} + ${e2.pp}";
  attachNote extensionGenerated("ableC-string");
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    attachNote logicalLocationFromOrigin(e1) on
      e1.typerep.defaultFunctionArrayLvalueConversion.strErrors(e1.env)
    end ++
    attachNote logicalLocationFromOrigin(e2) on
      e2.typerep.defaultFunctionArrayLvalueConversion.strErrors(e2.env)
    end ++
    case top.env.allocContext of
    | unspecifiedAllocContext() :: _ -> [errFromOrigin(top, "An allocator to use must be specfied (e.g. `allocate_using heap;`)")]
    | _ -> []
    end;

  top.typerep = extType(nilQualifier(), stringType());
  top.buildStr = \ buf::Name len::Name ->
    let buildE1::(Stmt, Expr, Stmt) = e1.buildStr(buf, len),
        buildE2::(Stmt, Expr, Stmt) = e2.buildStr(buf, len)
    in (seqStmt(buildE1.1, buildE2.1), addExpr(buildE1.2, buildE2.2), seqStmt(buildE1.3, buildE2.3))
    end;

  forward fwrd = transformBinaryOp(e1, e2, wrapBuildStr(top.buildStr));
  forwards to
    if null(localErrors) then @fwrd else errorExpr(localErrors);
}

production repeatString implements BinaryOp
top::Expr ::= @e1::Expr @e2::Expr
{
  top.pp = pp"${e1.pp} * ${e2.pp}";
  attachNote extensionGenerated("ableC-string");
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    case top.env.allocContext of
    | unspecifiedAllocContext() :: _ -> [errFromOrigin(top, "An allocator to use must be specfied (e.g. `allocate_using heap;`)")]
    | _ -> []
    end ++
    checkStringType(e1.typerep, "*") ++
    if e2.typerep.isIntegerType
    then []
    else [errFromOrigin(e2, s"string repeat must have integer type, but got ${show(80, e2.typerep)}")];

  top.typerep = extType(nilQualifier(), stringType());

  nondecorated local countName::Name = freshName("count");
  nondecorated local iName::Name = freshName("i");
  top.buildStr = \ buf::Name len::Name ->
    let buildE1::(Stmt, Expr, Stmt) = e1.buildStr(buf, len)
    in (
      ableC_Stmt {
        proto_typedef size_t;
        $Stmt{buildE1.1}
        size_t $Name{countName} = $Expr{^e2};
      },
      mulExpr(buildE1.2, declRefExpr(countName)),
      ableC_Stmt {
        proto_typedef size_t;
        for (size_t $Name{iName} = 0; $Name{iName} < $Name{countName}; $Name{iName}++) {
          $Stmt{buildE1.3}
        }
      })
    end;

  forward fwrd = transformBinaryOp(e1, e2, wrapBuildStr(top.buildStr));
  forwards to
    if null(localErrors) then @fwrd else errorExpr(localErrors);
}

production equalsString implements BinaryOp
top::Expr ::= @e1::Expr @e2::Expr
{
  top.pp = pp"${e1.pp} == ${e2.pp}";
  attachNote extensionGenerated("ableC-string");
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    attachNote logicalLocationFromOrigin(e1) on
      e1.typerep.defaultFunctionArrayLvalueConversion.strErrors(e1.env)
    end ++
    attachNote logicalLocationFromOrigin(e2) on
      e2.typerep.defaultFunctionArrayLvalueConversion.strErrors(e2.env)
    end ++
    checkStringHeaderDef(top.env) ++
    case top.env.allocContext of
    | unspecifiedAllocContext() :: _ -> [errFromOrigin(top, "An allocator to use must be specfied (e.g. `allocate_using heap;`)")]
    | _ -> []
    end;

  forward fwrd = bindBinaryOp(e1, e2,
    directCallExpr(name("equals_string"),
      consExpr(strExpr(e1.bindRefExpr), consExpr(strExpr(e2.bindRefExpr), nilExpr()))));
  forwards to
    if null(localErrors) then @fwrd else errorExpr(localErrors);
}

production subscriptString implements BinaryOp
top::Expr ::= @e1::Expr @e2::Expr
{
  top.pp = pp"${e1.pp}[${e2.pp}]";
  attachNote extensionGenerated("ableC-string");
  propagate controlStmtContext;
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    checkStringHeaderDef(top.env) ++
    checkStringType(e1.typerep, "[]") ++
    if e2.typerep.isIntegerType
    then []
    else [errFromOrigin(e2, s"string index must have integer type, but got ${show(80, e2.typerep)}")];

  forward fwrd = callBinaryOp(e1, e2, name("subscript_string"), nilExpr());
  forwards to
    if null(localErrors) then @fwrd else errorExpr(localErrors);
}

production memberString implements MemberAccess
top::Expr ::= @lhs::Expr deref::Boolean rhs::Name
{
  forwards to bindMemberAccess(lhs, deref, @rhs,
    case rhs.name of
    | "length" -> ableC_Expr { ((struct _string_s)$Expr{lhs.bindRefExpr}).length }
    | "text"   -> ableC_Expr { ((struct _string_s)$Expr{lhs.bindRefExpr}).text }
    | n -> errorExpr([errFromOrigin(rhs, s"string does not have field ${n}")])
    end);
}

production memberCallString implements MemberCall
top::Expr ::= @lhs::Expr deref::Boolean rhs::Name a::Exprs
{
  top.pp = forwardParent.pp;
  forwards to bindMemberCall(lhs, deref, @rhs, @a,
    case rhs.name, a.bindRefExprs of
    | "substring", [i1, i2] -> substringString(lhs.bindRefExpr, i1, i2)
    | "copy", [] -> copyString(lhs.bindRefExpr)
    | n, _ -> errorExpr([errFromOrigin(rhs, s"string does not have method ${n} with ${toString(a.count)} arguments")])
    end);
}

production substringString
top::Expr ::= s::Expr i1::Expr i2::Expr
{
  top.pp = pp"${s}.substring(${i1}, ${i2})";
  attachNote extensionGenerated("ableC-string");

  local localErrors::[Message] =
    s.errors ++ i1.errors ++ i2.errors ++
    checkStringHeaderDef(top.env) ++
    case top.env.allocContext of
    | unspecifiedAllocContext() :: _ -> [errFromOrigin(top, "An allocator to use must be specfied (e.g. `allocate_using heap;`)")]
    | _ -> []
    end ++
    checkStringType(s.typerep, "substring") ++
    (if i1.typerep.isIntegerType then []
     else [errFromOrigin(i1, "substring indices must have integer type")]) ++
    (if i2.typerep.isIntegerType then []
     else [errFromOrigin(i2, "substring indices must have integer type")]);

  nondecorated local bufName::Name = freshName("buf");
  nondecorated local lenName::Name = freshName("len");
  forward fwrd = ableC_Expr {
    proto_typedef size_t;
    ({_check_string_bounds($Expr{@s}, $Expr{@i1}, $Expr{@i2});
      size_t $Name{lenName} = $Expr{^i2} - $Expr{^i1};
      char *$Name{bufName} = allocate($Name{lenName} + 1);
      memcpy($Name{bufName}, $Expr{^s}.text + $Expr{^i1}, $Name{lenName});
      $Name{bufName}[$Name{lenName}] = '\0';
      ($directTypeExpr{extType(nilQualifier(), stringType())})(struct _string_s){
        $Name{lenName}, $Name{bufName}
      };})
  };
  forwards to
    if null(localErrors) then @fwrd else errorExpr(localErrors);
}


production copyString
top::Expr ::= s::Expr
{
  top.pp = pp"${s}.copy()";
  attachNote extensionGenerated("ableC-string");

  local localErrors::[Message] =
    s.errors ++
    checkStringHeaderDef(top.env) ++
    case top.env.allocContext of
    | unspecifiedAllocContext() :: _ -> [errFromOrigin(top, "An allocator to use must be specfied (e.g. `allocate_using heap;`)")]
    | _ -> []
    end ++
    checkStringType(s.typerep, "copy");

  nondecorated local bufName::Name = freshName("buf");
  forward fwrd = ableC_Expr {
    ($directTypeExpr{extType(nilQualifier(), stringType())})(struct _string_s){
      $Expr{@s}.length, memcpy(allocate($Expr{^s}.length + 1), $Expr{^s}.text, $Expr{^s}.length + 1)
    }
  };
  forwards to
    if null(localErrors) then @fwrd else errorExpr(localErrors);
}

production initString implements ExprInitializer
top::Initializer ::= e::Expr
{
  top.pp = e.pp;
  forwards to bindExprInitializer(@e, strExpr(e.bindRefExpr));
}

-- Check the given env for the given function name
fun checkStringHeaderDef [Message] ::= env::Env =
  if !null(lookupValue("MAX_POINTER_STR_LEN", env))
  then []
  else [errFromOrigin(ambientOrigin(), "Missing include of string.xh")];

-- Check that operand has string type
fun checkStringType [Message] ::= t::Type op::String =
  if typeAssignableTo(extType(nilQualifier(), stringType()), t)
  then []
  else [errFromOrigin(ambientOrigin(), s"Operand to ${op} expected string type (got ${show(80, t)})")];
