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
top::Expr ::= f::Name @a::Exprs handler::(Expr ::= Expr)
{
  top.pp = pp"${f.pp}(${ppImplode(pp", ", a.pps)})";
  forwards to bindDirectCallExpr(\ es::[Expr] ->
    case es of
    | [e] -> handler(e)
    | _ -> errorExpr([errFromOrigin(top, s"${f.name} expected exactly 1 argument, got ${toString(a.count)}")])
    end)(^f, a);
}

production strExpr
top::Expr ::= e::Expr
{
  top.pp = pp"str(${e.pp})";
  propagate env, controlStmtContext;
  
  local type::Type = e.typerep.defaultFunctionArrayLvalueConversion;
  local localErrors::[Message] = e.errors ++ type.strErrors(e.env) ++
    case top.env.allocContext of
    | unspecifiedAllocContext() :: _ -> [errFromOrigin(top, "An allocator to use must be specfied (e.g. `allocate_using heap;`)")]
    | _ -> []
    end;
  local fwrd::Expr = type.strProd(^e); -- Unavoidable re-decoration here, since we don't know what env strProd will provide to e
  forwards to mkErrorCheck(localErrors, @fwrd);
}

production strCharPointer
top::Expr ::= e::Expr
{
  attachNote extensionGenerated("ableC-string");
  nondecorated local bufName::Name = freshName("buf");
  forwards to
    ableC_Expr {
      ({char *$Name{bufName} = allocate(strlen($Expr{@e}) + 1);
        strcpy($Name{bufName}, $Expr{^e});
        ($directTypeExpr{extType(nilQualifier(), stringType())})(struct _string_s){
          strlen($Name{bufName}), $Name{bufName}
        };})
    };
}

production strChar
top::Expr ::= e::Expr
{
  attachNote extensionGenerated("ableC-string");
  nondecorated local bufName::Name = freshName("buf");
  forwards to
    ableC_Expr {
      ({char *$Name{bufName} = allocate(2);
        $Name{bufName}[0] = $Expr{@e};
        $Name{bufName}[1] = '\0';
        ($directTypeExpr{extType(nilQualifier(), stringType())})(struct _string_s){
          1, &$Name{bufName}
        };})
    };
}

production strPointer
top::Expr ::= e::Expr
{
  attachNote extensionGenerated("ableC-string");
  nondecorated local bufName::Name = freshName("buf");
  forwards to
    ableC_Expr {
      ({char *$Name{bufName} = allocate(MAX_POINTER_STR_LEN + 1);
        sprintf($Name{bufName}, "%p", $Expr{@e});
        ($directTypeExpr{extType(nilQualifier(), stringType())})(struct _string_s){
          strlen($Name{bufName}), $Name{bufName}
        };})
    };
}

production strBool
top::Expr ::= e::Expr
{
  attachNote extensionGenerated("ableC-string");
  forwards to
    ableC_Expr {
      $Expr{@e}? TRUE_STR : FALSE_STR
    };
}

production strNum
top::Expr ::= e::Expr width::Expr fmt::String
{
  attachNote extensionGenerated("ableC-string");
  nondecorated local bufName::Name = freshName("buf");
  forwards to
    ableC_Expr {
      ({char *$Name{bufName} = allocate($Expr{@width} + 1);
        sprintf($Name{bufName}, $stringLiteralExpr{fmt}, $Expr{@e});
        ($directTypeExpr{extType(nilQualifier(), stringType())})(struct _string_s){
          strlen($Name{bufName}), $Name{bufName}
        };})
    };
}

production showExpr
top::Expr ::= e::Expr
{
  top.pp = pp"show(${e.pp})";
  attachNote extensionGenerated("ableC-string");
  propagate env, controlStmtContext;
  
  nondecorated local type::Type = e.typerep.defaultFunctionArrayLvalueConversion;
  local localErrors::[Message] = e.errors ++ showErrors(top.env, type) ++
    case top.env.allocContext of
    | unspecifiedAllocContext() :: _ -> [errFromOrigin(top, "An allocator to use must be specfied (e.g. `allocate_using heap;`)")]
    | _ -> []
    end;

  nondecorated local lenName::Name = freshName("len");
  nondecorated local bufName::Name = freshName("buf");
  local fwrd::Expr = ableC_Expr {
    proto_typedef size_t;
    ({char *$Name{bufName} = allocate($Expr{getShowMaxLen(^e, top.env, type)} + 1);
      size_t $Name{lenName} = $Expr{getShow(declRefExpr(bufName), ^e, top.env, type)};
      ($directTypeExpr{extType(nilQualifier(), stringType())})(struct _string_s){
        $Name{lenName}, $Name{bufName}
      };})
  };
  forwards to mkErrorCheck(localErrors, @fwrd);
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

production showBool
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  forwards to
    ableC_Expr {
      strcpy($Expr{@buf}, $Expr{@e}? "true" : "false")
    };
}

production showNum
top::Expr ::= buf::Expr e::Expr fmt::String
{
  attachNote extensionGenerated("ableC-string");
  forwards to
    ableC_Expr {
      sprintf($Expr{@buf}, $stringLiteralExpr{fmt}, $Expr{@e}),
      strlen($Expr{^buf})
    };
}

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
attribute strProd, maxEnumItemLen, showProd occurs on EnumDecl, EnumItemList;

aspect production enumDecl
top::EnumDecl ::= name::MaybeName  dcls::EnumItemList
{
  top.strProd = dcls.strProd;
  top.maxEnumItemLen = dcls.maxEnumItemLen;
  top.showProd = dcls.showProd;
}

aspect production consEnumItem
top::EnumItemList ::= h::EnumItem  t::EnumItemList
{
  attachNote extensionGenerated("ableC-string");

  top.strProd = \ e::Expr ->
    ableC_Expr {
      $Expr{e} == $name{h.name}?
        $Expr{strExpr(mkStringConst(h.name))} :
        $Expr{t.strProd(e)}
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

  top.strProd = strNum(_, ableC_Expr { MAX_INT_STR_LEN }, "%d");
  top.maxEnumItemLen = length(show(80, top.containingEnum)) + 24;
  top.showProd = \ buf::Expr e::Expr ->
    ableC_Expr {
      sprintf($Expr{buf}, "<%s %d>", $stringLiteralExpr{show(80, top.containingEnum)}, $Expr{e}),
      strlen($Expr{buf})
    };
}

production showPointerMaxLen
top::Expr ::= e::Expr
{
  attachNote extensionGenerated("ableC-string");
  top.pp = pp"showPointerMaxLen(${e})";
  
  local subType::Type =
    case e.typerep of
    | pointerType(_, t) -> ^t
    | _ -> errorType()
    end;
  nondecorated local ptrValName::Name = freshName("ptr_val");
  forwards to
    ableC_Expr {
      ({$directTypeExpr{subType.withoutTypeQualifiers} $Name{ptrValName};
        _Bool _illegal = 0;
        
        // Hacky way of testing if a pointer can be dereferenced validly
        // TODO: This isn't remotely thread safe, but I don't know of a better way
        if($Expr{@e}) {
          _set_handler();
          if (!setjmp(_jump)) {
            $Name{ptrValName} = *$Expr{^e};
          } else {
            _illegal = 1;
          }
          _clear_handler();
        } else {
          _illegal = 1;
        }

        _illegal?
          $intLiteralExpr{length(show(80, e.typerep)) + 6} + MAX_POINTER_STR_LEN :
          $Expr{subType.showMaxLenProd(ableC_Expr { $Name{ptrValName} })} + 1;})
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
        _Bool _illegal = 0;
        
        // Hacky way of testing if a pointer can be dereferenced validly
        // TODO: This isn't remotely thread safe, but I don't know of a better way
        if($Expr{^e}) {
          _set_handler();
          if (!setjmp(_jump)) {
            $Name{ptrValName} = *$Expr{^e};
          } else {
            _illegal = 1;
          }
          _clear_handler();
        } else {
          _illegal = 1;
        }
        
        if (_illegal) {
          sprintf($Expr{@buf}, "<%s at %p>", $stringLiteralExpr{show(80, e.typerep)}, $Expr{^e});
        } else {
          buf[0] = '&';
          $Expr{subType.showProd(ableC_Expr { $Name{ptrValName} }, ableC_Expr { $Expr{^buf} + 1 })};
        }
        strlen($Expr{^buf});})
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
      ({sprintf($Expr{@buf}, "<%s at %p>", $stringLiteralExpr{show(80, e.typerep)}, $Expr{@e});
        strlen($Expr{^buf});})
    };
}

production showStructMaxLen
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  top.pp = pp"showStructMaxLen(${buf}, ${e})";
  
  local decl::Decorated StructDecl =
    case lookupRefId(e.typerep.maybeRefId.fromJust, top.env) of
    | structRefIdItem(decl) :: _ -> decl
    | _ -> error("struct refId not found")
    end;
  
  forwards to
    injectGlobalDeclsExpr(
      foldDecl([maybeValueDecl(decl.showMaxLenFnName, decls(decl.showMaxLenFnDecls))]),
      ableC_Expr { $name{decl.showMaxLenFnName}($Expr{@buf}, $Expr{@e}) });
}

production showStruct
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  top.pp = pp"showStruct(${buf}, ${e})";
  
  local decl::Decorated StructDecl =
    case lookupRefId(e.typerep.maybeRefId.fromJust, top.env) of
    | structRefIdItem(decl) :: _ -> decl
    | _ -> error("struct refId not found")
    end;
  
  forwards to
    injectGlobalDeclsExpr(
      foldDecl([maybeValueDecl(decl.showFnName, decls(decl.showFnDecls))]),
      ableC_Expr { $name{decl.showFnName}($Expr{@buf}, $Expr{@e}) });
}

production showUnionMaxLen
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  top.pp = pp"showUnionMaxLen(${buf}, ${e})";
  
  local decl::Decorated UnionDecl =
    case lookupRefId(e.typerep.maybeRefId.fromJust, top.env) of
    | unionRefIdItem(decl) :: _ -> decl
    | _ -> error("union refId not found")
    end;
  
  forwards to
    injectGlobalDeclsExpr(
      foldDecl([maybeValueDecl(decl.showMaxLenFnName, decls(decl.showMaxLenFnDecls))]),
      ableC_Expr { $name{decl.showMaxLenFnName}($Expr{@buf}, $Expr{@e}) });
}

production showUnion
top::Expr ::= buf::Expr e::Expr
{
  attachNote extensionGenerated("ableC-string");
  top.pp = pp"showUnion(${buf}, ${e})";
  
  local decl::Decorated UnionDecl =
    case lookupRefId(e.typerep.maybeRefId.fromJust, top.env) of
    | unionRefIdItem(decl) :: _ -> decl
    | _ -> error("union refId not found")
    end;
  
  forwards to
    injectGlobalDeclsExpr(
      foldDecl([maybeValueDecl(decl.showFnName, decls(decl.showFnDecls))]),
      ableC_Expr { $name{decl.showFnName}($Expr{@buf}, $Expr{@e}) });
}

synthesized attribute showDeclErrors::([Message] ::= Env) occurs on StructDecl, UnionDecl;
synthesized attribute showMaxLenFnName::String occurs on StructDecl, UnionDecl;
synthesized attribute showFnName::String occurs on StructDecl, UnionDecl;
synthesized attribute showMaxLenFnDecls::Decls occurs on StructDecl, UnionDecl;
synthesized attribute showFnDecls::Decls occurs on StructDecl, UnionDecl;
monoid attribute showMaxLenTransform::(Expr ::= Expr) with \ _ -> mkIntConst(0), joinMaxLen;
monoid attribute showTransform::(Stmt ::= Expr) with \ _ -> nullStmt(), joinShowFields;
attribute showErrors, showMaxLenTransform, showTransform occurs on StructDecl, UnionDecl, StructItemList, StructItem, StructDeclarators, StructDeclarator;
propagate showErrors, showMaxLenTransform on StructDecl, UnionDecl;
propagate showErrors, showMaxLenTransform, showTransform on StructItemList, StructItem, StructDeclarators;

fun joinMaxLen (Expr ::= Expr) ::= e1::(Expr ::= Expr) e2::(Expr ::= Expr) =
  \ e::Expr -> ableC_Expr {
    $Expr{e1(e)} + $Expr{e2(e)}
  };

fun joinShowFields (Stmt ::= Expr) ::= s1::(Stmt ::= Expr) s2::(Stmt ::= Expr) =
  \ e::Expr -> ableC_Stmt {
    $Stmt{s1(e)}
    buf[bufIndex++] = ',';
    buf[bufIndex++] = ' ';
    $Stmt{s2(e)}
  };

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
        $Stmt{top.showTransform(ableC_Expr { val })}
        return bufIndex;
      }
    };
  top.showTransform := \ e::Expr -> ableC_Stmt {
    buf[bufIndex++] = '{';
    $Stmt{dcls.showTransform(e)};
    buf[bufIndex++] = '}';
  };
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
        $Stmt{top.showTransform(ableC_Expr { val })}
        return bufIndex;
      }
    };
  top.showTransform := \ e::Expr -> ableC_Stmt {
    buf[bufIndex++] = '{';
    $Stmt{dcls.showTransform(e)};
    buf[bufIndex++] = '}';
  };
}

aspect production structField
top::StructDeclarator ::= name::Name  ty::TypeModifierExpr  attrs::Attributes
{
  attachNote extensionGenerated("ableC-string");
  local checkExpr::Expr = errorExpr([]);
  top.showErrors := \ env::Env ->
    attachNote logicalLocationFromOrigin(top) on showErrors(env, top.typerep) end;
  top.showMaxLenTransform := \ e::Expr ->
    getShowMaxLen(ableC_Expr { $Expr{e}.$Name{^name} }, top.env, top.typerep);
  top.showTransform := \ e::Expr -> ableC_Stmt {
    strcpy(buf + bufIndex, $stringLiteralExpr{"." ++ name.name ++ " = "});
    bufIndex += $intLiteralExpr{length("." ++ name.name ++ " = ")};
    bufIndex += $Expr{getShow(ableC_Expr { buf }, ableC_Expr { $Expr{e}.$Name{^name} }, top.env, top.typerep)};
  };
}
aspect production structBitfield
top::StructDeclarator ::= name::MaybeName  ty::TypeModifierExpr  e::Expr  attrs::Attributes
{
  attachNote extensionGenerated("ableC-string");
  local checkExpr::Expr = errorExpr([]);
  top.showErrors := \ env::Env ->
    attachNote logicalLocationFromOrigin(top) on showErrors(env, top.typerep) end;
  top.showMaxLenTransform := \ e::Expr ->
    case name.maybename of
    | just(n) -> getShowMaxLen(ableC_Expr { $Expr{e}.$Name{n} }, top.env, top.typerep)
    | nothing() -> mkIntConst(0)
    end;
  top.showTransform := \ e::Expr ->
    case name.maybename of
    | just(n) -> ableC_Stmt {
        strcpy(buf + bufIndex, $stringLiteralExpr{"." ++ n.name ++ " = "});
        bufIndex += $intLiteralExpr{length("." ++ n.name ++ " = ")};
        bufIndex += $Expr{getShow(ableC_Expr { buf }, ableC_Expr { $Expr{e}.$Name{n} }, top.env, top.typerep)};
      }
    | nothing() -> nullStmt()
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
  
  forwards to eqExpr(@lhs, strExpr(@rhs));
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
    checkStringHeaderDef("concat_string", top.env) ++
    case top.env.allocContext of
    | unspecifiedAllocContext() :: _ -> [errFromOrigin(top, "An allocator to use must be specfied (e.g. `allocate_using heap;`)")]
    | _ -> []
    end;

  forward fwrd =
    directCallExpr(
      name("concat_string"),
      consExpr(strExpr(@e1), consExpr(strExpr(@e2), nilExpr())));
  forwards to
    if null(localErrors) then @fwrd else errorExpr(localErrors);
}

production repeatString implements BinaryOp
top::Expr ::= @e1::Expr @e2::Expr
{
  top.pp = pp"${e1.pp} * ${e2.pp}";
  attachNote extensionGenerated("ableC-string");
  propagate controlStmtContext;
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    checkStringHeaderDef("repeat_string", top.env) ++
    case top.env.allocContext of
    | unspecifiedAllocContext() :: _ -> [errFromOrigin(top, "An allocator to use must be specfied (e.g. `allocate_using heap;`)")]
    | _ -> []
    end ++
    checkStringType(e1.typerep, "*") ++
    if e2.typerep.isIntegerType
    then []
    else [errFromOrigin(e2, s"string repeat must have integer type, but got ${show(80, e2.typerep)}")];

  forward fwrd =
    directCallExpr(
      name("repeat_string"),
      consExpr(strExpr(@e1), consExpr(strExpr(@e2), nilExpr())));
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
    checkStringHeaderDef("equals_string", top.env) ++
    case top.env.allocContext of
    | unspecifiedAllocContext() :: _ -> [errFromOrigin(top, "An allocator to use must be specfied (e.g. `allocate_using heap;`)")]
    | _ -> []
    end;
  
  local fwrd::Expr =
    directCallExpr(
      name("equals_string"),
      consExpr(strExpr(@e1), consExpr(strExpr(@e2), nilExpr())));
  forwards to mkErrorCheck(localErrors, @fwrd);
}

production subscriptString implements BinaryOp
top::Expr ::= @e1::Expr @e2::Expr
{
  top.pp = pp"${e1.pp}[${e2.pp}]";
  attachNote extensionGenerated("ableC-string");
  propagate controlStmtContext;
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    checkStringHeaderDef("subscript_string", top.env) ++
    case top.env.allocContext of
    | unspecifiedAllocContext() :: _ -> [errFromOrigin(top, "An allocator to use must be specfied (e.g. `allocate_using heap;`)")]
    | _ -> []
    end ++
    checkStringType(e1.typerep, "[]") ++
    if e2.typerep.isIntegerType
    then []
    else [errFromOrigin(e2, s"string index must have integer type, but got ${show(80, e2.typerep)}")];
  
  local fwrd::Expr =
    directCallExpr(
      name("subscript_string"),
      consExpr(strExpr(@e1), consExpr(strExpr(@e2), nilExpr())));
  forwards to mkErrorCheck(localErrors, @fwrd);
}

production callMemberString
top::Expr ::= lhs::Expr deref::Boolean rhs::Name a::Exprs
{
  forwards to
    case rhs.name of
    | "substring" -> substringString(@lhs, @a)
    | n -> errorExpr([errFromOrigin(rhs, s"string does not have field ${n}")])
    end;
}

production memberString implements MemberAccess
top::Expr ::= @lhs::Expr deref::Boolean rhs::Name
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
      ((const struct _string_s)$Expr{@lhs}).$Name{@rhs}
    };
  forwards to mkErrorCheck(localErrors, @fwrd);
}

production substringString
top::Expr ::= e1::Expr a::Exprs
{
  top.pp = pp"${e1.pp}.substring(${ppImplode(pp", ", a.pps)}";
  attachNote extensionGenerated("ableC-string");

  local localErrors::[Message] =
    e1.errors ++ a.errors ++
    checkStringHeaderDef("substring", top.env) ++
    case top.env.allocContext of
    | unspecifiedAllocContext() :: _ -> [errFromOrigin(top, "An allocator to use must be specfied (e.g. `allocate_using heap;`)")]
    | _ -> []
    end ++
    checkStringType(e1.typerep, "substring") ++
    a.argumentErrors;
  forward fwrd =
    directCallExpr(
      name("substring"),
      consExpr(@e1, @a));
  forwards to
    if null(localErrors) then @fwrd else errorExpr(localErrors);
}

production initString
top::Initializer ::= e::Expr
{
  forwards to exprInitializer(strExpr(@e));
}

-- Check the given env for the given function name
fun checkStringHeaderDef [Message] ::= n::String env::Env =
  if !null(lookupValue(n, env))
  then []
  else [errFromOrigin(ambientOrigin(), "Missing include of string.xh")];

-- Check that operand has string type
fun checkStringType [Message] ::= t::Type op::String =
  if typeAssignableTo(extType(nilQualifier(), stringType()), t)
  then []
  else [errFromOrigin(ambientOrigin(), s"Operand to ${op} expected string type (got ${show(80, t)})")];
