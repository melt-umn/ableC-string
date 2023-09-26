grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

-- Track any custom show implementation's names.
synthesized attribute customShows::Scopes<Name> occurs on Env;

aspect production emptyEnv_i
top::Env ::=
{
  top.customShows = emptyScope();
}
aspect production addEnv_i
top::Env ::= d::Defs  e::Decorated Env
{
  top.customShows = addGlobalScope(gd.customShowContribs, addScope(d.customShowContribs, e.customShows));
}
aspect production openScopeEnv_i
top::Env ::= e::Decorated Env
{
  top.customShows = openScope(e.customShows);
}
aspect production globalEnv_i
top::Env ::= e::Decorated Env
{
  top.customShows = globalScope(e.customShows);
}
aspect production nonGlobalEnv_i
top::Env ::= e::Decorated Env
{
  top.customShows = nonGlobalScope(e.customShows);
}
aspect production functionEnv_i
top::Env ::= e::Decorated Env
{
  top.customShows = functionScope(e.customShows);
}

synthesized attribute customShowContribs::Contribs<Name> occurs on Defs, Def;

aspect production nilDefs
top::Defs ::=
{
  top.customShowContribs = [];
}
aspect production consDefs
top::Defs ::= h::Def  t::Defs
{
  top.customShowContribs = h.customShowContribs ++ t.customShowContribs;
}

aspect default production
top::Def ::=
{
  top.customShowContribs = [];
}

abstract production customShowDef
top::Def ::= t::Type  showFunctionName::Name
{
  top.customShowContribs = [(t.withoutTypeQualifiers.mangledName, showFunctionName)];
}

function getCustomShow
Maybe<Name> ::= t::Type  e::Decorated Env
{
  return case lookupScope(t.withoutTypeQualifiers.mangledName, e.customShows) of
  | [] -> nothing()
  | customShow :: _ -> just(customShow)
  end;
}
