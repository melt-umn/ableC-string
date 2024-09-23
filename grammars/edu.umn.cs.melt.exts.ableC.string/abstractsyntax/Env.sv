grammar edu:umn:cs:melt:exts:ableC:string:abstractsyntax;

-- Track any custom show implementation's names.
synthesized attribute customShows::Scopes<(Name, Name)> occurs on Env;

aspect production emptyEnv
top::Env ::=
{
  top.customShows = emptyScope();
}
aspect production addDefsEnv
top::Env ::= d::Defs  e::Env
{
  top.customShows = addGlobalScope(gd.customShowContribs, addScope(d.customShowContribs, e.customShows));
}
aspect production openScopeEnv
top::Env ::= e::Env
{
  top.customShows = openScope(e.customShows);
}
aspect production globalEnv
top::Env ::= e::Env
{
  top.customShows = globalScope(e.customShows);
}
aspect production nonGlobalEnv
top::Env ::= e::Env
{
  top.customShows = nonGlobalScope(e.customShows);
}
aspect production functionEnv
top::Env ::= e::Env
{
  top.customShows = functionScope(e.customShows);
}

synthesized attribute customShowContribs::Contribs<(Name, Name)> occurs on Defs, Def;

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
top::Def ::= t::Type  showLenFunctionName::Name  showFunctionName::Name
{
  top.customShowContribs = [(t.withoutTypeQualifiers.mangledName, ^showLenFunctionName, ^showFunctionName)];
}

function getCustomShow
Maybe<(Name, Name)> ::= t::Type  e::Env
{
  return case lookupScope(t.withoutTypeQualifiers.mangledName, e.customShows) of
  | [] -> nothing()
  | customShow :: _ -> just(customShow)
  end;
}
