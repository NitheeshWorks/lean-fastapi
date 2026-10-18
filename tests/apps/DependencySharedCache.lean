-- upstream: tests/test_dependency_cache.py (one cache per request, here between an
-- application's `dependencies` and the route's own). Python twin: `shared_cache_app` in
-- tests/golden/generate.py.
import LeanFastapi
open LeanFastapi

namespace Tests.DependencySharedCache

initialize callsHolder : IO.Ref Nat ← IO.mkRef 0

def countCall : Handler Nat := do
  callsHolder.modify (· + 1)
  callsHolder.get

def app := FastAPI.new (dependencies := [Depends countCall])

@[get "/count"]
def readCount (n : Depends countCall) : Handler Json := do
  let calls ← callsHolder.get
  return json% {"count": n, "calls": calls}

@[post "/reset" (include_in_schema := false)]
def resetCalls : Handler Json := do
  callsHolder.set 0
  return json% null

end Tests.DependencySharedCache
