-- upstream: tests/test_dependency_yield_scope.py and test_dependency_contextmanager.py (the
-- order exits run in: function-scoped after the function, request-scoped after the
-- response, most recent first; an exception reaches every exit), as a fixture of its own:
-- its Python twin is `deps_yield` in tests/golden/generate.py.
import LeanFastapi
open LeanFastapi

namespace Tests.DependencyYield

def app := FastAPI.new

initialize events : IO.Ref (List String) ← IO.mkRef []

def log (s : String) : IO Unit := events.modify (· ++ [s])

def exitLogging (name : String) : Exit
  | some e => do log s!"{name} exit error"; throw e
  | none => log s!"{name} exit ok"

def depA : Yield String := do
  log "a enter"
  yieldWith "a" (exitLogging "a")

def depB (a : Depends depA) : Yield String := do
  log "b enter"
  yieldWith (a ++ "b") (exitLogging "b")

def depF : Yield String := do
  log "f enter"
  yieldWith "f" (exitLogging "f")

@[get "/run"]
def run (b : Depends depB) (f : Depends depF (scope := "function")) : Handler Json := do
  log "endpoint"
  return json% {"b": b, "f": f}

@[get "/fail"]
def fail (b : Depends depB) (f : Depends depF (scope := "function")) : Handler Json := do
  log s!"endpoint {b} {f}"
  throw (HTTPException 418 "teapot")

@[get "/invalid"]
def invalid (b : Depends depB) (n : Int) : Handler Json := do
  log s!"endpoint {b} {n}"
  return json% {"n": n}

-- The events since the last read.
@[get "/events"]
def getEvents : Handler Json := do
  let es ← events.get
  events.set []
  return json% es

end Tests.DependencyYield
