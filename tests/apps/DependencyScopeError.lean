-- upstream: tests/test_dependency_yield_scope.py::test_broken_scope
import LeanFastapi
open LeanFastapi

namespace Tests.DependencyScopeError

def app := FastAPI.new

def getSession : Yield String := yieldWith "session" fun _ => pure ()

def getNamedFuncSession (session : Depends getSession (scope := "function")) : Yield String :=
  yieldWith session fun _ => pure ()

-- FastAPI raises DependencyScopeError when the route is declared; here the
-- route does not elaborate.
/--
error: The dependency "getNamedFuncSession" has a scope of "request", it cannot depend on dependencies with scope "function".
-/
#guard_msgs in
@[get "/broken-scope"]
def getBroken (sessions : Depends getNamedFuncSession) : Handler String :=
  return sessions

end Tests.DependencyScopeError
