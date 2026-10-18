-- upstream: tests/test_dependency_overrides.py (the app without its APIRouter, which
-- arrives with routers)
import LeanFastapi
open LeanFastapi

namespace Tests.DependencyOverrides

def app := FastAPI.new

def commonParameters (q : String) (skip : Int := 0) (limit : Int := 100) : Handler Json :=
  return json% {"q": q, "skip": skip, "limit": limit}

@[get "/main-depends/"]
def mainDepends (commons : Depends commonParameters) : Handler Json :=
  return json% {"in": "main-depends", "params": commons}

@[get "/decorator-depends/" (dependencies := [Depends commonParameters])]
def decoratorDepends : Handler Json :=
  return json% {"in": "decorator-depends"}

def overriderDependencySimple (q : Option String := none) : Handler Json :=
  return json% {"q": q, "skip": 5, "limit": 10}

def overriderSubDependency (k : String) : Handler Json :=
  return json% {"k": k}

def overriderDependencyWithSub (msg : Depends overriderSubDependency) : Handler Json :=
  return msg

/-- `app.dependency_overrides[common_parameters] = overrider_dependency_simple`. -/
def appSimple : FastAPI := app.overrideDependency (Depends commonParameters) (Depends overriderDependencySimple)

/-- `app.dependency_overrides[common_parameters] = overrider_dependency_with_sub`. -/
def appWithSub : FastAPI := app.overrideDependency (Depends commonParameters) (Depends overriderDependencyWithSub)

end Tests.DependencyOverrides
