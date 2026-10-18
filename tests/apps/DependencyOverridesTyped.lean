-- upstream: tests/test_dependency_overrides.py (overrides of dependencies whose value has
-- no JSON form, a database session in practice; and an override's own dependencies
-- overridden in turn, as `solve_dependencies` does). Python twin: `typed_overrides_app`
-- in tests/golden/generate.py.
import LeanFastapi
open LeanFastapi

namespace Tests.DependencyOverridesTyped

/-- A value without a JSON form. -/
structure Db where
  name : String

def getDb : Db := ⟨"prod"⟩
def getTestDb : Db := ⟨"test"⟩

def nameDep : String := "orig"
def getUser : String := "alice"
def getBob : String := "bob"
def getName (user : Depends getUser) : String := "override:" ++ user

def app := FastAPI.new

@[get "/db"]
def readDb (db : Depends getDb) : Handler Json :=
  return json% {"db": db.name}

@[get "/name"]
def readName (n : Depends nameDep) : Handler Json :=
  return json% {"name": n}

/-- `app.dependency_overrides` with all three overrides. -/
def appOverridden : FastAPI :=
  app |>.overrideDependency (Depends getDb) (Depends getTestDb)
    |>.overrideDependency (Depends nameDep) (Depends getName)
    |>.overrideDependency (Depends getUser) (Depends getBob)

-- An override of another value type does not compile.
/--
error: Application type mismatch: The argument
  Dependency.declared getName String true "" [] { call := "Tests.DependencyOverridesTyped.getName" }
has type
  Dependency String
but is expected to have type
  Dependency Db
in the application
  app.overrideDependency (Dependency.declared getDb Db true "" [] { call := "Tests.DependencyOverridesTyped.getDb" })
    (Dependency.declared getName String true "" [] { call := "Tests.DependencyOverridesTyped.getName" })
-/
#guard_msgs in
example : FastAPI := app.overrideDependency (Depends getDb) (Depends getName)

end Tests.DependencyOverridesTyped
