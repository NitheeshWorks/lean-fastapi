-- upstream: docs_src/dependencies/tutorial007_py310.py, run as
-- tests/test_tutorial/test_dependencies/test_tutorial007.py runs it: the tutorial leaves
-- `DBSession` undefined and the test patches in a Mock; here (and in the Python twin,
-- `dependencies_007` in tests/golden/generate.py) a fake whose `close` is logged, read by
-- an app as test_tutorial008.py and test_tutorial010.py do.
import LeanFastapi
open LeanFastapi

namespace Tests.Dependencies007

initialize log : IO.Ref (List String) ← IO.mkRef []

/-- The fake session (no JSON form). -/
structure DBSession where
  name : String := "db"

def DBSession.close (db : DBSession) : Handler Unit := log.modify (· ++ [s!"close {db.name}"])

def getDb : Yield DBSession := do
  let db : DBSession := {}
  yieldFinally db db.close

def app := FastAPI.new

@[get "/"]
def readRoot (c : Depends getDb) : Handler Json :=
  return json% {"c": c.name}

@[get "/events"]
def getEvents : Handler Json := do
  let out ← log.get
  log.set []
  return LeanJson.intoJson out

end Tests.Dependencies007
