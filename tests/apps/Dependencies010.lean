-- upstream: docs_src/dependencies/tutorial010_py310.py, run as
-- tests/test_tutorial/test_dependencies/test_tutorial010.py runs it, with a fake in place
-- of the patched `DBSession` Mock (its `close` logged). The context manager's
-- `__enter__`/`__exit__` around the `yield` is `yieldFinally`. Python twin:
-- `dependencies_010` in tests/golden/generate.py.
import LeanFastapi
open LeanFastapi

namespace Tests.Dependencies010

initialize log : IO.Ref (List String) ← IO.mkRef []

/-- The fake session (no JSON form). -/
structure DBSession where
  name : String := "db"

def DBSession.close (db : DBSession) : Handler Unit := log.modify (· ++ [s!"close {db.name}"])

/-- `MySuperContextManager`: `__enter__` gives the session, `__exit__` closes it. -/
structure MySuperContextManager where
  db : DBSession := {}

def MySuperContextManager.enter (cm : MySuperContextManager) : DBSession := cm.db
def MySuperContextManager.exit (cm : MySuperContextManager) : Handler Unit := cm.db.close

def getDb : Yield DBSession := do
  let cm : MySuperContextManager := {}
  yieldFinally cm.enter cm.exit

def app := FastAPI.new

@[get "/"]
def readRoot (c : Depends getDb) : Handler Json :=
  return json% {"c": c.name}

@[get "/events"]
def getEvents : Handler Json := do
  let out ← log.get
  log.set []
  return LeanJson.intoJson out

end Tests.Dependencies010
