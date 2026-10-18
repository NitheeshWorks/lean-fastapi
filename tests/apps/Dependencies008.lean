-- upstream: docs_src/dependencies/tutorial008_py310.py, run as
-- tests/test_tutorial/test_dependencies/test_tutorial008.py runs it (`read_root` reading
-- `dependency_c`), with fakes in place of the Mocks the test patches in for
-- `generate_dep_a`, `generate_dep_b` and `generate_dep_c`: each has a name and logs its
-- `close`. Python twin: `dependencies_008` in tests/golden/generate.py.
import LeanFastapi
open LeanFastapi

namespace Tests.Dependencies008

initialize log : IO.Ref (List String) ← IO.mkRef []

/-- A fake resource (no JSON form). -/
structure Dep where
  name : String

def Dep.close (d : Dep) (after : List Dep := []) : Handler Unit :=
  log.modify (· ++ [s!"close {d.name}" ++ String.join (after.map (s!" after {·.name}"))])

def generateDepA : Dep := ⟨"a"⟩
def generateDepB : Dep := ⟨"b"⟩
def generateDepC : Dep := ⟨"c"⟩

def dependencyA : Yield Dep := do
  let depA := generateDepA
  yieldFinally depA depA.close

def dependencyB (dep_a : Depends dependencyA) : Yield Dep := do
  let depB := generateDepB
  yieldFinally depB (depB.close [dep_a])

def dependencyC (dep_b : Depends dependencyB) : Yield Dep := do
  let depC := generateDepC
  yieldFinally depC (depC.close [dep_b])

def app := FastAPI.new

@[get "/"]
def readRoot (c : Depends dependencyC) : Handler Json :=
  return json% {"c": c.name}

@[get "/events"]
def getEvents : Handler Json := do
  let out ← log.get
  log.set []
  return LeanJson.intoJson out

end Tests.Dependencies008
