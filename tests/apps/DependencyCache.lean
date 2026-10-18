-- upstream: tests/test_dependency_cache.py
import LeanFastapi
open LeanFastapi

namespace Tests.DependencyCache

def app := FastAPI.new

initialize counterHolder : IO.Ref Nat ← IO.mkRef 0

def depCounter : Handler Nat := do
  counterHolder.modify (· + 1)
  counterHolder.get

def superDep (count : Depends depCounter) : Nat := count

@[get "/counter/"]
def getCounter (count : Depends depCounter) : Handler Json :=
  return json% {"counter": count}

@[get "/sub-counter/"]
def getSubCounter (subcount : Depends superDep) (count : Depends depCounter) : Handler Json :=
  return json% {"counter": count, "subcounter": subcount}

@[get "/sub-counter-no-cache/"]
def getSubCounterNoCache (subcount : Depends superDep) (count : Depends depCounter (use_cache := false)) :
    Handler Json :=
  return json% {"counter": count, "subcounter": subcount}

@[get "/scope-counter"]
def getScopeCounter (count : Security depCounter) (scope_count_1 : Security depCounter ["scope"])
    (scope_count_2 : Security depCounter ["scope"]) : Handler Json :=
  return json% {"counter": count, "scope_counter_1": scope_count_1, "scope_counter_2": scope_count_2}

-- `counter_holder["counter"] = 0`, as each upstream test starts (the Python app gets the
-- same route in tests/golden/generate.py).
@[post "/reset" (include_in_schema := false)]
def reset : Handler Json := do
  counterHolder.set 0
  return json% null

end Tests.DependencyCache
