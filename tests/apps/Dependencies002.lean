-- upstream: docs_src/dependencies/tutorial002_an_py310.py (and tutorial003, tutorial004:
-- `Depends(CommonQueryParams)` and `Depends()` are both `Depends CommonQueryParams`)
import LeanFastapi
open LeanFastapi

namespace Tests.Dependencies002

def app := FastAPI.new

def fakeItemsDb : List Json := [json% {"item_name": "Foo"}, json% {"item_name": "Bar"}, json% {"item_name": "Baz"}]

structure CommonQueryParams where
  q : Option String := none
  skip : Int := 0
  limit : Int := 100

/-- Python's `xs[start:stop]` for a non-negative `start`. -/
def slice (xs : List Json) (start stop : Int) : List Json :=
  (xs.drop start.toNat).take (stop - start).toNat

@[get "/items/"]
def readItems (commons : Depends CommonQueryParams) : Handler Json := do
  let items := jarr (slice fakeItemsDb commons.skip (commons.skip + commons.limit))
  match commons.q with
  | some q => if q.isEmpty then return json% {"items": items} else return json% {"q": q, "items": items}
  | none => return json% {"items": items}

end Tests.Dependencies002
