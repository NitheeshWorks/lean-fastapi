-- upstream: docs_src/query_params/tutorial001_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.QueryParams001

def app := FastAPI.new

def fakeItemsDb : List Json := [json% {"item_name": "Foo"}, json% {"item_name": "Bar"}, json% {"item_name": "Baz"}]

/-- Python's `xs[start:stop]` for a non-negative `start`. -/
def slice (xs : List Json) (start stop : Int) : List Json :=
  (xs.drop start.toNat).take (stop - start).toNat

@[get "/items/"]
def readItem (skip : Int := 0) (limit : Int := 10) : Handler Json :=
  return jarr (slice fakeItemsDb skip (skip + limit))

end Tests.QueryParams001
