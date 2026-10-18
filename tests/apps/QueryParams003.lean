-- upstream: docs_src/query_params/tutorial003_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.QueryParams003

def app := FastAPI.new

@[get "/items/{item_id}"]
def readItem (item_id : String) (q : Option String := none) (short : Bool := false) : Handler Json := do
  let mut item : List (String × Json) := [("item_id", .str item_id)]
  if let some q := q then
    unless q.isEmpty do item := item ++ [("q", .str q)]
  if !short then
    item := item ++ [("description", .str "This is an amazing item that has a long description")]
  return jobj item

end Tests.QueryParams003
