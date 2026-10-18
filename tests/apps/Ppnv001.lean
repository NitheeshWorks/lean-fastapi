-- upstream: docs_src/path_params_numeric_validations/tutorial001_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Ppnv001

def app := FastAPI.new

@[get "/items/{item_id}"]
def readItems (item_id : Path Int (title := "The ID of the item to get"))
    (q : Query (Option String) (alias := "item-query") := none) : Handler Json := do
  let results := [("item_id", json% item_id)]
  match q with
  | some q => if q.isEmpty then return jobj results else return jobj (results ++ [("q", .str q)])
  | none => return jobj results

end Tests.Ppnv001
