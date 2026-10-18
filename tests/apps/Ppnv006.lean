-- upstream: docs_src/path_params_numeric_validations/tutorial006_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Ppnv006

def app := FastAPI.new

@[get "/items/{item_id}"]
def readItems (item_id : Path (Int ∣ ge 0 ∧ le 1000) (title := "The ID of the item to get")) (q : String)
    (size : Float ∣ gt 0 ∧ lt 10.5) : Handler Json := do
  let mut results := [("item_id", json% item_id.val)]
  unless q.isEmpty do results := results ++ [("q", .str q)]
  unless size.val == 0 do results := results ++ [("size", json% size.val)]
  return jobj results

end Tests.Ppnv006
