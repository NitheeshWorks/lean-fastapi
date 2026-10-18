-- upstream: docs_src/query_params_str_validations/tutorial003_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Qpsv003

def app := FastAPI.new

@[get "/items/"]
def readItems (q : Option (String ∣ minLength 3 ∧ maxLength 50) := none) : Handler Json := do
  let results := [("items", (json% [{"item_id": "Foo"}, {"item_id": "Bar"}] : Json))]
  match q with
  | some q => if q.val.isEmpty then return jobj results else return jobj (results ++ [("q", .str q.val)])
  | none => return jobj results

end Tests.Qpsv003
