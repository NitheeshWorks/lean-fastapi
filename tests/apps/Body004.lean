-- upstream: docs_src/body/tutorial004_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Body004

structure Item where
  name : String
  description : Option String := none
  price : Float
  tax : Option Float := none
  deriving Model

def app := FastAPI.new

@[put "/items/{item_id}"]
def updateItem (item_id : Int) (item : Item) (q : Option String := none) : Handler Json := do
  let fields := (jfields? (LeanPydantic.toJson {} item)).getD []
  let result := [("item_id", json% item_id)] ++ fields
  match q with
  | some q => if q.isEmpty then return jobj result else return jobj (result ++ [("q", .str q)])
  | none => return jobj result

end Tests.Body004
