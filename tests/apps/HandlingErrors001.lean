-- upstream: docs_src/handling_errors/tutorial001_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.HandlingErrors001

def app := FastAPI.new

def items : List (String × String) := [("foo", "The Foo Wrestlers")]

@[get "/items/{item_id}"]
def readItem (item_id : String) : Handler Json := do
  match items.lookup item_id with
  | some item => return json% {"item": item}
  | none => throw (HTTPException 404 "Item not found")

end Tests.HandlingErrors001
