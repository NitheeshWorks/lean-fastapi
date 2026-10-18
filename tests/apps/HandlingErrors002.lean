-- upstream: docs_src/handling_errors/tutorial002_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.HandlingErrors002

def app := FastAPI.new

def items : List (String × String) := [("foo", "The Foo Wrestlers")]

@[get "/items-header/{item_id}"]
def readItemHeader (item_id : String) : Handler Json := do
  match items.lookup item_id with
  | some item => return json% {"item": item}
  | none => throw (HTTPException 404 "Item not found" (headers := [("X-Error", "There goes my error")]))

end Tests.HandlingErrors002
