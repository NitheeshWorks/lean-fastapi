import LeanFastapi
open LeanFastapi

namespace Demo

/-!
# The milestone 1 demo: the application

`lake exe example` serves this application on http://127.0.0.1:8000, the
first steps, path parameters, body, response model and error handling of
the FastAPI tutorial in one file. `tests/golden/generate.py` runs the same
application on fastapi 0.143.3 (`demo` there).
-/

def app := FastAPI.new

@[get "/"]
def root : Handler Json :=
  return json% {"message": "Hello World"}

@[get "/items/{item_id}"]
def readItem (item_id : Int) (q : Option String := none) : Handler Json :=
  return json% {"item_id": item_id, "q": q}

structure Item where
  name        : String ∣ maxLength 50
  description : Option String := none
  price       : Decimal ∣ gt 0
  tax         : Option Decimal := none
  deriving Model

@[put "/items/{item_id}" (response_model := Item)]
def updateItem (item_id : Int) (item : Item) : Handler Item :=
  return item

def stock : List (String × String) := [("foo", "The Foo Wrestlers")]

@[get "/stock/{item_id}"]
def readStock (item_id : String) : Handler Json := do
  match stock.lookup item_id with
  | some item => return json% {"item": item}
  | none => throw (HTTPException 404 "Item not found")

end Demo
