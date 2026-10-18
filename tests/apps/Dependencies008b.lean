-- upstream: docs_src/dependencies/tutorial008b_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Dependencies008b

def app := FastAPI.new

def data : List (String × Json) :=
  [("plumbus", json% {"description": "Freshly pickled plumbus", "owner": "Morty"}),
   ("portal-gun", json% {"description": "Gun to create portals", "owner": "Rick"})]

/-- `class OwnerError(Exception)`. -/
def OwnerError (msg : String) : Exception := .custom "OwnerError" msg .null

def getUsername : Yield String :=
  yieldWith "Rick" fun
    | some (.custom "OwnerError" e _) => throw (HTTPException 400 s!"Owner error: {e}")
    | some e => throw e
    | none => pure ()

@[get "/items/{item_id}"]
def getItem (item_id : String) (username : Depends getUsername) : Handler Json := do
  let some item := data.lookup item_id | throw (HTTPException 404 "Item not found")
  if (jfields? item).bind (·.lookup "owner") != some (.str username) then
    throw (OwnerError username)
  return item

end Tests.Dependencies008b
