-- upstream: docs_src/dependencies/tutorial008c_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Dependencies008c

def app := FastAPI.new

/-- `class InternalError(Exception)`. -/
def InternalError (msg : String) : Exception := .custom "InternalError" msg .null

def getUsername : Yield String :=
  yieldWith "Rick" fun
    | some (.custom "InternalError" _ _) => IO.println "Oops, we didn't raise again, Britney 😱"
    | some e => throw e
    | none => pure ()

@[get "/items/{item_id}" (response_model := none)]
def getItem (item_id : String) (username : Depends getUsername) : Handler String := do
  if item_id == "portal-gun" then
    throw (InternalError s!"The portal gun is too dangerous to be owned by {username}")
  if item_id != "plumbus" then
    throw (HTTPException 404 "Item not found, there's only a plumbus here")
  return item_id

end Tests.Dependencies008c
