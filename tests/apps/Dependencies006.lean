-- upstream: docs_src/dependencies/tutorial006_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Dependencies006

def app := FastAPI.new

def verifyToken (x_token : Header String) : Handler Unit := do
  if x_token != "fake-super-secret-token" then
    throw (HTTPException 400 "X-Token header invalid")

def verifyKey (x_key : Header String) : Handler String := do
  if x_key != "fake-super-secret-key" then
    throw (HTTPException 400 "X-Key header invalid")
  return x_key

@[get "/items/" (dependencies := [Depends verifyToken, Depends verifyKey])]
def readItems : Handler Json :=
  return json% [{"item": "Foo"}, {"item": "Bar"}]

end Tests.Dependencies006
