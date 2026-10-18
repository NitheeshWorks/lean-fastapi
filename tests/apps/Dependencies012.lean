-- upstream: docs_src/dependencies/tutorial012_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Dependencies012

def verifyToken (x_token : Header String) : Handler Unit := do
  if x_token != "fake-super-secret-token" then
    throw (HTTPException 400 "X-Token header invalid")

def verifyKey (x_key : Header String) : Handler String := do
  if x_key != "fake-super-secret-key" then
    throw (HTTPException 400 "X-Key header invalid")
  return x_key

def app := FastAPI.new (dependencies := [Depends verifyToken, Depends verifyKey])

@[get "/items/"]
def readItems : Handler Json :=
  return json% [{"item": "Portal Gun"}, {"item": "Plumbus"}]

@[get "/users/"]
def readUsers : Handler Json :=
  return json% [{"username": "Rick"}, {"username": "Morty"}]

end Tests.Dependencies012
