-- upstream: docs_src/dependencies/tutorial001_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Dependencies001

def app := FastAPI.new

def commonParameters (q : Option String := none) (skip : Int := 0) (limit : Int := 100) : Handler Json :=
  return json% {"q": q, "skip": skip, "limit": limit}

@[get "/items/"]
def readItems (commons : Depends commonParameters) : Handler Json :=
  return commons

@[get "/users/"]
def readUsers (commons : Depends commonParameters) : Handler Json :=
  return commons

end Tests.Dependencies001
