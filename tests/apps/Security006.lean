-- upstream: docs_src/security/tutorial006_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Security006

def app := FastAPI.new

def security := HTTPBasic

@[get "/users/me"]
def readCurrentUser (credentials : Depends security) : Handler Json :=
  return json% {"username": credentials.username, "password": credentials.password}

end Tests.Security006
