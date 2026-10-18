-- upstream: docs_src/security/tutorial007_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Security007

def app := FastAPI.new

def security := HTTPBasic

def getCurrentUsername (credentials : Depends security) : Handler String := do
  -- `secrets.compare_digest` compares in constant time; equality is what it decides
  let isCorrectUsername := credentials.username == "stanleyjobson"
  let isCorrectPassword := credentials.password == "swordfish"
  unless isCorrectUsername && isCorrectPassword do
    throw (HTTPException 401 "Incorrect username or password" (headers := [("WWW-Authenticate", "Basic")]))
  return credentials.username

@[get "/users/me"]
def readCurrentUser (username : Depends getCurrentUsername) : Handler Json :=
  return json% {"username": username}

end Tests.Security007
