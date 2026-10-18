-- upstream: docs_src/security/tutorial001_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Security001

def app := FastAPI.new

def oauth2Scheme := OAuth2PasswordBearer (tokenUrl := "token")

@[get "/items/"]
def readItems (token : Depends oauth2Scheme) : Handler Json :=
  return json% {"token": token}

end Tests.Security001
