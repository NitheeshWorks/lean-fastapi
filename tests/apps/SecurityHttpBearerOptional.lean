-- upstream: tests/test_security_http_bearer_optional.py
import LeanFastapi
open LeanFastapi

namespace Tests.SecurityHttpBearerOptional

structure User where
  username : String
  deriving Model

def app := FastAPI.new

def security := HTTPBearer (auto_error := false)

@[get "/users/me"]
def readCurrentUser (credentials : Security security) : Handler Json :=
  match credentials with
  | none => return json% {"msg": "Create an account first"}
  | some c => return json% {"scheme": c.scheme, "credentials": c.credentials}

end Tests.SecurityHttpBearerOptional
