-- upstream: tests/test_security_api_key_header_optional.py
import LeanFastapi
open LeanFastapi

namespace Tests.SecurityApiKeyHeaderOptional

structure User where
  username : String
  deriving Model

def app := FastAPI.new

def apiKey := APIKeyHeader (name := "key") (auto_error := false)

def getCurrentUser (oauth_header : Security apiKey) : Option User :=
  oauth_header.map fun h => { username := h }

@[get "/users/me"]
def readCurrentUser (current_user : Depends getCurrentUser) : Handler Json :=
  match current_user with
  | none => return json% {"msg": "Create an account first"}
  | some u => return LeanPydantic.toJson {} u

end Tests.SecurityApiKeyHeaderOptional
