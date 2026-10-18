-- upstream: tests/test_security_openid_connect_optional.py
import LeanFastapi
open LeanFastapi

namespace Tests.SecurityOpenIdConnectOptional

structure User where
  username : String
  deriving Model

def app := FastAPI.new

def oid := OpenIdConnect (openIdConnectUrl := "/openid") (auto_error := false)

def getCurrentUser (oauth_header : Security oid) : Option User :=
  oauth_header.map fun h => { username := h }

@[get "/users/me"]
def readCurrentUser (current_user : Depends getCurrentUser) : Handler Json :=
  match current_user with
  | none => return json% {"msg": "Create an account first"}
  | some u => return LeanPydantic.toJson {} u

end Tests.SecurityOpenIdConnectOptional
