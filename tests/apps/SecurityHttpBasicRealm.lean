-- upstream: tests/test_security_http_basic_realm.py
import LeanFastapi
open LeanFastapi

namespace Tests.SecurityHttpBasicRealm

structure User where
  username : String
  deriving Model

def app := FastAPI.new

def security := HTTPBasic (realm := "simple")

@[get "/users/me"]
def readCurrentUser (credentials : Security security) : Handler Json :=
  return json% {"username": credentials.username, "password": credentials.password}

end Tests.SecurityHttpBasicRealm
