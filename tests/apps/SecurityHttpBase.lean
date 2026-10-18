-- upstream: tests/test_security_http_base.py
import LeanFastapi
open LeanFastapi

namespace Tests.SecurityHttpBase

structure User where
  username : String
  deriving Model

def app := FastAPI.new

def security := HTTPBase (scheme := "Other")

@[get "/users/me"]
def readCurrentUser (credentials : Security security) : Handler Json :=
  return json% {"scheme": credentials.scheme, "credentials": credentials.credentials}

end Tests.SecurityHttpBase
