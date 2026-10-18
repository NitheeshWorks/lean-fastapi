-- upstream: tests/test_security_http_digest.py
import LeanFastapi
open LeanFastapi

namespace Tests.SecurityHttpDigest

structure User where
  username : String
  deriving Model

def app := FastAPI.new

def security := HTTPDigest

@[get "/users/me"]
def readCurrentUser (credentials : Security security) : Handler Json :=
  return json% {"scheme": credentials.scheme, "credentials": credentials.credentials}

end Tests.SecurityHttpDigest
