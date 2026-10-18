-- upstream: tests/test_security_api_key_cookie.py
import LeanFastapi
open LeanFastapi

namespace Tests.SecurityApiKeyCookie

structure User where
  username : String
  deriving Model

def app := FastAPI.new

def apiKey := APIKeyCookie (name := "key")

def getCurrentUser (oauth_header : Security apiKey) : User := { username := oauth_header }

@[get "/users/me"]
def readCurrentUser (current_user : Depends getCurrentUser) : Handler Json := return LeanPydantic.toJson {} current_user

end Tests.SecurityApiKeyCookie
