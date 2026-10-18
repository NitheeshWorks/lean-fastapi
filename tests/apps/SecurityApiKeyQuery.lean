-- upstream: tests/test_security_api_key_query.py
import LeanFastapi
open LeanFastapi

namespace Tests.SecurityApiKeyQuery

structure User where
  username : String
  deriving Model

def app := FastAPI.new

def apiKey := APIKeyQuery (name := "key")

def getCurrentUser (oauth_header : Security apiKey) : User := { username := oauth_header }

@[get "/users/me"]
def readCurrentUser (current_user : Depends getCurrentUser) : Handler Json := return LeanPydantic.toJson {} current_user

end Tests.SecurityApiKeyQuery
