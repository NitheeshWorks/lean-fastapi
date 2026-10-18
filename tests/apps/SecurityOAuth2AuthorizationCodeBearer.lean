-- upstream: tests/test_security_oauth2_authorization_code_bearer.py
import LeanFastapi
open LeanFastapi

namespace Tests.SecurityOAuth2AuthorizationCodeBearer

def app := FastAPI.new

def oauth2Scheme := OAuth2AuthorizationCodeBearer (authorizationUrl := "authorize") (tokenUrl := "token")
  (auto_error := true)

@[get "/items/"]
def readItems (token : Security oauth2Scheme) : Handler Json :=
  return json% {"token": token}

end Tests.SecurityOAuth2AuthorizationCodeBearer
