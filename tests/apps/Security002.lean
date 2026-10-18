-- upstream: docs_src/security/tutorial002_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Security002

def app := FastAPI.new

def oauth2Scheme := OAuth2PasswordBearer (tokenUrl := "token")

structure User where
  username : String
  email : Option String := none
  full_name : Option String := none
  disabled : Option Bool := none
  deriving Model

def fakeDecodeToken (token : String) : User :=
  { username := token ++ "fakedecoded", email := "john@example.com", full_name := "John Doe" }

def getCurrentUser (token : Depends oauth2Scheme) : Handler User :=
  return fakeDecodeToken token

@[get "/users/me" (response_model := none)]
def readUsersMe (current_user : Depends getCurrentUser) : Handler User :=
  return current_user

end Tests.Security002
