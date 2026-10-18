-- upstream: docs_src/security/tutorial003_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Security003

structure UserInDB where
  username : String
  email : Option String := none
  full_name : Option String := none
  disabled : Option Bool := none
  hashed_password : String
  deriving Model

def fakeUsersDb : List (String × UserInDB) :=
  [("johndoe", { username := "johndoe", full_name := "John Doe", email := "johndoe@example.com",
                 hashed_password := "fakehashedsecret", disabled := false }),
   ("alice", { username := "alice", full_name := "Alice Wonderson", email := "alice@example.com",
               hashed_password := "fakehashedsecret2", disabled := true })]

def app := FastAPI.new

def fakeHashPassword (password : String) : String := "fakehashed" ++ password

def oauth2Scheme := OAuth2PasswordBearer (tokenUrl := "token")

structure User where
  username : String
  email : Option String := none
  full_name : Option String := none
  disabled : Option Bool := none
  deriving Model

def UserInDB.toUser (u : UserInDB) : User :=
  { username := u.username, email := u.email, full_name := u.full_name, disabled := u.disabled }

def getUser (db : List (String × UserInDB)) (username : String) : Option UserInDB := db.lookup username

def fakeDecodeToken (token : String) : Option UserInDB :=
  -- This doesn't provide any security at all
  getUser fakeUsersDb token

def getCurrentUser (token : Depends oauth2Scheme) : Handler UserInDB := do
  let some user := fakeDecodeToken token
    | throw (HTTPException 401 "Not authenticated" (headers := [("WWW-Authenticate", "Bearer")]))
  return user

def getCurrentActiveUser (current_user : Depends getCurrentUser) : Handler UserInDB := do
  if current_user.disabled == some true then throw (HTTPException 400 "Inactive user")
  return current_user

@[post "/token"]
def login (form_data : Depends OAuth2PasswordRequestForm) : Handler Json := do
  let some user := fakeUsersDb.lookup form_data.username
    | throw (HTTPException 400 "Incorrect username or password")
  if fakeHashPassword form_data.password != user.hashed_password then
    throw (HTTPException 400 "Incorrect username or password")
  return json% {"access_token": user.username, "token_type": "bearer"}

-- Python returns the `UserInDB` itself: with no response model it is sent
-- whole, `hashed_password` included.
@[get "/users/me"]
def readUsersMe (current_user : Depends getCurrentActiveUser) : Handler Json :=
  return LeanPydantic.toJson {} current_user

end Tests.Security003
