-- upstream: docs_src/security/tutorial005_an_py310.py, with its argon2 password hash and
-- its JWT replaced by fakes (`fakehashed` + password; `sub|scope`), in the Python twin
-- (tests/golden/generate.py, `security_005`) as here: the scopes logic is the tutorial's.
import LeanFastapi
open LeanFastapi

namespace Tests.Security005

structure Token where
  access_token : String
  token_type : String
  deriving Model

structure User where
  username : String
  email : Option String := none
  full_name : Option String := none
  disabled : Option Bool := none
  deriving Model

structure UserInDB where
  username : String
  email : Option String := none
  full_name : Option String := none
  disabled : Option Bool := none
  hashed_password : String
  deriving Model

def UserInDB.toUser (u : UserInDB) : User :=
  { username := u.username, email := u.email, full_name := u.full_name, disabled := u.disabled }

def fakeUsersDb : List (String × UserInDB) :=
  [("johndoe", { username := "johndoe", full_name := "John Doe", email := "johndoe@example.com",
                 hashed_password := "fakehashedsecret", disabled := false }),
   ("alice", { username := "alice", full_name := "Alice Chains", email := "alicechains@example.com",
               hashed_password := "fakehashedsecret2", disabled := true })]

def oauth2Scheme := OAuth2PasswordBearer (tokenUrl := "token")
  (scopes := [("me", "Read information about the current user."), ("items", "Read items.")])

def app := FastAPI.new

def verifyPassword (plain hashed : String) : Bool := "fakehashed" ++ plain == hashed

def getUser (db : List (String × UserInDB)) (username : String) : Option UserInDB := db.lookup username

def authenticateUser (db : List (String × UserInDB)) (username password : String) : Option UserInDB := do
  let user ← getUser db username
  if verifyPassword password user.hashed_password then some user else none

/-- The fake token: `sub|scope`. -/
def createAccessToken (sub scope : String) : String := sub ++ "|" ++ scope

def getCurrentUser (security_scopes : SecurityScopes) (token : Depends oauth2Scheme) : Handler UserInDB := do
  let authenticateValue :=
    if security_scopes.scopes.isEmpty then "Bearer" else s!"Bearer scope=\"{security_scopes.scope_str}\""
  let credentialsException :=
    HTTPException 401 "Could not validate credentials" (headers := [("WWW-Authenticate", authenticateValue)])
  let (username, scope) ← match token.splitOn "|" with
    | [u, s] => pure (u, s)
    | _ => throw credentialsException
  let tokenScopes := scope.splitOn " "
  let some user := getUser fakeUsersDb username | throw credentialsException
  for s in security_scopes.scopes do
    unless tokenScopes.contains s do
      throw (HTTPException 401 "Not enough permissions" (headers := [("WWW-Authenticate", authenticateValue)]))
  return user

def getCurrentActiveUser (current_user : Security getCurrentUser ["me"]) : Handler UserInDB := do
  if current_user.disabled == some true then throw (HTTPException 400 "Inactive user")
  return current_user

@[post "/token"]
def loginForAccessToken (form_data : Depends OAuth2PasswordRequestForm) : Handler Token := do
  let some user := authenticateUser fakeUsersDb form_data.username form_data.password
    | throw (HTTPException 400 "Incorrect username or password")
  return { access_token := createAccessToken user.username (" ".intercalate form_data.scopes), token_type := "bearer" }

@[get "/users/me/"]
def readUsersMe (current_user : Depends getCurrentActiveUser) : Handler User :=
  return current_user.toUser

@[get "/users/me/items/"]
def readOwnItems (current_user : Security getCurrentActiveUser ["items"]) : Handler Json :=
  return json% [{"item_id": "Foo", "owner": current_user.username}]

@[get "/status/"]
def readSystemStatus (current_user : Depends getCurrentUser) : Handler Json :=
  return json% {"status": "ok"}

end Tests.Security005
