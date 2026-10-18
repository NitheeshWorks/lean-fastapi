-- upstream: docs_src/security/tutorial004_an_py310.py, with its argon2 password hash and
-- its JWT replaced by fakes (`fakehashed` + password; the token a payload of `key=value`
-- pairs joined by `&`, `sub=<username>` when issued), in the Python twin
-- (tests/golden/generate.py, `security_004`) as here. Alice, whom
-- test_token_inactive_user patches into the database, is in it throughout.
import LeanFastapi
open LeanFastapi

namespace Tests.Security004

structure Token where
  access_token : String
  token_type : String
  deriving Model

structure TokenData where
  username : Option String := none
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
   ("alice", { username := "alice", full_name := "Alice Wonderson", email := "alice@example.com",
               hashed_password := "fakehashedsecretalice", disabled := true })]

def oauth2Scheme := OAuth2PasswordBearer (tokenUrl := "token")

def app := FastAPI.new

def verifyPassword (plain hashed : String) : Bool := "fakehashed" ++ plain == hashed

def getUser (db : List (String × UserInDB)) (username : String) : Option UserInDB := db.lookup username

def authenticateUser (db : List (String × UserInDB)) (username password : String) : Option UserInDB := do
  let user ← getUser db username
  if verifyPassword password user.hashed_password then some user else none

/-- The fake token for a payload. -/
def createAccessToken (data : List (String × String)) : String :=
  "&".intercalate (data.map fun (k, v) => k ++ "=" ++ v)

/-- The fake decoder: `none` (`InvalidTokenError`) unless every part is `key=value`. -/
def decode (token : String) : Option (List (String × String)) :=
  (token.splitOn "&").mapM fun part =>
    match part.splitOn "=" with
    | k :: v :: rest => some (k, "=".intercalate (v :: rest))
    | _ => none

def getCurrentUser (token : Depends oauth2Scheme) : Handler UserInDB := do
  let credentialsException :=
    HTTPException 401 "Could not validate credentials" (headers := [("WWW-Authenticate", "Bearer")])
  let some payload := decode token | throw credentialsException
  let some username := payload.lookup "sub" | throw credentialsException
  let tokenData : TokenData := { username }
  let some user := tokenData.username.bind (getUser fakeUsersDb) | throw credentialsException
  return user

def getCurrentActiveUser (current_user : Depends getCurrentUser) : Handler UserInDB := do
  if current_user.disabled == some true then throw (HTTPException 400 "Inactive user")
  return current_user

@[post "/token"]
def loginForAccessToken (form_data : Depends OAuth2PasswordRequestForm) : Handler Token := do
  let some user := authenticateUser fakeUsersDb form_data.username form_data.password
    | throw (HTTPException 401 "Incorrect username or password" (headers := [("WWW-Authenticate", "Bearer")]))
  return { access_token := createAccessToken [("sub", user.username)], token_type := "bearer" }

@[get "/users/me/"]
def readUsersMe (current_user : Depends getCurrentActiveUser) : Handler User :=
  return current_user.toUser

@[get "/users/me/items/"]
def readOwnItems (current_user : Depends getCurrentActiveUser) : Handler Json :=
  return json% [{"item_id": "Foo", "owner": current_user.username}]

end Tests.Security004
