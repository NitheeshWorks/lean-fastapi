import LeanFastapi.RepoImpl.Dependencies
import LeanFastapi.RepoImpl.Body

/-!
# RepoImpl: security schemes

`fastapi.security`: each scheme is a value whose `call` reads the request,
used as a dependency (`Depends security`), and which describes itself to
OpenAPI (`SecurityBase`).

* `APIKeyQuery`, `APIKeyHeader`, `APIKeyCookie`: the key from the query, a
  header or a cookie (`apiKeyValue`), as a parameter of that location would
  be read;
* `HTTPBasic`: `Authorization: Basic <base64(user:password)>`, decoded as
  Python's `base64.b64decode` does (`b64decode`, non-validating: characters
  outside the alphabet are skipped, padding ends the data);
* `HTTPBearer`, `HTTPDigest`: the scheme and credentials of the
  `Authorization` header (`authorizationSchemeParam`, Python's
  `get_authorization_scheme_param`);
* `OAuth2PasswordBearer`, `OAuth2AuthorizationCodeBearer`: the bearer token;
  `OAuth2`, `OpenIdConnect`: the whole `Authorization` header.

`auto_error` is a type index: a scheme with `auto_error := true` (the
default) answers 401 itself and gives its value; with `false` it gives
`none` instead of failing (`AutoError`).
-/

namespace LeanFastapi

open LeanJson (Json)
open LeanStarlette (Request Exception)

/-- A scheme's value: itself when it raises on a missing credential
(`auto_error=True`), else optional. -/
@[reducible] def AutoError : Bool → Type → Type
  | true, α => α
  | false, α => Option α

/-- What a scheme gives when the credential is missing or wrong: the 401 it
raises, or `none`. -/
def AutoError.fail {α : Type} : (autoError : Bool) → Exception → Handler (AutoError autoError α)
  | true, e => throw e
  | false, _ => pure (none : Option α)

/-- What a scheme gives when the credential is there. -/
def AutoError.ok {α : Type} : (autoError : Bool) → α → AutoError autoError α
  | true, a => a
  | false, a => some a

/-- What a security scheme tells OpenAPI: its name in
`components.securitySchemes`, and its model. -/
class SecurityBase (T : Type) where
  scheme_name : T → String
  model : T → SecurityScheme

/-- `401 Not authenticated` with a `WWW-Authenticate` challenge. -/
def notAuthenticated (challenge : String) : Exception :=
  .http 401 "Not authenticated" [("WWW-Authenticate", challenge)] (by decide)

/-! ## The `Authorization` header -/

/-- **`get_authorization_scheme_param`**: the text before the first space
and the (stripped) rest; `("", "")` without a header. -/
def authorizationSchemeParam : Option String → String × String
  | none => ("", "")
  | some v =>
    if v.isEmpty then ("", "")
    else
      let cs := v.toList
      let scheme := cs.takeWhile (· ≠ ' ')
      (String.ofList scheme, pyStrip (String.ofList ((cs.dropWhile (· ≠ ' ')).drop 1)))

/-- The request's `Authorization` header. -/
def authorizationOf (req : Request) : Option String := req.headers.get? "authorization"

/-! ## Base64 -/

/-- The character of a 6-bit value in the standard alphabet. -/
def b64Char (n : Nat) : Char :=
  let i := n % 64
  if i < 26 then Char.ofNat (65 + i)
  else if i < 52 then Char.ofNat (71 + i)
  else if i < 62 then Char.ofNat (i - 4)
  else if i = 62 then '+' else '/'

/-- The 6-bit value of a character of the standard alphabet. -/
def b64Value (c : Char) : Option Nat :=
  let n := c.toNat
  if 65 ≤ n ∧ n ≤ 90 then some (n - 65)
  else if 97 ≤ n ∧ n ≤ 122 then some (n - 71)
  else if 48 ≤ n ∧ n ≤ 57 then some (n + 4)
  else if c = '+' then some 62
  else if c = '/' then some 63
  else none

/-- `base64.b64encode`: three bytes as four characters, the last group
padded with `=`. -/
def b64encode : List Nat → List Char
  | a :: b :: c :: rest =>
    b64Char (a / 4) :: b64Char (a % 4 * 16 + b / 16) :: b64Char (b % 16 * 4 + c / 64) :: b64Char (c % 64) ::
      b64encode rest
  | [a, b] => [b64Char (a / 4), b64Char (a % 4 * 16 + b / 16), b64Char (b % 16 * 4), '=']
  | [a] => [b64Char (a / 4), b64Char (a % 4 * 16), '=', '=']
  | [] => []

/-- The decoder's state (CPython's `binascii.a2b_base64`): the position in
the current group of four, the bits carried, the pads seen, and the bytes
so far (reversed). -/
structure B64State where
  quad : Nat := 0
  left : Nat := 0
  pads : Nat := 0
  out : List Nat := []

/-- Feed one character to the decoder: `.inr` when a pad sequence ends the
data. -/
def B64State.step (st : B64State) (c : Char) : B64State ⊕ B64State :=
  if c = '=' then
    let pads := st.pads + 1
    -- a complete pad sequence ends the data, and the group counts as whole
    if st.quad ≥ 2 ∧ st.quad + pads ≥ 4 then .inr { st with quad := 0, left := 0, pads := 0 }
    else .inl { st with pads }
  else
    match b64Value c with
    | none => .inl st
    | some v =>
      match st.quad with
      | 0 => .inl { st with quad := 1, left := v, pads := 0 }
      | 1 => .inl { st with quad := 2, left := v % 16, pads := 0, out := (st.left * 4 + v / 16) % 256 :: st.out }
      | 2 => .inl { st with quad := 3, left := v % 4, pads := 0, out := (st.left * 16 + v / 4) % 256 :: st.out }
      | _ => .inl { st with quad := 0, left := 0, pads := 0, out := (st.left * 64 + v) % 256 :: st.out }

/-- Run the decoder over the characters until they end or a pad sequence
ends the data. -/
def B64State.run (st : B64State) : List Char → B64State
  | [] => st
  | c :: cs =>
    match st.step c with
    | .inl st' => st'.run cs
    | .inr st' => st'

/-- **`base64.b64decode(s)`** (non-validating): `none` for non-ASCII input,
one stray data character, or missing padding. -/
def b64decode (s : List Char) : Option (List Nat) :=
  if s.any (fun c => c.toNat ≥ 128) then none
  else
    let st := ({} : B64State).run s
    if st.quad = 0 then some st.out.reverse else none

/-- The `Authorization: Basic` parameter a client sends:
`base64(username:password)` (what `httpx.BasicAuth` encodes). -/
def basicToken (username password : String) : String :=
  String.ofList (b64encode ((username ++ ":" ++ password).toList.map Char.toNat))

/-! ## Credentials -/

/-- `HTTPBasicCredentials`. -/
structure HTTPBasicCredentials where
  username : String
  password : String
  deriving LeanPydantic.Model

/-- `HTTPAuthorizationCredentials`: the scheme and the credentials of an
`Authorization` header. -/
structure HTTPAuthorizationCredentials where
  scheme : String
  credentials : String
  deriving LeanPydantic.Model

/-- **`HTTPBasic.__call__`'s decoding**: the `Basic` parameter, base64-decoded
to ASCII and split at the first `:`. -/
def basicCredentials (param : String) : Option HTTPBasicCredentials := do
  let bytes ← b64decode param.toList
  if bytes.any (· ≥ 128) then none
  else
    let data := bytes.map Char.ofNat
    let user := data.takeWhile (· ≠ ':')
    let rest := data.dropWhile (· ≠ ':')
    match rest with
    | [] => none
    | _ :: pw => some { username := String.ofList user, password := String.ofList pw }

/-! ## The schemes -/

/-- `APIKeyQuery`, `APIKeyHeader` and `APIKeyCookie`: an API key read from
`location` under `name`. -/
structure APIKey (location : APIKeyIn) (autoError : Bool) where
  name : String
  scheme_name : String
  description : Option String := none

/-- **Where an API key is read**: the query string, a header, or a cookie. -/
def apiKeyValue (location : APIKeyIn) (name : String) (req : Request) : Option String :=
  match location with
  | .query => req.queryParams.get? name
  | .header => req.headers.get? name
  | .cookie => (cookieParser ((req.headers.get? "cookie").getD "")).lookup name

/-- `APIKeyQuery(name=..., scheme_name=None, description=None, auto_error=True)`. -/
def APIKeyQuery (name : String) (scheme_name : String := "APIKeyQuery") (description : Option String := none)
    (auto_error : Bool := true) : APIKey .query auto_error := { name, scheme_name, description }

/-- `APIKeyHeader(name=..., ...)`. -/
def APIKeyHeader (name : String) (scheme_name : String := "APIKeyHeader") (description : Option String := none)
    (auto_error : Bool := true) : APIKey .header auto_error := { name, scheme_name, description }

/-- `APIKeyCookie(name=..., ...)`. -/
def APIKeyCookie (name : String) (scheme_name : String := "APIKeyCookie") (description : Option String := none)
    (auto_error : Bool := true) : APIKey .cookie auto_error := { name, scheme_name, description }

/-- `APIKeyBase.__call__`: the key, or 401 (`WWW-Authenticate: APIKey`) when
it is missing or empty. -/
def APIKey.call {location : APIKeyIn} {autoError : Bool} (self : APIKey location autoError) (request : Request) :
    Handler (AutoError autoError String) :=
  match apiKeyValue location self.name request with
  | some k => if k.isEmpty then AutoError.fail autoError (notAuthenticated "APIKey") else pure (AutoError.ok autoError k)
  | none => AutoError.fail autoError (notAuthenticated "APIKey")

instance {location : APIKeyIn} {autoError : Bool} : SecurityBase (APIKey location autoError) where
  scheme_name s := s.scheme_name
  model s := .apiKey location s.name s.description

/-- `HTTPBasic(scheme_name=None, realm=None, description=None,
auto_error=True)`. -/
structure HTTPBasic (autoError : Bool := true) where
  scheme_name : String := "HTTPBasic"
  realm : Option String := none
  description : Option String := none

/-- `HTTPBasic(...)`. -/
def HTTPBasic.new (scheme_name : String := "HTTPBasic") (realm : Option String := none)
    (description : Option String := none) (auto_error : Bool := true) : HTTPBasic auto_error :=
  { scheme_name, realm, description }

/-- `HTTPBasic.__call__`. -/
def HTTPBasic.call {autoError : Bool} (self : HTTPBasic autoError) (request : Request) :
    Handler (AutoError autoError HTTPBasicCredentials) :=
  let challenge := match self.realm with
    | some r => if r.isEmpty then "Basic" else s!"Basic realm=\"{r}\""
    | none => "Basic"
  let authorization := authorizationOf request
  let (scheme, param) := authorizationSchemeParam authorization
  if (authorization.getD "").isEmpty || scheme.toLower != "basic" then AutoError.fail autoError (notAuthenticated challenge)
  else match basicCredentials param with
    | some c => pure (AutoError.ok autoError c)
    | none => throw (notAuthenticated challenge)

instance {autoError : Bool} : SecurityBase (HTTPBasic autoError) where
  scheme_name s := s.scheme_name
  model s := .http "basic" none s.description

/-- `HTTPBearer` and `HTTPDigest`: an `Authorization` header of one scheme. -/
structure HTTPScheme (scheme : String) (autoError : Bool) where
  scheme_name : String
  bearerFormat : Option String := none
  description : Option String := none

/-- `HTTPBearer(bearerFormat=None, scheme_name=None, description=None,
auto_error=True)`. -/
def HTTPBearer (bearerFormat : Option String := none) (scheme_name : String := "HTTPBearer")
    (description : Option String := none) (auto_error : Bool := true) : HTTPScheme "bearer" auto_error :=
  { scheme_name, bearerFormat, description }

/-- `HTTPDigest(scheme_name=None, description=None, auto_error=True)`. -/
def HTTPDigest (scheme_name : String := "HTTPDigest") (description : Option String := none)
    (auto_error : Bool := true) : HTTPScheme "digest" auto_error :=
  { scheme_name, description }

/-- `HTTPBearer.__call__` / `HTTPDigest.__call__`: the header's scheme (which
must be this one, in any case) and credentials. -/
def HTTPScheme.call {scheme : String} {autoError : Bool} (_self : HTTPScheme scheme autoError) (request : Request) :
    Handler (AutoError autoError HTTPAuthorizationCredentials) :=
  let challenge := String.ofList (match scheme.toList with | c :: cs => c.toUpper :: cs | [] => [])
  let authorization := authorizationOf request
  let (s, credentials) := authorizationSchemeParam authorization
  if (authorization.getD "").isEmpty || s.isEmpty || credentials.isEmpty || s.toLower != scheme then
    AutoError.fail autoError (notAuthenticated challenge)
  else pure (AutoError.ok autoError { scheme := s, credentials })

instance {scheme : String} {autoError : Bool} : SecurityBase (HTTPScheme scheme autoError) where
  scheme_name s := s.scheme_name
  model s := .http scheme (if scheme = "bearer" then s.bearerFormat else none) s.description

/-- `OAuth2PasswordBearer`, `OAuth2AuthorizationCodeBearer`: a bearer token,
with the flow OpenAPI shows. -/
structure OAuth2Bearer (autoError : Bool) where
  flow : OAuthFlow
  scheme_name : String
  description : Option String := none

/-- `OAuth2PasswordBearer(tokenUrl, scheme_name=None, scopes=None,
description=None, auto_error=True, refreshUrl=None)`. -/
def OAuth2PasswordBearer (tokenUrl : String) (scheme_name : String := "OAuth2PasswordBearer")
    (scopes : List (String × String) := []) (description : Option String := none) (auto_error : Bool := true)
    (refreshUrl : Option String := none) : OAuth2Bearer auto_error :=
  { flow := { kind := "password", tokenUrl, refreshUrl, scopes }, scheme_name, description }

/-- `OAuth2AuthorizationCodeBearer(authorizationUrl, tokenUrl,
refreshUrl=None, scheme_name=None, scopes=None, description=None,
auto_error=True)`. -/
def OAuth2AuthorizationCodeBearer (authorizationUrl tokenUrl : String) (refreshUrl : Option String := none)
    (scheme_name : String := "OAuth2AuthorizationCodeBearer") (scopes : List (String × String) := [])
    (description : Option String := none) (auto_error : Bool := true) : OAuth2Bearer auto_error :=
  { flow := { kind := "authorizationCode", authorizationUrl, tokenUrl, refreshUrl, scopes }, scheme_name, description }

/-- `__call__`: the token after `Bearer`, or 401 (`WWW-Authenticate:
Bearer`). -/
def OAuth2Bearer.call {autoError : Bool} (_self : OAuth2Bearer autoError) (request : Request) :
    Handler (AutoError autoError String) :=
  let authorization := authorizationOf request
  let (scheme, param) := authorizationSchemeParam authorization
  if (authorization.getD "").isEmpty || scheme.toLower != "bearer" then AutoError.fail autoError (notAuthenticated "Bearer")
  else pure (AutoError.ok autoError param)

instance {autoError : Bool} : SecurityBase (OAuth2Bearer autoError) where
  scheme_name s := s.scheme_name
  model s := .oauth2 [s.flow] s.description

/-- `OAuth2(flows=..., ...)` and `OpenIdConnect(openIdConnectUrl=..., ...)`:
the whole `Authorization` header. -/
structure AuthorizationHeader (autoError : Bool) where
  model : SecurityScheme
  scheme_name : String

/-- `OAuth2(flows=OAuthFlows(), scheme_name=None, description=None,
auto_error=True)`. -/
def OAuth2 (flows : List OAuthFlow := []) (scheme_name : String := "OAuth2") (description : Option String := none)
    (auto_error : Bool := true) : AuthorizationHeader auto_error :=
  { model := .oauth2 flows description, scheme_name }

/-- `OpenIdConnect(openIdConnectUrl, scheme_name=None, description=None,
auto_error=True)`. -/
def OpenIdConnect (openIdConnectUrl : String) (scheme_name : String := "OpenIdConnect")
    (description : Option String := none) (auto_error : Bool := true) : AuthorizationHeader auto_error :=
  { model := .openIdConnect openIdConnectUrl description, scheme_name }

/-- `__call__`: the `Authorization` header, or 401. -/
def AuthorizationHeader.call {autoError : Bool} (_self : AuthorizationHeader autoError) (request : Request) :
    Handler (AutoError autoError String) :=
  match authorizationOf request with
  | some a => if a.isEmpty then AutoError.fail autoError (notAuthenticated "Bearer") else pure (AutoError.ok autoError a)
  | none => AutoError.fail autoError (notAuthenticated "Bearer")

instance {autoError : Bool} : SecurityBase (AuthorizationHeader autoError) where
  scheme_name s := s.scheme_name
  model s := s.model

end LeanFastapi
