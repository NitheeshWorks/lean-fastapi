import LeanFastapi.DataTypes.Params

/-!
# DataTypes: dependencies and security schemes

What a dependency is, independently of how it is solved:

* `DepScope`: where a `yield` dependency's exit code runs (`Depends(...,
  scope="function")` or `"request"`);
* `CacheKey`: `fastapi.dependencies.models._get_cache_key`, the identity two
  uses of a dependency share a cached value under: the function, the sorted
  OAuth2 scopes when the dependency uses scopes, and the computed scope;
* `SecurityScheme`: the OpenAPI security scheme objects of
  `fastapi.openapi.models` (`APIKey`, `HTTPBase`, `HTTPBearer`, `OAuth2`,
  `OpenIdConnect`);
* `DepInfo`: the dependency tree as OpenAPI sees it (each dependant's own
  parameters, its sub-dependencies in order, its key, scopes and scheme),
  what `_get_openapi_dependency_data` walks;
* `SecurityScopes`: the value a `SecurityScopes` parameter receives.
-/

namespace LeanFastapi

open LeanJson (Json)

/-- Where a `yield` dependency's exit code runs: after the path operation
function returns (`function`), or after the response (`request`, the
default for `yield` dependencies). -/
inductive DepScope where
  | function
  | request
  deriving DecidableEq, Repr, Inhabited

namespace DepScope

/-- The name FastAPI uses. -/
def value : DepScope → String
  | .function => "function"
  | .request => "request"

end DepScope

/-- `_get_cache_key`: the dependency (a declaration name), its scopes sorted
and deduplicated when it uses scopes (else empty), and its computed scope
(`""` for a dependency that does not `yield` and has no explicit scope). -/
structure CacheKey where
  call : String
  scopes : List String := []
  scope : String := ""
  deriving DecidableEq, Repr, Inhabited

/-- Where an API key is read from (`APIKeyIn`). -/
inductive APIKeyIn where
  | query
  | header
  | cookie
  deriving DecidableEq, Repr, Inhabited

namespace APIKeyIn

/-- The OpenAPI `in` value. -/
def value : APIKeyIn → String
  | .query => "query"
  | .header => "header"
  | .cookie => "cookie"

/-- The parameter source it reads. -/
def source : APIKeyIn → Source
  | .query => .query
  | .header => .header
  | .cookie => .cookie

end APIKeyIn

/-- One OAuth2 flow (`OAuthFlowPassword`, `OAuthFlowAuthorizationCode`, ...):
its URLs and its scopes with their descriptions. -/
structure OAuthFlow where
  /-- `password`, `authorizationCode`, `clientCredentials` or `implicit`. -/
  kind : String
  authorizationUrl : Option String := none
  tokenUrl : Option String := none
  refreshUrl : Option String := none
  scopes : List (String × String) := []
  deriving Repr, Inhabited

/-- An OpenAPI security scheme object (`fastapi.openapi.models.SecurityBase`
and its subclasses). -/
inductive SecurityScheme where
  | apiKey («in» : APIKeyIn) (name : String) (description : Option String)
  | http (scheme : String) (bearerFormat : Option String) (description : Option String)
  | oauth2 (flows : List OAuthFlow) (description : Option String)
  | openIdConnect (url : String) (description : Option String)
  deriving Repr, Inhabited

/-- A dependency tree as OpenAPI sees it. `param` is a parameter of the
dependant at this level; `sub` a sub-dependency with its cache key, its own
OAuth2 scopes, its security scheme (with the scheme's name) when it is one,
and its own tree. -/
inductive DepInfo where
  | param (p : ParamInfo)
  | sub (key : CacheKey) (ownScopes : List String) (scheme : Option (String × SecurityScheme))
      (args : List DepInfo)
  deriving Inhabited

/-- `fastapi.security.SecurityScopes`: the OAuth2 scopes required by the
dependants on the way to this one, in order, each once. -/
structure SecurityScopes where
  scopes : List String := []
  deriving DecidableEq, Repr, Inhabited

namespace SecurityScopes

/-- `scope_str`: the scopes separated by spaces. -/
def scope_str (s : SecurityScopes) : String := " ".intercalate s.scopes

end SecurityScopes

end LeanFastapi
