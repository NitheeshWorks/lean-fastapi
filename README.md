# lean-fastapi

[![Lean 4](https://img.shields.io/badge/built%20with-Lean%204-blue.svg)](https://lean-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-machine%20checked-brightgreen.svg)](CONTRIBUTING.md#verification)

A clean-room port of [FastAPI](https://github.com/fastapi/fastapi) to Lean 4: typed dependency injection, parameter extraction, response models and OpenAPI generation, each with its contract proved.

Part of the verified FastAPI stack: [lean-fastapi](https://github.com/NitheeshWorks/lean-fastapi)
and its dependencies, each ported as its own repo with its proofs. This one
depends on: [lean-pydantic](https://github.com/NitheeshWorks/lean-pydantic), [lean-starlette](https://github.com/NitheeshWorks/lean-starlette), [lean-click](https://github.com/NitheeshWorks/lean-click).

## What "verified" means here

* Public functions take the weakest precondition they need and return the
  strongest postcondition, as a refinement type `{r // Post r}` or an
  `Except` of one. Invariants live in types, not comments.
* Every theorem is machine-checked. CI fails on `sorry` and on any axiom
  beyond Lean's own `propext`, `Quot.sound` and `Classical.choice`.
* What is tested rather than proved is listed, with the reason, in
  [CONTRIBUTING.md](CONTRIBUTING.md#verification) and in
  `docs/traceability.toml`.

## Quickstart

```lean
import LeanFastapi
open LeanFastapi

def app := FastAPI.new

@[get "/items/{item_id}"]
def readItem (item_id : Int) (q : Option String := none) : Handler Json :=
  return json% {"item_id": item_id, "q": q}

structure Item where
  name  : String ∣ maxLength 50
  price : Float ∣ gt 0
  deriving Model

@[put "/items/{item_id}" (response_model := Item)]
def updateItem (item_id : Int) (item : Item) : Handler Item :=
  return item

def main : IO Unit := app.run (port := 8000)
```

As in FastAPI, a parameter's kind is inferred: a name in the path template is
a path parameter, a `Model` is the body, anything else is a query parameter.
`Path`, `Query`, `Header`, `Cookie` and `Body` wrap a type to say so
explicitly or to carry metadata; constraints are refinement types `α ∣ c`;
`throw (HTTPException 404 "Item not found")` answers `{"detail": ...}`. No
proof terms are written by the user. `/openapi.json`, `/docs` and `/redoc`
are served for every app.

Dependencies and security read as in the tutorial (`tests/apps/` has every
ported tutorial app):

```lean
def commonParameters (q : Option String := none) (skip : Int := 0) (limit : Int := 100) : Handler Json :=
  return json% {"q": q, "skip": skip, "limit": limit}

@[get "/users/"]
def readUsers (commons : Depends commonParameters) : Handler Json :=
  return commons

def oauth2Scheme := OAuth2PasswordBearer (tokenUrl := "token")

def getDb : Yield Db := yieldWith openDb fun _ => closeDb   -- exit code after the response

@[get "/items/"]
def readItems (token : Depends oauth2Scheme) (db : Depends getDb) : Handler Json :=
  return json% {"token": token}
```

`Security oauth2Scheme ["items"]` and a `SecurityScopes` parameter carry
OAuth2 scopes; `app.dependency_overrides` (`app.overrideDependency`)
replaces a dependency in tests:
`app.overrideDependency (Depends commonParameters) (Depends overrider)`.

```
lake exe example      # demo/App.lean on http://127.0.0.1:8000
lake build            # library, proofs, tests
lake exe props        # property tests (seeded; `lake exe props 42`)
lake exe conformance  # golden cases recorded from fastapi 0.143.3
scripts/check.sh      # the whole CI gate, locally (--pbt adds plausible)
```

Toolchain: `leanprover/lean4:v4.35.0` (pinned in `lean-toolchain`; `elan` installs it).

### The demo against FastAPI

The same requests to `lake exe example` and to the Python twin of the demo
under uvicorn (fastapi 0.143.3, pydantic 2.14.1) give identical output:

```
$ curl 127.0.0.1:8000/items/42?q=x
{"item_id":42,"q":"x"}                                                      [200]
$ curl 127.0.0.1:8000/items/foo
{"detail":[{"type":"int_parsing","loc":["path","item_id"],"msg":"Input should be a valid integer, unable to parse string as an integer","input":"foo"}]}   [422]
$ curl -X PUT 127.0.0.1:8000/items/1 -H 'content-type: application/json' -d '{"price":-1}'
{"detail":[{"type":"missing","loc":["body","name"],"msg":"Field required","input":{"price":-1}},{"type":"greater_than","loc":["body","price"],"msg":"Input should be greater than 0","input":-1,"ctx":{"gt":0.0}}]}   [422]
$ curl -X PUT 127.0.0.1:8000/items/1 -H 'content-type: application/json' -d '{"name":'
{"detail":[{"type":"json_invalid","loc":["body",8],"msg":"JSON decode error","input":{},"ctx":{"error":"Expecting value"}}]}   [422]
$ curl 127.0.0.1:8000/stock/bar
{"detail":"Item not found"}                                                 [404]
$ curl -s 127.0.0.1:8000/openapi.json | sha256sum     # the same on both
06a6bf49950e9392710a35a0059557389e40ef8ecc0e00336258a134d9408688
```

## What is proved

For every application (`LeanFastapi/Proofs/Verified.lean` bundles them):

* **Parameters.** Every validation error of a parameter is located under its
  `(source, alias)` (`params_to_args_loc`); extraction succeeds exactly when
  every parameter validates (`extract_cons_ok_iff`, `extract_sound`); a
  failure answers 422 with `{"detail": errors}` (`extract_422`); kind
  inference follows FastAPI's rule (`infer_param`); header names use hyphens
  (`header_alias_hyphen`).
* **Responses.** With a response model the body conforms to the model's
  schema (`serialize_response_conforms`).
* **OpenAPI.** Every route and method appears exactly once
  (`openapi_all_routes`); every `$ref` resolves to a component
  (`openapi_refs_resolve`); components are sorted
  (`openapi_components_sorted`); operation ids are unique
  (`operationId_unique`); a 422 response is documented iff the route has
  parameters (`openapi_422_iff`); documented parameters are the route's
  (`openapi_params_match`).

* **Dependencies.** Sub-dependencies run in declaration order, before the
  dependant (`solve_order`), and the errors of a tree are its nodes' errors
  in that order (`params_errors`); two uses under one cache key share a value
  within a request (`cache_same_key`); an override replaces the dependency
  and its sub-tree (`override_replaces`); exit code runs in reverse order of
  entry (`cleanup_reverse`), and function-scoped exits finish before the
  response (`function_scope_not_outlive`); `SecurityScopes` holds the scopes
  of every `Security` on the way to it (`security_scopes_accumulate`).
* **Security.** An `Authorization` header splits into scheme and credentials
  at the first space (`bearer_parse`); HTTP Basic credentials decode back to
  what the client encoded (`basic_base64_roundtrip`); an API key is read
  only from its declared location (`apikey_sources`).

Wire behaviour (byte-identical bodies, headers, `/openapi.json`, `/docs`,
`/redoc`, CPython's `json.loads` error positions) is tested against recorded
fastapi output rather than proved; see CONTRIBUTING.md.

## Status

Milestones 1 and 3: path, query, header and cookie parameters, JSON and
urlencoded form bodies, 422 errors, response models, HTTPException, OpenAPI
and the docs pages, the demo; `Depends` with caching, overrides and `yield`
dependencies, `Security` and `SecurityScopes`, API keys, HTTP Basic, Bearer
and Digest, OAuth2 password and authorization code, and OpenID Connect.
Multipart forms and files, middleware and streaming are the next milestones.

## License

MIT, see [LICENSE](LICENSE). Upstream attribution is in [NOTICE](NOTICE).
