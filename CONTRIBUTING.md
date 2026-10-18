# Contributing to lean-fastapi

`README.md` covers usage. This file covers the architecture, the verification
rules, the repository layout and the conventions, and is the document to keep
current when the code changes.

## Architecture

`LeanFastapi/` is layered bottom-up; each layer imports only the ones below it, so a
proof at one layer rewrites with lemmas from beneath it instead of unfolding
to bytes:

| Directory | Holds | Proved? |
|---|---|---|
| `DataTypes/` | structures and inductives; invariants are fields | n/a |
| `RepoImpl/` | executable definitions; total, structural recursion | subject of proofs |
| `Specifications/` | the properties, in `Prop` | the contract |
| `Proofs/` | theorems; `Proofs/Verified.lean` bundles one `Verified<Layer>` per layer | yes |
| `APIs/` | the public surface, returning refinements | by construction |
| `APIs/Endpoint.lean` | the `@[get]`/`@[post]`/... attributes: elaborate a path operation into an `APIRoute` | by construction |
| transport | lean-starlette's server; `FastAPI.run` only calls it | no; tested |

A request flows: lean-starlette routing → `APIRoute.app` → `Inputs.ofRequest`
(`RepoImpl/Body.lean`, which reads the JSON body and emulates `json.loads`
errors with `RepoImpl/PyJson.lean`) → `Params.extract` (each `Param` a Keel
`Validator` at its location, built on lean-pydantic's `FromJson`) → the
handler → `renderResult` (a `ResponseModel` re-validates and dumps) → the
exception handlers (`RepoImpl/Exceptions.lean`). `RepoImpl/OpenApi.lean`
builds the document from the same `APIRoute`s, which is what lets the
OpenAPI theorems quantify over every app.

The attribute (`APIs/Endpoint.lean`) records each route in an environment
extension; `FastAPI.run`, `complete`, `openapi` and `TestClient.new` take an
auto-parameter filled by the `declared_routes` tactic with the routes declared
in the app's module, so routes may follow the `def app`.

Everything except the transport module is a pure function. This is
load-bearing: a round-trip property of a function is an equation that
`omega` and `simp` attack directly; the same property of a procedure would
be a Hoare triple over a heap.

## Verification <a name="verification"></a>

* **Weak preconditions, strong postconditions.** A public function takes the
  minimal hypothesis its body needs (usually none; the refinement lives in the
  input type) and returns the strongest useful statement, typically a round
  trip or a membership, as `{r // Post r}` or `Except Err {r // Post r}`.
* **Refinement types are subtypes with `Decidable` predicates**, so the same
  predicate is checked at runtime (`if h : P x`) and used in proofs.
* **Totality.** No `partial def` or `unsafe` under `LeanFastapi/`. Byte parsers recurse
  on a `Nat` fuel equal to the remaining input, with a progress lemma per
  production.
* **`_ext` lemmas.** A decoder lemma holds on any continuation of the buffer and
  reports the final position, so field lemmas compose. Do not add a lemma that
  only holds at the end of a buffer; it is unusable one field later.
* **Numbers.** `Nat`/`Int`/decimal-as-rational in proofs. `Float` only at the
  boundary via `Float.toBits`. Never `bv_decide` or `native_decide`.
* **The gate.** `scripts/check.sh` runs what CI runs: build, `sorry` grep,
  `scripts/Axioms.lean` (every theorem under `LeanFastapi` reaches only `propext`,
  `Quot.sound`, `Classical.choice`), `lake exe props`, `lake exe conformance`,
  the traceability check.

### Tested, not proved

Listed here with the reason, and in `docs/traceability.toml` with
`status = "tested"`.

* **`json.loads` error emulation** (`RepoImpl/PyJson.lean`): the position and
  message of CPython's C scanner are a property of CPython, not a
  specification; checked on a 4000-text corpus recorded from CPython
  (`tests/golden/pyjson.json`), against lean-json on edited texts
  (`tests/Props.lean`) and with plausible. `readBody` parses with lean-json
  first and asks the emulation only where the two can differ (a rejection,
  or a digit run past Python's 4300-digit limit); a property checks it
  answers as the Python-first order would.
* **Byte-level output**: response bodies and headers, `/openapi.json` key
  order and number formatting, and the `/docs`, `/redoc` and oauth2-redirect
  HTML are compared byte for byte with fastapi 0.143.3 (`tests/golden/`,
  regenerated with `tests/golden/generate.py`).
* **Cookie parsing and the name helpers** (`cookieParser`, `pathFormat`,
  `snakeCase`, `generateUniqueId`): property tests.
* **Transport**: lean-starlette's server, exercised by `lake exe example`.
* **Base64 in `HTTPBasic`** (`b64decode`, `basicCredentials`): the round
  trip is proved (`basic_base64_roundtrip`); the rejections of malformed
  input follow CPython's non-strict `binascii.a2b_base64` and are checked on
  a 3000-text corpus recorded from it (`tests/golden/b64.json`).
* **Urlencoded forms** (`readForm`): Starlette's `FormParser` limits and
  python-multipart's splitting, checked on a 1500-body corpus recorded from
  `Request.form()` (`tests/golden/form.json`).
* **Security schemes and OAuth2PasswordRequestForm**: their 401s, headers
  and OpenAPI objects are compared with fastapi's on the security tutorials
  and tests; what is proved is the parsing underneath (`bearer_parse`,
  `apikey_sources`) and the scope bookkeeping (`security_scopes_accumulate`).
* **The `Depends` macro** (`APIs/Depends.lean`): it builds the `Dep` tree at
  elaboration; the tree's laws are proved (`solve_order`, `cache_same_key`,
  `override_replaces`, `cleanup_reverse`, `function_scope_not_outlive`), the
  macro's translation is tested by the tutorial twins.

### Deviations from FastAPI

* A 405's `Allow` is the union of the methods of every route whose path
  matches (lean-starlette, UP-027); Starlette, and so FastAPI, uses the first
  partially matching route's methods only. With `GET /m` and `POST /m`, a
  `PUT /m` allows `GET, POST` here and `GET` upstream. Path operations are
  `RouteExact` routes, so a `HEAD` on a `GET` operation is a 405 with
  `allow: GET`, as upstream.
* Client input never yields a 500. A 422 whose error echoes an `Infinity` or
  `NaN` the client sent writes it as `null`; FastAPI answers 500 (UP-051). A
  body with a lone surrogate escape (`"\ud800"`) is a 400 "There was an error
  parsing the body", since lean-json rejects it, and a deeply nested array
  (5000 levels) is a 422; FastAPI answers 500 for both (UP-049).
* `operationId` is generated per method, so a multi-method route has distinct
  ids; upstream reuses the first method of a set (UP-046).
* `\W` in `generate_unique_id` treats every non-ASCII character as a word
  character.
* UTF-16 and UTF-32 JSON bodies are not detected (only UTF-8, BOM dropped).
* JSON bodies nested deeper than 9998 levels are rejected by lean-json's
  depth limit; Python's limit depends on the interpreter stack.
* An override's value reaches the dependant through JSON (`FromJson` of the
  dependency's type, or `Json` itself); a value that does not decode is a
  500 `DependencyOverrideError`. Python passes any object.
* The dependencies of an override are not themselves overridden; FastAPI
  applies `dependency_overrides` again inside the override's tree.
* App and router `dependencies=[...]` run with their own per-request cache,
  so a dependency used both there and in the path operation runs twice;
  FastAPI shares one cache.
* An exception raised by request-scoped exit code after the response has
  been sent is dropped; under uvicorn FastAPI logs it.
* `DependencyScopeError` (a request-scoped `yield` dependency depending on a
  function-scoped one) is an elaboration error, not a runtime error when the
  route is added.
* The same parameter declared by the path operation and a dependency reports
  its validation error once per declaration, as FastAPI does (UP-060).
* Security tutorials 004 (argon2 and PyJWT) is not twinned; 005 is, with a
  fake hash and token in place of those libraries. Dependencies tutorials
  007, 008, 010, 013 and 014 are fragments or need sqlmodel and are not
  twinned.
* Not yet: `multipart/form-data` and `File` (milestone 4); `root_path` and
  the `servers` entry.

## Tests

* `tests/Props.lean`: seeded property tests, no dependencies, under a second.
* `tests/Conformance.lean`: cases re-expressed from the upstream suite; each
  names the upstream test (`tests/test_x.py::test_y`). The golden cases
  replay every exchange recorded in `tests/golden/fastapi.json` against the
  Lean twin in `tests/apps/` of each upstream tutorial app. The bench cases
  (`tests/golden/bench.json`) send large generated requests through the demo
  and check the bytes and a time budget.
* `tests/pbt/`: a separate Lake package, the one place an external dependency
  (`plausible`) is taken.

## Traceability

`docs/traceability.toml` links upstream behaviour to the Lean symbol, theorem
and test that realise it. Add a row when behaviour is newly implemented,
tested-only, excluded, or deviates. CI fails if a registered symbol does not
resolve.

## Conventions

* Lean 4 `leanprover/lean4:v4.35.0`; no Mathlib; the core library depends only on Lean
  core and the sibling `lean-*` repos listed in `lakefile.toml`, pinned by
  commit in `lake-manifest.json`.
* Choose the definition that suits the automation over a prettier one with a
  harder proof.
* No upstream code is copied; the upstream test suite and docs are the spec.
