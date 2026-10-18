import LeanFastapi.APIs.Endpoint
import LeanStarlette.Transport

/-!
# APIs: `FastAPI`

```lean
def app := FastAPI.new

@[get "/"]
def root : Handler Json := return json% {"message": "Hello World"}

def main : IO Unit := app.run (port := 8000)
```

`FastAPI.new` takes `FastAPI(...)`'s arguments. The path operations
declared in the module of `app` belong to it: `app.run`, `app.openapi` and
`TestClient app` collect them where they are used (the `routes` argument,
filled in by `declared_routes`), so `app` can be declared before its routes,
as in Python.
-/

namespace LeanFastapi

open LeanJson (Json)
open LeanStarlette (Request Response)

export LeanStarlette (Request Response JSONResponse HTMLResponse PlainTextResponse RedirectResponse Exception)
export LeanJson (Json)
export LeanPydantic (Decimal Model)

namespace FastAPI

/-- `FastAPI(debug=False, title="FastAPI", summary=None, description="",
version="0.1.0", openapi_url="/openapi.json", docs_url="/docs",
redoc_url="/redoc", swagger_ui_oauth2_redirect_url="/docs/oauth2-redirect",
swagger_ui_parameters=None, dependencies=None)`. -/
def new (debug : Bool := false) (title : String := "FastAPI") (summary : Option String := none)
    (description : String := "") (version : String := "0.1.0")
    (openapi_url : Option String := some "/openapi.json") (docs_url : Option String := some "/docs")
    (redoc_url : Option String := some "/redoc")
    (swagger_ui_oauth2_redirect_url : Option String := some "/docs/oauth2-redirect")
    (swagger_ui_parameters : List (String × Json) := []) (dependencies : List AnyDependency := []) : FastAPI :=
  { debug, title, summary, description, version, openapi_url, docs_url, redoc_url,
    swagger_ui_oauth2_redirect_url, swagger_ui_parameters, dependencies }

/-- The application with its declared path operations. -/
def complete (app : FastAPI) (routes : DeclaredRoutes app := by declared_routes) : FastAPI :=
  app.withDeclared routes

/-- `app.openapi()`: the OpenAPI document, as JSON. -/
def openapi (app : FastAPI) (routes : DeclaredRoutes app := by declared_routes) : Json :=
  (app.withDeclared routes).openapiJson

/-- `uvicorn.run(app, host=..., port=...)`. -/
def run (app : FastAPI) (host : String := "127.0.0.1") (port : Nat := 8000)
    (routes : DeclaredRoutes app := by declared_routes) : IO Unit :=
  (app.withDeclared routes).application.run host port

end FastAPI

/-- A test client over an application: requests go straight to it, in
process (`fastapi.testclient.TestClient`, the subset milestone 1 needs). -/
structure TestClient where
  app : FastAPI

/-- `TestClient(app)`. -/
def TestClient.new (app : FastAPI) (routes : DeclaredRoutes app := by declared_routes) : TestClient :=
  ⟨app.withDeclared routes⟩

namespace TestClient

/-- Send a request: method, path with query string, headers and body. -/
def request (c : TestClient) (method : String) (url : String) (headers : List (String × String) := [])
    (content : ByteArray := .empty) : IO Response :=
  let (path, query_string) := LeanStarlette.splitTarget url
  c.app.call { method, path, query_string, headers := LeanStarlette.Headers.ofList headers, bodyBytes := content
               server := some ("testserver", 80) }

def get (c : TestClient) (url : String) (headers : List (String × String) := []) : IO Response :=
  c.request "GET" url headers

/-- A request with a JSON body (`json=`), as `application/json`. -/
def requestJson (c : TestClient) (method url : String) (body : Json) (headers : List (String × String) := []) :
    IO Response :=
  c.request method url (headers ++ [("content-type", "application/json")]) (LeanJson.print body).val

end TestClient

end LeanFastapi
