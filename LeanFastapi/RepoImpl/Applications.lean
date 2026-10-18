import LeanFastapi.RepoImpl.Docs

/-!
# RepoImpl: the `FastAPI` application

`fastapi/applications.py`. A `FastAPI` value is the application's settings
and its path operations. Like the Python class, which subclasses
`Starlette`, it runs as a Starlette application (`FastAPI.application`):

* the routes are, in order, the documentation routes `setup()` adds
  (`/openapi.json`, `/docs`, `/docs/oauth2-redirect`, `/redoc`, each a
  Starlette `Route` outside the schema) and then the path operations;
* the exception handlers are the user's, then FastAPI's defaults
  (`HTTPException` as JSON, `RequestValidationError` as 422);
* Starlette's `ServerErrorMiddleware` and `ExceptionMiddleware` wrap them,
  so a `ResponseValidationError` (or any other exception) is a 500.

FastAPI's `APIRoute` answers only its own methods: unlike a Starlette
`Route`, a `GET` operation does not answer `HEAD`. Path operations are
therefore lean-starlette `RouteExact` routes (no automatic `HEAD`), while the
docs pages are plain `Route`s, as in FastAPI.
-/

namespace LeanFastapi

open LeanJson (Json)
open LeanStarlette (Request Response App BaseRoute ExceptionKey ExceptionHandler Middleware)

/-- A FastAPI application: `FastAPI(title=..., version=..., ...)` and its
path operations. -/
structure FastAPI where
  debug : Bool := false
  title : String := "FastAPI"
  summary : Option String := none
  description : String := ""
  version : String := "0.1.0"
  openapi_url : Option String := some "/openapi.json"
  docs_url : Option String := some "/docs"
  redoc_url : Option String := some "/redoc"
  swagger_ui_oauth2_redirect_url : Option String := some "/docs/oauth2-redirect"
  swagger_ui_parameters : List (String × Json) := []
  /-- The path operations, in the order they were added. -/
  routes : List APIRoute := []
  exception_handlers : List (ExceptionKey × ExceptionHandler) := []
  middleware : List Middleware := []
  /-- `FastAPI(dependencies=[...])`: solved before every path operation's
  own dependencies. -/
  dependencies : List Dependency := []
  /-- `app.dependency_overrides`: replacements by dependency name. -/
  dependency_overrides : List (String × ErasedRun) := []

namespace FastAPI

/-- The application with more path operations, after its own; the
application's `dependencies` head each one's tree. -/
def withRoutes (app : FastAPI) (routes : List APIRoute) : FastAPI :=
  { app with routes := app.routes ++ routes.map (APIRoute.withDependencies app.dependencies) }

/-- `app.dependency_overrides[original] = override`: requests solve
`override` wherever `original` was declared. -/
def overrideDependency (app : FastAPI) (original override : Dependency) : FastAPI :=
  { app with dependency_overrides :=
      (original.key.call, override.run) :: app.dependency_overrides.filter (·.1 != original.key.call) }

/-- `app.dependency_overrides = {}`. -/
def clearOverrides (app : FastAPI) : FastAPI := { app with dependency_overrides := [] }

/-- What the routes read from the application. -/
def routeEnv (app : FastAPI) : RouteEnv :=
  { overrides := app.dependency_overrides, dependencies := app.dependencies }

/-- The `info` object. -/
def info (app : FastAPI) : Info :=
  { title := app.title, version := app.version, summary := app.summary, description := app.description }

/-- **`app.openapi()`**, as a document. -/
def openapiSchema (app : FastAPI) : OpenAPI := getOpenapi app.info app.routes

/-- `app.openapi()`, as JSON. -/
def openapiJson (app : FastAPI) : Json := app.openapiSchema.toJson

/-- The routes `setup()` adds for the documentation. -/
def docsRoutes (app : FastAPI) : List BaseRoute :=
  match app.openapi_url with
  | none => []
  | some openapi_url =>
    let schema := app.openapiJson
    let openapiRoute := LeanStarlette.Route openapi_url (fun (_ : Request) =>
      LeanStarlette.JSONResponse schema) (name := "openapi")
    let docs := match app.docs_url with
      | none => []
      | some docs_url =>
        let rootless (req : Request) := String.ofList (req.root_path.toList.reverse.dropWhile (· = '/')).reverse
        LeanStarlette.Route docs_url (fun (req : Request) =>
          LeanStarlette.HTMLResponse (getSwaggerUiHtml (rootless req ++ openapi_url) (app.title ++ " - Swagger UI")
            (oauth2_redirect_url := app.swagger_ui_oauth2_redirect_url.map (rootless req ++ ·))
            (swagger_ui_parameters := app.swagger_ui_parameters))) (name := "swagger_ui_html") ::
        (match app.swagger_ui_oauth2_redirect_url with
          | some u => [LeanStarlette.Route u (fun (_ : Request) =>
              LeanStarlette.HTMLResponse swaggerUiOauth2RedirectHtml) (name := "swagger_ui_redirect")]
          | none => [])
    let redoc := match app.redoc_url with
      | none => []
      | some redoc_url =>
        [LeanStarlette.Route redoc_url (fun (req : Request) =>
          let rp := String.ofList (req.root_path.toList.reverse.dropWhile (· = '/')).reverse
          LeanStarlette.HTMLResponse (getRedocHtml (rp ++ openapi_url) (app.title ++ " - ReDoc"))) (name := "redoc_html")]
    openapiRoute :: docs ++ redoc

end FastAPI

namespace APIRoute

/-- The Starlette route of a path operation, under the application's
overrides and dependencies: exactly its methods. -/
def toBaseRoute (env : RouteEnv) (r : APIRoute) : BaseRoute :=
  LeanStarlette.RouteExact r.path (r.endpoint env) (methods := r.methods) (name := r.name)

end APIRoute

namespace FastAPI

/-- **The application as a Starlette application**: what serves requests. -/
def application (app : FastAPI) : LeanStarlette.Application :=
  LeanStarlette.Starlette (debug := app.debug)
    (routes := app.docsRoutes ++ app.routes.map (APIRoute.toBaseRoute app.routeEnv))
    (middleware := app.middleware)
    (exception_handlers := app.exception_handlers ++ defaultExceptionHandlers)

/-- Handle one request. -/
def call (app : FastAPI) (req : Request) : IO Response := app.application.call req

end FastAPI

end LeanFastapi
