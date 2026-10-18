import LeanFastapi.RepoImpl.Body

/-!
# RepoImpl: FastAPI's exceptions and their default handlers

`fastapi/exceptions.py` and `fastapi/exception_handlers.py`:

* `HTTPException` is Starlette's (FastAPI subclasses it); FastAPI's handler
  renders it as JSON, `{"detail": detail}`, with the exception's headers,
  or with no body when the status allows none;
* `RequestValidationError(errors)` is a 422 with `{"detail": errors}`;
* `ResponseValidationError(errors)` has no handler: it is a server error,
  which Starlette's `ServerErrorMiddleware` turns into a 500.

Lean's `Exception` (lean-starlette) carries non-HTTP exceptions as
`custom kind detail data`; the two validation errors are custom exceptions
whose data is the list of errors as JSON.
-/

namespace LeanFastapi

open LeanJson (Json)
open LeanStarlette (Request Response Exception ExceptionHandler AppM)

export LeanStarlette (HTTPException)

/-- `fastapi.utils.is_body_allowed_for_status_code`. -/
def isBodyAllowedForStatusCode (s : Nat) : Bool := !(s < 200 || s == 204 || s == 205 || s == 304)

/-- The errors as the JSON list FastAPI puts under `detail`. -/
def errorsJson (es : List RequestError) : Json := jarr (es.map RequestError.toJson)

/-- `RequestValidationError(errors)`. -/
def RequestValidationError (errors : List RequestError) : Exception :=
  .custom "RequestValidationError" "" (errorsJson errors)

/-- `ResponseValidationError(errors)`. -/
def ResponseValidationError (errors : List RequestError) : Exception :=
  .custom "ResponseValidationError" s!"{errors.length} validation error(s)" (errorsJson errors)

mutual
/-- Non-finite numbers (an `Infinity` or `NaN` a client sent, echoed as an
error's `input`) written `null`, so a 422 never fails to render. FastAPI
answers 500 there (`allow_nan=False`, UP-051); this is a recorded deviation. -/
def finiteOnly : Json → Json
  | .num n => if n.isFinite then .num n else .null
  | .arr xs => jarr (finiteOnlyList xs.toList)
  | .obj kvs => jobj (finiteOnlyFields kvs.toList)
  | j => j

def finiteOnlyList : List Json → List Json
  | [] => []
  | x :: xs => finiteOnly x :: finiteOnlyList xs

def finiteOnlyFields : List (String × Json) → List (String × Json)
  | [] => []
  | (k, v) :: kvs => (k, finiteOnly v) :: finiteOnlyFields kvs
end

/-- The response FastAPI sends for an `HTTPException`. -/
def httpExceptionResponse (s : Nat) (detail : String) (headers : List (String × String))
    (h : LeanStarlette.StatusCode.Valid s) : Response :=
  if isBodyAllowedForStatusCode s then
    LeanStarlette.JSONResponse (jobj [("detail", .str detail)]) s headers (h := h)
  else Response.make {} s headers none h

/-- `fastapi.exception_handlers.http_exception_handler`. -/
def http_exception_handler : ExceptionHandler := fun _ e =>
  match e with
  | .http s d hs h => pure (httpExceptionResponse s d hs h)
  | e => throw e

/-- The 422 response for a list of errors. -/
def validationErrorResponse (errorsJson : Json) : Response :=
  LeanStarlette.JSONResponse (jobj [("detail", finiteOnly errorsJson)]) 422

/-- `fastapi.exception_handlers.request_validation_exception_handler`. -/
def request_validation_exception_handler : ExceptionHandler := fun _ e =>
  match e with
  | .custom "RequestValidationError" _ data => pure (validationErrorResponse data)
  | e => throw e

/-- FastAPI's default `exception_handlers`. -/
def defaultExceptionHandlers : List (LeanStarlette.ExceptionKey × ExceptionHandler) :=
  [(.httpException, http_exception_handler), (.kind "RequestValidationError", request_validation_exception_handler)]

end LeanFastapi
