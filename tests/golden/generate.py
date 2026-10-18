"""Record fastapi 0.143.3's exact responses for the golden conformance cases.

Run locally (never in CI) with the upstream-spec venv:

    upstream-spec/.venv/bin/python -I tests/golden/generate.py

It writes tests/golden/fastapi.json (HTTP exchanges and app.openapi() per
fixture), tests/golden/bench.json (large inputs through the demo) and
tests/golden/pyjson.json (json.loads errors on a corpus), tests/golden/b64.json
(base64.b64decode and HTTPBasic's credentials) and tests/golden/form.json
(Request.form() on urlencoded bodies).

Each fixture is an upstream tutorial app (imported from
upstream-spec/fastapi/docs_src, the real code) or an app defined below; its
Lean twin of the same name is in tests/apps/ and listed in
tests/Conformance.lean (`fixtures`). Every request is replayed in Lean with
the exact headers TestClient sent, and the status, the response headers and
the body are compared byte for byte.
"""
import importlib, json, random, sys, types, warnings
from pathlib import Path
from typing import Annotated, Any

warnings.simplefilter("ignore")
HERE = Path(__file__).resolve().parent
UPSTREAM = HERE.parents[2] / "upstream-spec" / "fastapi"
sys.path.insert(0, str(UPSTREAM))

from fastapi import Depends, FastAPI, Header, HTTPException, Security  # noqa: E402
from fastapi.security import OAuth2PasswordBearer, OAuth2PasswordRequestForm, SecurityScopes  # noqa: E402
from fastapi.testclient import TestClient  # noqa: E402
from pydantic import BaseModel, Field  # noqa: E402

# The upstream test modules import inline_snapshot, which only their asserts use.
sys.modules.setdefault("inline_snapshot", types.SimpleNamespace(snapshot=lambda x=None: x))


def tutorial(path):
    return importlib.import_module("docs_src." + path).app


def upstream_test(name):
    """The app an upstream test module defines (tests/<name>.py)."""
    return importlib.import_module("tests." + name).app


# The milestone 1 demo, twin of demo/Example.lean.
demo = FastAPI()


@demo.get("/")
async def root():
    return {"message": "Hello World"}


@demo.get("/items/{item_id}")
async def read_item(item_id: int, q: str | None = None):
    return {"item_id": item_id, "q": q}


class Item(BaseModel):
    name: Annotated[str, Field(max_length=50)]
    description: str | None = None
    price: Annotated[float, Field(gt=0)]
    tax: float | None = None


@demo.put("/items/{item_id}", response_model=Item)
async def update_item(item_id: int, item: Item):
    return item


stock = {"foo": "The Foo Wrestlers"}


@demo.get("/stock/{item_id}")
async def read_stock(item_id: str):
    if item_id not in stock:
        raise HTTPException(status_code=404, detail="Item not found")
    return {"item": stock[item_id]}


# response_model filtering and validation, twin of tests/apps/ResponseModel.lean.
rm = FastAPI()


class Public(BaseModel):
    name: str
    price: float


@rm.get("/public", response_model=Public)
async def get_public():
    return {"name": "Foo", "price": 1, "secret": "s3cr3t"}


@rm.get("/typed")
async def get_typed() -> Public:
    return Public(name="Bar", price=2.5)


@rm.get("/count")
async def get_count() -> int:
    return 3


@rm.post("/created", status_code=201, tags=["items"], summary="Create", response_description="Made",
         deprecated=True)
async def make(item: Public) -> Public:
    return item


@rm.delete("/zap", operation_id="zap_it")
async def zap(item: Public | None = None):
    return {"had": item is not None}


@rm.get("/multi")
async def multi_get():
    return {"m": "get"}


@rm.post("/multi")
async def multi_post():
    return {"m": "post"}


class Count(BaseModel):
    n: int


@rm.post("/counted")
async def counted(c: Count) -> Count:
    return c


# Timed cases (critic, b6n01b9wts1z), twin of tests/apps/Bench.lean.
bench_app = FastAPI()


@bench_app.get("/header-int")
async def header_int(x_n: Annotated[int, Header()]):
    return {"positive": x_n > 0}


@bench_app.post("/dict")
async def dict_body(d: dict[str, int]):
    return {"keys": len(d)}


# Exit order of yield dependencies, twin of tests/apps/DependencyYield.lean.
deps_yield = FastAPI()
events = []


def dep_a():
    events.append("a enter")
    try:
        yield "a"
    except Exception:
        events.append("a exit error")
        raise
    else:
        events.append("a exit ok")


def dep_b(a: Annotated[str, Depends(dep_a)]):
    events.append("b enter")
    try:
        yield a + "b"
    except Exception:
        events.append("b exit error")
        raise
    else:
        events.append("b exit ok")


def dep_f():
    events.append("f enter")
    try:
        yield "f"
    except Exception:
        events.append("f exit error")
        raise
    else:
        events.append("f exit ok")


@deps_yield.get("/run")
def run(b: Annotated[str, Depends(dep_b)], f: Annotated[str, Depends(dep_f, scope="function")]):
    events.append("endpoint")
    return {"b": b, "f": f}


@deps_yield.get("/fail")
def fail(b: Annotated[str, Depends(dep_b)], f: Annotated[str, Depends(dep_f, scope="function")]):
    events.append(f"endpoint {b} {f}")
    raise HTTPException(status_code=418, detail="teapot")


@deps_yield.get("/invalid")
def invalid(b: Annotated[str, Depends(dep_b)], n: int):
    events.append(f"endpoint {b} {n}")
    return {"n": n}


@deps_yield.get("/events")
def get_events():
    out = list(events)
    events.clear()
    return out


# tests/test_dependency_overrides.py without its APIRouter, twin of
# tests/apps/DependencyOverrides.lean; two apps, one per override.
def overrides_app(override):
    app = FastAPI()

    async def common_parameters(q: str, skip: int = 0, limit: int = 100):
        return {"q": q, "skip": skip, "limit": limit}

    @app.get("/main-depends/")
    async def main_depends(commons: dict = Depends(common_parameters)):
        return {"in": "main-depends", "params": commons}

    @app.get("/decorator-depends/", dependencies=[Depends(common_parameters)])
    async def decorator_depends():
        return {"in": "decorator-depends"}

    async def overrider_dependency_simple(q: str | None = None):
        return {"q": q, "skip": 5, "limit": 10}

    async def overrider_sub_dependency(k: str):
        return {"k": k}

    async def overrider_dependency_with_sub(msg: dict = Depends(overrider_sub_dependency)):
        return msg

    if override:
        app.dependency_overrides[common_parameters] = {
            "simple": overrider_dependency_simple, "with_sub": overrider_dependency_with_sub}[override]
    return app


# docs_src/security/tutorial005_an_py310.py with its argon2 hash and its JWT
# replaced by fakes, twin of tests/apps/Security005.lean.
security_005 = FastAPI()


class Token(BaseModel):
    access_token: str
    token_type: str


class User(BaseModel):
    username: str
    email: str | None = None
    full_name: str | None = None
    disabled: bool | None = None


class UserInDB(User):
    hashed_password: str


fake_users_db_005 = {
    "johndoe": {"username": "johndoe", "full_name": "John Doe", "email": "johndoe@example.com",
                "hashed_password": "fakehashedsecret", "disabled": False},
    "alice": {"username": "alice", "full_name": "Alice Chains", "email": "alicechains@example.com",
              "hashed_password": "fakehashedsecret2", "disabled": True},
}

oauth2_scheme_005 = OAuth2PasswordBearer(
    tokenUrl="token",
    scopes={"me": "Read information about the current user.", "items": "Read items."},
)


def get_user_005(db, username: str):
    if username in db:
        return UserInDB(**db[username])


def authenticate_user_005(db, username, password):
    user = get_user_005(db, username)
    if not user or "fakehashed" + password != user.hashed_password:
        return False
    return user


async def get_current_user_005(security_scopes: SecurityScopes, token: Annotated[str, Depends(oauth2_scheme_005)]):
    if security_scopes.scopes:
        authenticate_value = f'Bearer scope="{security_scopes.scope_str}"'
    else:
        authenticate_value = "Bearer"
    credentials_exception = HTTPException(
        status_code=401, detail="Could not validate credentials", headers={"WWW-Authenticate": authenticate_value})
    parts = token.split("|")
    if len(parts) != 2:
        raise credentials_exception
    username, scope = parts
    token_scopes = scope.split(" ")
    user = get_user_005(fake_users_db_005, username=username)
    if user is None:
        raise credentials_exception
    for scope in security_scopes.scopes:
        if scope not in token_scopes:
            raise HTTPException(status_code=401, detail="Not enough permissions",
                                headers={"WWW-Authenticate": authenticate_value})
    return user


async def get_current_active_user_005(current_user: Annotated[User, Security(get_current_user_005, scopes=["me"])]):
    if current_user.disabled:
        raise HTTPException(status_code=400, detail="Inactive user")
    return current_user


@security_005.post("/token")
async def login_for_access_token(form_data: Annotated[OAuth2PasswordRequestForm, Depends()]) -> Token:
    user = authenticate_user_005(fake_users_db_005, form_data.username, form_data.password)
    if not user:
        raise HTTPException(status_code=400, detail="Incorrect username or password")
    return Token(access_token=user.username + "|" + " ".join(form_data.scopes), token_type="bearer")


@security_005.get("/users/me/")
async def read_users_me(current_user: Annotated[User, Depends(get_current_active_user_005)]) -> User:
    return current_user


@security_005.get("/users/me/items/")
async def read_own_items(current_user: Annotated[User, Security(get_current_active_user_005, scopes=["items"])]):
    return [{"item_id": "Foo", "owner": current_user.username}]


@security_005.get("/status/")
async def read_system_status(current_user: Annotated[User, Depends(get_current_user_005)]):
    return {"status": "ok"}


# docs_src/dependencies/tutorial007, 008 and 010 as their upstream tests run
# them (tests/test_tutorial/test_dependencies/test_tutorial007.py, 008, 010):
# an app reading the dependency, with the session classes the tutorials leave
# undefined patched in (fakes in place of Mocks: a name, and `close` logged).
# Twins: tests/apps/Dependencies007.lean, 008.lean, 010.lean.
def fake_resource(name, log):
    class Fake:
        def __str__(self):
            return name

        def close(self, *others):
            log.append(f"close {name}" + "".join(f" after {o}" for o in others))
    return Fake


def mock_dependency_app(module, dependency, patches):
    mod = importlib.import_module("docs_src.dependencies." + module)
    log = []
    for attr, name in patches.items():
        fake = fake_resource(name, log)
        setattr(mod, attr, fake if attr[0].isupper() else (lambda fake=fake: fake()))
    app = FastAPI()

    @app.get("/")
    def read_root(c: Annotated[Any, Depends(getattr(mod, dependency))]):
        return {"c": str(c)}

    @app.get("/events")
    def get_events():
        out = list(log)
        log.clear()
        return out
    return app


dependencies_007 = mock_dependency_app("tutorial007_py310", "get_db", {"DBSession": "db"})
dependencies_008 = mock_dependency_app("tutorial008_py310", "dependency_c",
                                       {"generate_dep_a": "a", "generate_dep_b": "b", "generate_dep_c": "c"})
dependencies_010 = mock_dependency_app("tutorial010_py310", "get_db", {"DBSession": "db"})


# docs_src/security/tutorial004_an_py310.py with its argon2 hash and its JWT
# replaced by fakes ("fakehashed" + password; the token "sub=<name>", a
# payload of key=value pairs), twin of tests/apps/Security004.lean. Alice,
# whom test_token_inactive_user patches in, is in the database throughout.
security_004 = FastAPI()

fake_users_db_004 = {
    "johndoe": {"username": "johndoe", "full_name": "John Doe", "email": "johndoe@example.com",
                "hashed_password": "fakehashedsecret", "disabled": False},
    "alice": {"username": "alice", "full_name": "Alice Wonderson", "email": "alice@example.com",
              "hashed_password": "fakehashedsecretalice", "disabled": True},
}

oauth2_scheme_004 = OAuth2PasswordBearer(tokenUrl="token")


class InvalidTokenError(Exception):
    pass


def fake_decode(token):
    payload = {}
    for part in token.split("&"):
        k, sep, v = part.partition("=")
        if not sep:
            raise InvalidTokenError
        payload[k] = v
    return payload


def authenticate_user_004(db, username, password):
    user = get_user_005(db, username)
    if not user or "fakehashed" + password != user.hashed_password:
        return False
    return user


async def get_current_user_004(token: Annotated[str, Depends(oauth2_scheme_004)]):
    credentials_exception = HTTPException(
        status_code=401, detail="Could not validate credentials", headers={"WWW-Authenticate": "Bearer"})
    try:
        payload = fake_decode(token)
        username = payload.get("sub")
        if username is None:
            raise credentials_exception
    except InvalidTokenError:
        raise credentials_exception
    user = get_user_005(fake_users_db_004, username=username)
    if user is None:
        raise credentials_exception
    return user


async def get_current_active_user_004(current_user: Annotated[User, Depends(get_current_user_004)]):
    if current_user.disabled:
        raise HTTPException(status_code=400, detail="Inactive user")
    return current_user


@security_004.post("/token")
async def login_for_access_token(form_data: Annotated[OAuth2PasswordRequestForm, Depends()]) -> Token:
    user = authenticate_user_004(fake_users_db_004, form_data.username, form_data.password)
    if not user:
        raise HTTPException(status_code=401, detail="Incorrect username or password",
                            headers={"WWW-Authenticate": "Bearer"})
    return Token(access_token="sub=" + user.username, token_type="bearer")


@security_004.get("/users/me/")
async def read_users_me(current_user: Annotated[User, Depends(get_current_active_user_004)]) -> User:
    return current_user


@security_004.get("/users/me/items/")
async def read_own_items(current_user: Annotated[User, Depends(get_current_active_user_004)]):
    return [{"item_id": "Foo", "owner": current_user.username}]


# The review cases for overrides and application dependencies, twin of
# tests/apps/DependencyOverridesTyped.lean: an override of a dependency whose
# value has no JSON form, overrides applied inside an override's own tree,
# and an application dependency shared with the route through one cache.
class Db:
    def __init__(self, name):
        self.name = name


def typed_overrides_app(override):
    app = FastAPI()

    def get_db():
        return Db("prod")

    def get_test_db():
        return Db("test")

    def name_dep():
        return "orig"

    def get_user():
        return "alice"

    def get_bob():
        return "bob"

    def get_name(user: Annotated[str, Depends(get_user)]):
        return "override:" + user

    @app.get("/db")
    def read_db(db: Annotated[Db, Depends(get_db)]):
        return {"db": db.name}

    @app.get("/name")
    def read_name(n: Annotated[str, Depends(name_dep)]):
        return {"name": n}

    if override:
        app.dependency_overrides[get_db] = get_test_db
        app.dependency_overrides[name_dep] = get_name
        app.dependency_overrides[get_user] = get_bob
    return app


calls_holder = {"calls": 0}


def count_call():
    calls_holder["calls"] += 1
    return calls_holder["calls"]


shared_cache_app = FastAPI(dependencies=[Depends(count_call)])


@shared_cache_app.get("/count")
def read_count(n: Annotated[int, Depends(count_call)]):
    return {"count": n, "calls": calls_holder["calls"]}


@shared_cache_app.post("/reset", include_in_schema=False)
def reset_calls():
    calls_holder["calls"] = 0


# tests/test_dependency_cache.py resets its counter in each test; here a
# request does, outside the schema (twin: the Lean app's /reset).
dependency_cache = upstream_test("test_dependency_cache")
_cache_module = sys.modules["tests.test_dependency_cache"]


@dependency_cache.post("/reset", include_in_schema=False)
def reset_counter():
    _cache_module.counter_holder["counter"] = 0


FIXTURES = {
    "first_steps_001": tutorial("first_steps.tutorial001_py310"),
    "path_params_002": tutorial("path_params.tutorial002_py310"),
    "path_params_004": tutorial("path_params.tutorial004_py310"),
    "query_params_001": tutorial("query_params.tutorial001_py310"),
    "query_params_003": tutorial("query_params.tutorial003_py310"),
    "query_params_005": tutorial("query_params.tutorial005_py310"),
    "body_001": tutorial("body.tutorial001_py310"),
    "body_004": tutorial("body.tutorial004_py310"),
    "handling_errors_001": tutorial("handling_errors.tutorial001_py310"),
    "handling_errors_002": tutorial("handling_errors.tutorial002_py310"),
    "qpsv_003": tutorial("query_params_str_validations.tutorial003_an_py310"),
    "ppnv_001": tutorial("path_params_numeric_validations.tutorial001_an_py310"),
    "ppnv_006": tutorial("path_params_numeric_validations.tutorial006_an_py310"),
    "header_params_001": tutorial("header_params.tutorial001_an_py310"),
    "header_params_002": tutorial("header_params.tutorial002_an_py310"),
    "cookie_params_001": tutorial("cookie_params.tutorial001_an_py310"),
    "demo": demo,
    "response_model": rm,
    "bench": bench_app,
    "dependencies_001": tutorial("dependencies.tutorial001_an_py310"),
    "dependencies_002": tutorial("dependencies.tutorial002_an_py310"),
    "dependencies_004": tutorial("dependencies.tutorial004_an_py310"),
    "dependencies_005": tutorial("dependencies.tutorial005_an_py310"),
    "dependencies_006": tutorial("dependencies.tutorial006_an_py310"),
    "dependencies_008b": tutorial("dependencies.tutorial008b_an_py310"),
    "dependencies_008c": tutorial("dependencies.tutorial008c_an_py310"),
    "dependencies_008d": tutorial("dependencies.tutorial008d_an_py310"),
    "dependencies_008e": tutorial("dependencies.tutorial008e_an_py310"),
    "dependencies_011": tutorial("dependencies.tutorial011_an_py310"),
    "dependencies_012": tutorial("dependencies.tutorial012_an_py310"),
    "security_001": tutorial("security.tutorial001_an_py310"),
    "security_002": tutorial("security.tutorial002_an_py310"),
    "security_003": tutorial("security.tutorial003_an_py310"),
    "security_005": security_005,
    "security_006": tutorial("security.tutorial006_an_py310"),
    "security_007": tutorial("security.tutorial007_an_py310"),
    "dependency_cache": dependency_cache,
    "dependency_duplicates": upstream_test("test_dependency_duplicates"),
    "dependency_yield": deps_yield,
    "dependency_overrides": overrides_app(None),
    "dependency_overrides_simple": overrides_app("simple"),
    "dependency_overrides_with_sub": overrides_app("with_sub"),
    "dependencies_007": dependencies_007,
    "dependencies_008": dependencies_008,
    "dependencies_010": dependencies_010,
    "security_004": security_004,
    "dependency_overrides_typed": typed_overrides_app(False),
    "dependency_overrides_typed_on": typed_overrides_app(True),
    "dependency_shared_cache": shared_cache_app,
    "request_forms_001": tutorial("request_forms.tutorial001_an_py310"),
    "request_files_001": tutorial("request_files.tutorial001_an_py310"),
    "request_files_001_02": tutorial("request_files.tutorial001_02_an_py310"),
    "request_files_001_03": tutorial("request_files.tutorial001_03_an_py310"),
    "request_files_002": tutorial("request_files.tutorial002_an_py310"),
    "request_files_003": tutorial("request_files.tutorial003_an_py310"),
    "request_forms_and_files_001": tutorial("request_forms_and_files.tutorial001_an_py310"),
    "request_form_models_001": tutorial("request_form_models.tutorial001_an_py310"),
    # request_form_models.tutorial002 (`model_config = {"extra": "forbid"}`) waits
    # on lean-pydantic's extra="forbid" (no ConfigDict extra yet).
    "security_api_key_query": upstream_test("test_security_api_key_query"),
    "security_api_key_header_optional": upstream_test("test_security_api_key_header_optional"),
    "security_api_key_cookie": upstream_test("test_security_api_key_cookie"),
    "security_http_base": upstream_test("test_security_http_base"),
    "security_http_bearer_optional": upstream_test("test_security_http_bearer_optional"),
    "security_http_digest": upstream_test("test_security_http_digest"),
    "security_http_basic_realm": upstream_test("test_security_http_basic_realm"),
    "security_openid_connect_optional": upstream_test("test_security_openid_connect_optional"),
    "security_oauth2_authorization_code_bearer": upstream_test("test_security_oauth2_authorization_code_bearer"),
}

J = {"content-type": "application/json"}
F = {"content-type": "application/x-www-form-urlencoded"}
T = "tests/test_tutorial/"
TD = T + "test_dependencies/"
TS = T + "test_security/"
BASIC = "Basic am9objpzZWNyZXQ="  # john:secret
TF = T + "test_request_forms/"
TFI = T + "test_request_files/"
TFF = T + "test_request_forms_and_files/"
TFM = T + "test_request_form_models/"
BOUNDARY = "b0undary"
MPH = {"content-type": "multipart/form-data; boundary=" + BOUNDARY}


def MP(*parts):
    """A multipart/form-data body as httpx sends `files=` and `data=`: each part a
    (name, filename or None, content type or None, content)."""
    out = ""
    for name, filename, ctype, content in parts:
        out += "--" + BOUNDARY + "\r\n" + f'Content-Disposition: form-data; name="{name}"'
        if filename is not None:
            out += f'; filename="{filename}"'
        out += "\r\n"
        if ctype is not None:
            out += f"Content-Type: {ctype}\r\n"
        out += "\r\n" + content + "\r\n"
    return out + "--" + BOUNDARY + "--\r\n"


OCT = "application/octet-stream"
# (fixture, upstream test, method, url, extra headers, body)
SCENARIOS = [
    ("first_steps_001", T + "test_first_steps/test_tutorial001_tutorial002_tutorial003.py::test_get_path", "GET", "/", {}, None),
    ("first_steps_001", "tests/test_application.py::test_get_path", "GET", "/nonexistent", {}, None),
    ("first_steps_001", "tests/test_application.py::test_redoc", "GET", "/redoc", {}, None),
    ("first_steps_001", "tests/test_application.py::test_swagger_ui", "GET", "/docs", {}, None),
    ("first_steps_001", "tests/test_application.py::test_swagger_ui_oauth2_redirect", "GET", "/docs/oauth2-redirect", {}, None),
    ("first_steps_001", "tests/test_application.py::test_get_path", "POST", "/", {}, None),
    ("path_params_002", T + "test_path_params/test_tutorial002.py::test_get_items", "GET", "/items/1", {}, None),
    ("path_params_002", T + "test_path_params/test_tutorial002.py::test_get_items_invalid_id", "GET", "/items/item1", {}, None),
    ("path_params_002", "tests/test_path.py::test_path_int_foobar", "GET", "/items/1.5", {}, None),
    ("path_params_002", "tests/test_path.py::test_path_int_42", "GET", "/items/0042", {}, None),
    ("path_params_004", T + "test_path_params/test_tutorial004.py::test_file_path", "GET", "/files/home/johndoe/myfile.txt", {}, None),
    ("path_params_004", T + "test_path_params/test_tutorial004.py::test_root_file_path", "GET", "/files//home/johndoe/myfile.txt", {}, None),
    ("query_params_001", T + "test_query_params/test_tutorial001.py::test_read_user_item", "GET", "/items/", {}, None),
    ("query_params_001", T + "test_query_params/test_tutorial001.py::test_read_user_item", "GET", "/items/?skip=1", {}, None),
    ("query_params_001", T + "test_query_params/test_tutorial001.py::test_read_user_item", "GET", "/items/?skip=1&limit=1", {}, None),
    ("query_params_001", "tests/test_query.py::test_query_int_query_baz", "GET", "/items/?skip=baz&limit=1.5", {}, None),
    ("query_params_003", T + "test_query_params/test_tutorial003.py::test_read_user_item", "GET", "/items/foo?short=1", {}, None),
    ("query_params_003", T + "test_query_params/test_tutorial003.py::test_read_user_item", "GET", "/items/foo?short=True", {}, None),
    ("query_params_003", T + "test_query_params/test_tutorial003.py::test_read_user_item", "GET", "/items/foo?short=yes&q=bar", {}, None),
    ("query_params_003", T + "test_query_params/test_tutorial003.py::test_read_user_item", "GET", "/items/foo?short=off", {}, None),
    ("query_params_003", T + "test_query_params/test_tutorial003.py::test_read_user_item", "GET", "/items/foo?short=maybe", {}, None),
    ("query_params_005", T + "test_query_params/test_tutorial005.py::test_foo_needy_very", "GET", "/items/foo?needy=very", {}, None),
    ("query_params_005", T + "test_query_params/test_tutorial005.py::test_foo_no_needy", "GET", "/items/foo", {}, None),
    ("query_params_005", "tests/test_query.py::test_query_query_baz", "GET", "/items/foo?needy=a&needy=b", {}, None),
    ("query_params_005", "tests/test_query.py::test_query_query_baz", "GET", "/items/foo?needy=", {}, None),
    ("body_001", T + "test_body/test_tutorial001.py::test_body_float", "POST", "/items/", J, '{"name": "Foo", "price": 50.5}'),
    ("body_001", T + "test_body/test_tutorial001.py::test_post_with_str_float", "POST", "/items/", J, '{"name": "Foo", "price": "50.5"}'),
    ("body_001", T + "test_body/test_tutorial001.py::test_post_with_str_float_description_tax", "POST", "/items/", J, '{"name": "Foo", "price": "50.5", "description": "Some Foo", "tax": 0.3}'),
    ("body_001", T + "test_body/test_tutorial001.py::test_post_with_only_name", "POST", "/items/", J, '{"name": "Foo"}'),
    ("body_001", T + "test_body/test_tutorial001.py::test_post_with_only_name_price", "POST", "/items/", J, '{"name": "Foo", "price": "twenty"}'),
    ("body_001", T + "test_body/test_tutorial001.py::test_post_with_no_data", "POST", "/items/", J, '{}'),
    ("body_001", T + "test_body/test_tutorial001.py::test_post_with_none", "POST", "/items/", J, 'null'),
    ("body_001", T + "test_body/test_tutorial001.py::test_post_with_none", "POST", "/items/", {}, None),
    ("body_001", T + "test_body/test_tutorial001.py::test_post_broken_body", "POST", "/items/", J, '{some broken json}'),
    ("body_001", T + "test_body/test_tutorial001.py::test_post_form_for_json", "POST", "/items/", {"content-type": "application/x-www-form-urlencoded"}, 'name=Foo&price=50.5'),
    ("body_001", T + "test_body/test_tutorial001.py::test_explicit_content_type", "POST", "/items/", {"Content-Type": "application/json"}, '{"name": "Foo", "price": 50.5}'),
    ("body_001", T + "test_body/test_tutorial001.py::test_geo_json", "POST", "/items/", {"Content-Type": "application/geo+json"}, '{"name": "Foo", "price": 50.5}'),
    ("body_001", T + "test_body/test_tutorial001.py::test_no_content_type_json", "POST", "/items/", {}, '{"name": "Foo", "price": 50.5}'),
    ("body_001", T + "test_body/test_tutorial001.py::test_wrong_headers", "POST", "/items/", {"Content-Type": "text/plain"}, '{"name": "Foo", "price": 50.5}'),
    ("body_001", T + "test_body/test_tutorial001.py::test_wrong_headers", "POST", "/items/", {"Content-Type": "application/geo+json-seq"}, '{"name": "Foo", "price": 50.5}'),
    ("body_001", T + "test_body/test_tutorial001.py::test_wrong_headers", "POST", "/items/", {"Content-Type": "application/not-really-json"}, '{"name": "Foo", "price": 50.5}'),
    ("body_001", T + "test_body/test_tutorial001.py::test_post_broken_body", "POST", "/items/", J, '[1, 2,]'),
    ("body_001", T + "test_body/test_tutorial001.py::test_post_broken_body", "POST", "/items/", J, '{"name": "Foo", "price": 50.5} x'),
    ("body_001", T + "test_body/test_tutorial001.py::test_post_broken_body", "POST", "/items/", J, '[1]'),
    ("body_001", T + "test_body/test_tutorial001.py::test_post_broken_body", "POST", "/items/", J, '"Foo"'),
    ("body_004", T + "test_body/test_tutorial004.py::test_put_all", "PUT", "/items/123?q=somequery", J, '{"name": "Foo", "price": 50.1, "description": "Some Foo", "tax": 0.3}'),
    ("body_004", T + "test_body/test_tutorial004.py::test_put_only_required", "PUT", "/items/123", J, '{"name": "Foo", "price": 50.1}'),
    ("body_004", T + "test_body/test_tutorial004.py::test_put_with_no_data", "PUT", "/items/123", J, '{}'),
    ("body_004", T + "test_body/test_tutorial004.py::test_put_with_no_data", "PUT", "/items/abc", J, '{"price": "x"}'),
    ("handling_errors_001", T + "test_handling_errors/test_tutorial001.py::test_get_item", "GET", "/items/foo", {}, None),
    ("handling_errors_001", T + "test_handling_errors/test_tutorial001.py::test_get_item_not_found", "GET", "/items/bar", {}, None),
    ("handling_errors_002", T + "test_handling_errors/test_tutorial002.py::test_get_item_header", "GET", "/items-header/foo", {}, None),
    ("handling_errors_002", T + "test_handling_errors/test_tutorial002.py::test_get_item_not_found_header", "GET", "/items-header/bar", {}, None),
    ("qpsv_003", T + "test_query_params_str_validations/test_tutorial003.py::test_query_params_str_validations_no_query", "GET", "/items/", {}, None),
    ("qpsv_003", T + "test_query_params_str_validations/test_tutorial003.py::test_query_params_str_validations_q_query", "GET", "/items/?q=query", {}, None),
    ("qpsv_003", T + "test_query_params_str_validations/test_tutorial003.py::test_query_params_str_validations_q_too_short", "GET", "/items/?q=qu", {}, None),
    ("qpsv_003", T + "test_query_params_str_validations/test_tutorial003.py::test_query_params_str_validations_q_too_long", "GET", "/items/?q=" + "q" * 51, {}, None),
    ("ppnv_001", T + "test_path_params_numeric_validations/test_tutorial001.py::test_read_items", "GET", "/items/42", {}, None),
    ("ppnv_001", T + "test_path_params_numeric_validations/test_tutorial001.py::test_read_items", "GET", "/items/42?item-query=somequery", {}, None),
    ("ppnv_001", T + "test_path_params_numeric_validations/test_tutorial001.py::test_read_items", "GET", "/items/42?q=ignored", {}, None),
    ("ppnv_006", T + "test_path_params_numeric_validations/test_tutorial006.py::test_read_items", "GET", "/items/42?q=somequery&size=5", {}, None),
    ("ppnv_006", T + "test_path_params_numeric_validations/test_tutorial006.py::test_read_items_item_id_less_than_zero", "GET", "/items/-1?q=somequery&size=5", {}, None),
    ("ppnv_006", T + "test_path_params_numeric_validations/test_tutorial006.py::test_read_items_item_id_greater_than_one_thousand", "GET", "/items/1001?q=somequery&size=5", {}, None),
    ("ppnv_006", T + "test_path_params_numeric_validations/test_tutorial006.py::test_read_items_size_too_small", "GET", "/items/1?q=somequery&size=0.0", {}, None),
    ("ppnv_006", T + "test_path_params_numeric_validations/test_tutorial006.py::test_read_items_size_too_large", "GET", "/items/1?q=somequery&size=10.5", {}, None),
    ("ppnv_006", T + "test_path_params_numeric_validations/test_tutorial006.py::test_read_items", "GET", "/items/1001?size=abc", {}, None),
    ("header_params_001", T + "test_header_params/test_tutorial001.py::test", "GET", "/items", {}, None),
    ("header_params_001", T + "test_header_params/test_tutorial001.py::test", "GET", "/items/", {}, None),
    ("header_params_001", T + "test_header_params/test_tutorial001.py::test", "GET", "/items/", {"X-Header": "notvalid"}, None),
    ("header_params_001", T + "test_header_params/test_tutorial001.py::test", "GET", "/items/", {"User-Agent": "FastAPI test"}, None),
    ("header_params_002", T + "test_header_params/test_tutorial002.py::test", "GET", "/items/", {}, None),
    ("header_params_002", T + "test_header_params/test_tutorial002.py::test", "GET", "/items/", {"strange_header": "FastAPI test"}, None),
    ("header_params_002", T + "test_header_params/test_tutorial002.py::test", "GET", "/items/", {"strange-header": "Not really underscore"}, None),
    ("cookie_params_001", T + "test_cookie_params/test_tutorial001.py::test", "GET", "/items/", {"cookie": "ads_id=ads_track; session=cookiesession"}, None),
    ("cookie_params_001", T + "test_cookie_params/test_tutorial001.py::test", "GET", "/items/", {"cookie": "session=cookiesession"}, None),
    ("cookie_params_001", T + "test_cookie_params/test_tutorial001.py::test", "GET", "/items/", {"cookie": 'ads_id="a\\"b"; x=1'}, None),
    ("cookie_params_001", T + "test_cookie_params/test_tutorial001.py::test", "GET", "/items", {}, None),
    ("demo", "plan: milestone 1 curl checks", "GET", "/items/42?q=x", {}, None),
    ("demo", "plan: milestone 1 curl checks", "GET", "/items/abc", {}, None),
    ("demo", "plan: milestone 1 curl checks", "PUT", "/items/1", J, '{"price":-1}'),
    ("demo", "plan: milestone 1 curl checks", "PUT", "/items/1", J, '{"name":"x","price":1}'),
    ("demo", "plan: milestone 1 curl checks", "PUT", "/items/1", J, '{"name":"' + "n" * 51 + '","price":2.5,"tax":0}'),
    ("demo", "plan: milestone 1 curl checks", "GET", "/stock/foo", {}, None),
    ("demo", "plan: milestone 1 curl checks", "GET", "/stock/bar", {}, None),
    ("demo", "plan: milestone 1 curl checks", "GET", "/docs", {}, None),
    ("demo", "plan: milestone 1 curl checks", "GET", "/redoc", {}, None),
    ("response_model", T + "test_response_model/test_tutorial003.py::test_post_user", "GET", "/public", {}, None),
    ("response_model", T + "test_response_model/test_tutorial003_01.py::test_post_user", "GET", "/typed", {}, None),
    ("response_model", "tests/test_response_model_as_return_annotation.py::test_response_model_no_annotation_return_same_model", "GET", "/count", {}, None),
    ("response_model", "tests/test_response_code_no_body.py::test_get_response", "POST", "/created", J, '{"name": "a", "price": "3"}'),
    ("response_model", "tests/test_response_code_no_body.py::test_get_response", "DELETE", "/zap", {}, None),
    ("response_model", "tests/test_response_code_no_body.py::test_get_response", "DELETE", "/zap", J, '{"name": "a", "price": 3}'),
    ("response_model", "tests/test_router_events.py (405 on a partial match)", "PUT", "/multi", {}, None),
    ("response_model", "tests/test_router_events.py (405 on a partial match)", "HEAD", "/multi", {}, None),
    ("response_model", "tests/test_router_events.py (405 on a partial match)", "HEAD", "/public", {}, None),
    ("response_model", "critic review of b6n01b9wts1z (non-finite input in a 422)", "POST", "/counted", J, '{"n": Infinity}'),
    ("response_model", "critic review of b6n01b9wts1z (non-finite input in a 422)", "POST", "/counted", J, '{"n": NaN}'),
    ("demo", "wide object body (lean-json bca7cc0 parse)", "PUT", "/items/1", J,
     '{"name":"x","price":2,' + ",".join(f'"k{i}":{i}' for i in range(5000)) + '}'),
    ("demo", "critic review of b6n01b9wts1z (float price)", "PUT", "/items/1", J, '{"name":"x","price":Infinity}'),
    ("demo", "critic review of b6n01b9wts1z (float price)", "PUT", "/items/1", J, '{"name":"x","price":1e400}'),
    ("demo", "critic review of b6n01b9wts1z (float price)", "PUT", "/items/1", J, '{"name":"x","price":12345678901234567890}'),
    # milestone 3: dependencies
    ("dependencies_001", TD + "test_tutorial001_tutorial001_02.py::test_get", "GET", "/items", {}, None),
    ("dependencies_001", TD + "test_tutorial001_tutorial001_02.py::test_get", "GET", "/items?q=foo", {}, None),
    ("dependencies_001", TD + "test_tutorial001_tutorial001_02.py::test_get", "GET", "/items?q=foo&skip=5", {}, None),
    ("dependencies_001", TD + "test_tutorial001_tutorial001_02.py::test_get", "GET", "/items?q=foo&skip=5&limit=30", {}, None),
    ("dependencies_001", TD + "test_tutorial001_tutorial001_02.py::test_get", "GET", "/users", {}, None),
    ("dependencies_001", "tests/test_dependency_class.py (errors of a dependency's parameters)", "GET", "/items/?skip=x&limit=y", {}, None),
    ("dependencies_002", TD + "test_tutorial002_tutorial003_tutorial004.py::test_get", "GET", "/items", {}, None),
    ("dependencies_002", TD + "test_tutorial002_tutorial003_tutorial004.py::test_get", "GET", "/items?q=foo", {}, None),
    ("dependencies_002", TD + "test_tutorial002_tutorial003_tutorial004.py::test_get", "GET", "/items?q=foo&skip=1", {}, None),
    ("dependencies_002", TD + "test_tutorial002_tutorial003_tutorial004.py::test_get", "GET", "/items?q=bar&limit=2", {}, None),
    ("dependencies_002", TD + "test_tutorial002_tutorial003_tutorial004.py::test_get", "GET", "/items?q=bar&skip=1&limit=1", {}, None),
    ("dependencies_002", TD + "test_tutorial002_tutorial003_tutorial004.py::test_get", "GET", "/items?limit=1&q=bar&skip=1", {}, None),
    ("dependencies_004", TD + "test_tutorial002_tutorial003_tutorial004.py::test_get", "GET", "/items/?q=bar&skip=1&limit=1", {}, None),
    ("dependencies_005", TD + "test_tutorial005.py::test_get", "GET", "/items", {}, None),
    ("dependencies_005", TD + "test_tutorial005.py::test_get", "GET", "/items/?q=foo", {}, None),
    ("dependencies_005", TD + "test_tutorial005.py::test_get", "GET", "/items/", {"cookie": "last_query=cookiequery"}, None),
    ("dependencies_005", TD + "test_tutorial005.py::test_get", "GET", "/items/?q=foo", {"cookie": "last_query=cookiequery"}, None),
    ("dependencies_006", TD + "test_tutorial006.py::test_get_no_headers", "GET", "/items/", {}, None),
    ("dependencies_006", TD + "test_tutorial006.py::test_get_invalid_one_header", "GET", "/items/", {"X-Token": "invalid"}, None),
    ("dependencies_006", TD + "test_tutorial006.py::test_get_invalid_second_header", "GET", "/items/", {"X-Token": "fake-super-secret-token", "X-Key": "invalid"}, None),
    ("dependencies_006", TD + "test_tutorial006.py::test_get_valid_headers", "GET", "/items/", {"X-Token": "fake-super-secret-token", "X-Key": "fake-super-secret-key"}, None),
    ("dependencies_008b", TD + "test_tutorial008b.py::test_get_no_item", "GET", "/items/foo", {}, None),
    ("dependencies_008b", TD + "test_tutorial008b.py::test_owner_error", "GET", "/items/plumbus", {}, None),
    ("dependencies_008b", TD + "test_tutorial008b.py::test_get_item", "GET", "/items/portal-gun", {}, None),
    ("dependencies_008c", TD + "test_tutorial008c.py::test_get_no_item", "GET", "/items/foo", {}, None),
    ("dependencies_008c", TD + "test_tutorial008c.py::test_get", "GET", "/items/plumbus", {}, None),
    ("dependencies_008c", TD + "test_tutorial008c.py::test_fastapi_error", "GET", "/items/portal-gun", {}, None),
    ("dependencies_008d", TD + "test_tutorial008d.py::test_get_no_item", "GET", "/items/foo", {}, None),
    ("dependencies_008d", TD + "test_tutorial008d.py::test_get", "GET", "/items/plumbus", {}, None),
    ("dependencies_008d", TD + "test_tutorial008d.py::test_internal_error", "GET", "/items/portal-gun", {}, None),
    ("dependencies_008e", TD + "test_tutorial008e.py::test_get_users_me", "GET", "/users/me", {}, None),
    ("dependencies_011", TD + "test_tutorial011.py::test_get", "GET", "/query-checker/", {}, None),
    ("dependencies_011", TD + "test_tutorial011.py::test_get", "GET", "/query-checker/?q=qwerty", {}, None),
    ("dependencies_011", TD + "test_tutorial011.py::test_get", "GET", "/query-checker/?q=foobar", {}, None),
    ("dependencies_012", TD + "test_tutorial012.py::test_get_no_headers_items", "GET", "/items/", {}, None),
    ("dependencies_012", TD + "test_tutorial012.py::test_get_no_headers_users", "GET", "/users/", {}, None),
    ("dependencies_012", TD + "test_tutorial012.py::test_get_invalid_one_header_items", "GET", "/items/", {"X-Token": "invalid"}, None),
    ("dependencies_012", TD + "test_tutorial012.py::test_get_invalid_second_header_users", "GET", "/users/", {"X-Token": "fake-super-secret-token", "X-Key": "invalid"}, None),
    ("dependencies_012", TD + "test_tutorial012.py::test_get_valid_headers_items", "GET", "/items/", {"X-Token": "fake-super-secret-token", "X-Key": "fake-super-secret-key"}, None),
    ("dependencies_012", TD + "test_tutorial012.py::test_get_valid_headers_users", "GET", "/users/", {"X-Token": "fake-super-secret-token", "X-Key": "fake-super-secret-key"}, None),
    ("dependency_cache", "tests/test_dependency_cache.py::test_normal_counter", "POST", "/reset", {}, None),
    ("dependency_cache", "tests/test_dependency_cache.py::test_normal_counter", "GET", "/counter/", {}, None),
    ("dependency_cache", "tests/test_dependency_cache.py::test_normal_counter", "GET", "/counter/", {}, None),
    ("dependency_cache", "tests/test_dependency_cache.py::test_sub_counter", "POST", "/reset", {}, None),
    ("dependency_cache", "tests/test_dependency_cache.py::test_sub_counter", "GET", "/sub-counter/", {}, None),
    ("dependency_cache", "tests/test_dependency_cache.py::test_sub_counter", "GET", "/sub-counter/", {}, None),
    ("dependency_cache", "tests/test_dependency_cache.py::test_sub_counter_no_cache", "POST", "/reset", {}, None),
    ("dependency_cache", "tests/test_dependency_cache.py::test_sub_counter_no_cache", "GET", "/sub-counter-no-cache/", {}, None),
    ("dependency_cache", "tests/test_dependency_cache.py::test_sub_counter_no_cache", "GET", "/sub-counter-no-cache/", {}, None),
    ("dependency_cache", "tests/test_dependency_cache.py::test_security_cache", "POST", "/reset", {}, None),
    ("dependency_cache", "tests/test_dependency_cache.py::test_security_cache", "GET", "/scope-counter", {}, None),
    ("dependency_cache", "tests/test_dependency_cache.py::test_security_cache", "GET", "/scope-counter", {}, None),
    ("dependency_duplicates", "tests/test_dependency_duplicates.py::test_no_duplicates_invalid", "POST", "/no-duplicates", J, '{"item": {"data": "myitem"}}'),
    ("dependency_duplicates", "tests/test_dependency_duplicates.py::test_no_duplicates", "POST", "/no-duplicates", J, '{"item": {"data": "myitem"}, "item2": {"data": "myitem2"}}'),
    ("dependency_duplicates", "tests/test_dependency_duplicates.py::test_duplicates", "POST", "/with-duplicates", J, '{"data": "myitem"}'),
    ("dependency_duplicates", "tests/test_dependency_duplicates.py::test_sub_duplicates", "POST", "/with-duplicates-sub", J, '{"data": "myitem"}'),
    ("dependency_duplicates", "tests/test_dependency_duplicates.py (errors of both uses)", "POST", "/with-duplicates", J, '{}'),
    ("dependency_duplicates", "tests/test_dependency_duplicates.py (errors of both uses)", "POST", "/no-duplicates", J, '{}'),
    ("dependency_yield", "tests/test_dependency_yield_scope.py (exit order)", "GET", "/run", {}, None),
    ("dependency_yield", "tests/test_dependency_yield_scope.py (exit order)", "GET", "/events", {}, None),
    ("dependency_yield", "tests/test_dependency_contextmanager.py (an exception reaches every exit)", "GET", "/fail", {}, None),
    ("dependency_yield", "tests/test_dependency_contextmanager.py (an exception reaches every exit)", "GET", "/events", {}, None),
    ("dependency_yield", "tests/test_dependency_contextmanager.py (a validation error reaches every exit)", "GET", "/invalid?n=x", {}, None),
    ("dependency_yield", "tests/test_dependency_contextmanager.py (a validation error reaches every exit)", "GET", "/events", {}, None),
    ("dependency_overrides", "tests/test_dependency_overrides.py::test_main_depends", "GET", "/main-depends/", {}, None),
    ("dependency_overrides", "tests/test_dependency_overrides.py::test_main_depends_q_foo", "GET", "/main-depends/?q=foo", {}, None),
    ("dependency_overrides", "tests/test_dependency_overrides.py::test_main_depends_q_foo_skip_100_limit_200", "GET", "/main-depends/?q=foo&skip=100&limit=200", {}, None),
    ("dependency_overrides", "tests/test_dependency_overrides.py::test_decorator_depends", "GET", "/decorator-depends/", {}, None),
    ("dependency_overrides", "tests/test_dependency_overrides.py::test_decorator_depends_q_foo", "GET", "/decorator-depends/?q=foo", {}, None),
    ("dependency_overrides_simple", "tests/test_dependency_overrides.py::test_override_simple", "GET", "/main-depends/", {}, None),
    ("dependency_overrides_simple", "tests/test_dependency_overrides.py::test_override_simple", "GET", "/main-depends/?q=foo", {}, None),
    ("dependency_overrides_simple", "tests/test_dependency_overrides.py::test_override_simple", "GET", "/decorator-depends/", {}, None),
    ("dependency_overrides_with_sub", "tests/test_dependency_overrides.py::test_override_with_sub_main_depends", "GET", "/main-depends/", {}, None),
    ("dependency_overrides_with_sub", "tests/test_dependency_overrides.py::test_override_with_sub_main_depends_k_bar", "GET", "/main-depends/?k=bar", {}, None),
    ("dependency_overrides_with_sub", "tests/test_dependency_overrides.py::test_override_with_sub_decorator_depends", "GET", "/decorator-depends/?k=bar", {}, None),
    ("dependencies_007", TD + "test_tutorial007.py::test_get_db", "GET", "/", {}, None),
    ("dependencies_007", TD + "test_tutorial007.py::test_get_db (close called once)", "GET", "/events", {}, None),
    ("dependencies_008", TD + "test_tutorial008.py::test_get_db", "GET", "/", {}, None),
    ("dependencies_008", TD + "test_tutorial008.py::test_get_db (closes in reverse)", "GET", "/events", {}, None),
    ("dependencies_010", TD + "test_tutorial010.py::test_get_db", "GET", "/", {}, None),
    ("dependencies_010", TD + "test_tutorial010.py::test_get_db (closed after)", "GET", "/events", {}, None),
    ("dependency_overrides_typed", "tests/test_dependency_overrides.py (a value without a JSON form)", "GET", "/db", {}, None),
    ("dependency_overrides_typed", "tests/test_dependency_overrides.py (no override)", "GET", "/name", {}, None),
    ("dependency_overrides_typed_on", "tests/test_dependency_overrides.py (a value without a JSON form)", "GET", "/db", {}, None),
    ("dependency_overrides_typed_on", "tests/test_dependency_overrides.py (overrides inside an override)", "GET", "/name", {}, None),
    ("dependency_shared_cache", "tests/test_dependency_cache.py (application and route dependencies share one cache)", "POST", "/reset", {}, None),
    ("dependency_shared_cache", "tests/test_dependency_cache.py (application and route dependencies share one cache)", "GET", "/count", {}, None),
    ("dependency_shared_cache", "tests/test_dependency_cache.py (application and route dependencies share one cache)", "GET", "/count", {}, None),
    # milestone 4: forms and files
    ("request_forms_001", TF + "test_tutorial001.py::test_post_body_form", "POST", "/login/", F, "username=Foo&password=secret"),
    ("request_forms_001", TF + "test_tutorial001.py::test_post_body_form_no_password", "POST", "/login/", F, "username=Foo"),
    ("request_forms_001", TF + "test_tutorial001.py::test_post_body_form_no_username", "POST", "/login/", F, "password=secret"),
    ("request_forms_001", TF + "test_tutorial001.py::test_post_body_form_no_data", "POST", "/login/", {}, None),
    ("request_forms_001", TF + "test_tutorial001.py::test_post_body_json", "POST", "/login/", J, '{"username": "Foo", "password": "secret"}'),
    ("request_forms_001", TF + "test_tutorial001.py (a multipart form)", "POST", "/login/", MPH, MP(("username", None, None, "Foo"), ("password", None, None, "secret"))),
    ("request_forms_001", TF + "test_tutorial001.py (an empty field is missing)", "POST", "/login/", F, "username=&password=secret"),
    ("request_forms_001", TF + "test_tutorial001.py (a file where a field goes)", "POST", "/login/", MPH, MP(("username", "u.txt", "text/plain", "Foo"), ("password", None, None, "secret"))),
    ("request_files_001", TFI + "test_tutorial001.py::test_post_form_no_body", "POST", "/files/", {}, None),
    ("request_files_001", TFI + "test_tutorial001.py::test_post_body_json", "POST", "/files/", J, '{"file": "Foo"}'),
    ("request_files_001", TFI + "test_tutorial001.py::test_post_file", "POST", "/files/", MPH, MP(("file", "test.txt", OCT, "<file content>"))),
    ("request_files_001", TFI + "test_tutorial001.py::test_post_large_file", "POST", "/files/", MPH, MP(("file", "test.txt", OCT, "x" * (2**16 + 1)))),
    ("request_files_001", TFI + "test_tutorial001.py::test_post_upload_file", "POST", "/uploadfile/", MPH, MP(("file", "test.txt", OCT, "<file content>"))),
    ("request_files_001", TFI + "test_tutorial001.py (bytes from a text field)", "POST", "/files/", MPH, MP(("file", None, None, "héllo"))),
    ("request_files_001", TFI + "test_tutorial001.py (an UploadFile from a text field)", "POST", "/uploadfile/", MPH, MP(("file", None, None, "hello"))),
    ("request_files_001", TFI + "test_tutorial001.py (an empty file)", "POST", "/files/", MPH, MP(("file", "e.txt", OCT, ""))),
    ("request_files_001", TFI + "test_tutorial001.py (no upload)", "POST", "/uploadfile/", {}, None),
    ("request_files_001", TFI + "test_tutorial001.py (malformed multipart)", "POST", "/files/", MPH, "garbage"),
    ("request_files_001", TFI + "test_tutorial001.py (no boundary)", "POST", "/files/", {"content-type": "multipart/form-data"}, MP(("file", "t", OCT, "x"))),
    ("request_files_001_02", TFI + "test_tutorial001_02.py::test_post_form_no_body", "POST", "/files/", {}, None),
    ("request_files_001_02", TFI + "test_tutorial001_02.py::test_post_uploadfile_no_body", "POST", "/uploadfile/", {}, None),
    ("request_files_001_02", TFI + "test_tutorial001_02.py::test_post_file", "POST", "/files/", MPH, MP(("file", "test.txt", OCT, "<file content>"))),
    ("request_files_001_02", TFI + "test_tutorial001_02.py::test_post_upload_file", "POST", "/uploadfile/", MPH, MP(("file", "test.txt", OCT, "<file content>"))),
    ("request_files_001_03", TFI + "test_tutorial001_03.py::test_post_file", "POST", "/files/", MPH, MP(("file", "test.txt", OCT, "<file content>"))),
    ("request_files_001_03", TFI + "test_tutorial001_03.py::test_post_upload_file", "POST", "/uploadfile/", MPH, MP(("file", "test.txt", OCT, "<file content>"))),
    ("request_files_002", TFI + "test_tutorial002.py::test_post_form_no_body", "POST", "/files/", {}, None),
    ("request_files_002", TFI + "test_tutorial002.py::test_post_body_json", "POST", "/files/", J, '{"file": "Foo"}'),
    ("request_files_002", TFI + "test_tutorial002.py::test_post_files", "POST", "/files/", MPH, MP(("files", "test.txt", OCT, "<file content>"), ("files", "test2.txt", OCT, "<file content2>"))),
    ("request_files_002", TFI + "test_tutorial002.py::test_post_upload_file", "POST", "/uploadfiles/", MPH, MP(("files", "test.txt", OCT, "<file content>"), ("files", "test2.txt", OCT, "<file content2>"))),
    ("request_files_002", TFI + "test_tutorial002.py (one text value among the uploads)", "POST", "/uploadfiles/", MPH, MP(("files", None, None, "hello"), ("files", "test2.txt", OCT, "x"))),
    ("request_files_002", TFI + "test_tutorial002.py (a text value among bytes files)", "POST", "/files/", MPH, MP(("files", None, None, "hello"), ("files", "test2.txt", OCT, "x"))),
    ("request_files_002", TFI + "test_tutorial002.py::test_get_root", "GET", "/", {}, None),
    ("request_files_003", TFI + "test_tutorial003.py::test_post_files", "POST", "/files/", MPH, MP(("files", "test.txt", OCT, "<file content>"), ("files", "test2.txt", OCT, "<file content2>"))),
    ("request_files_003", TFI + "test_tutorial003.py::test_post_upload_file", "POST", "/uploadfiles/", MPH, MP(("files", "test.txt", OCT, "<file content>"), ("files", "test2.txt", OCT, "<file content2>"))),
    ("request_files_003", TFI + "test_tutorial003.py::test_get_root", "GET", "/", {}, None),
    ("request_forms_and_files_001", TFF + "test_tutorial001.py::test_post_form_no_body", "POST", "/files/", {}, None),
    ("request_forms_and_files_001", TFF + "test_tutorial001.py::test_post_form_no_file", "POST", "/files/", F, "token=foo"),
    ("request_forms_and_files_001", TFF + "test_tutorial001.py::test_post_body_json", "POST", "/files/", J, '{"file": "Foo", "token": "Bar"}'),
    ("request_forms_and_files_001", TFF + "test_tutorial001.py::test_post_file_no_token", "POST", "/files/", MPH, MP(("file", "test.txt", OCT, "<file content>"))),
    ("request_forms_and_files_001", TFF + "test_tutorial001.py::test_post_files_and_token", "POST", "/files/", MPH, MP(("token", None, None, "foo"), ("file", "test.txt", OCT, "<file content>"), ("fileb", "testb.txt", "text/plain", "<file b content>"))),
    ("request_form_models_001", TFM + "test_tutorial001.py::test_post_body_form", "POST", "/login/", F, "username=Foo&password=secret"),
    ("request_form_models_001", TFM + "test_tutorial001.py::test_post_body_form_no_password", "POST", "/login/", F, "username=Foo"),
    ("request_form_models_001", TFM + "test_tutorial001.py::test_post_body_form_no_username", "POST", "/login/", F, "password=secret"),
    ("request_form_models_001", TFM + "test_tutorial001.py::test_post_body_form_no_data", "POST", "/login/", {}, None),
    ("request_form_models_001", TFM + "test_tutorial001.py::test_post_body_json", "POST", "/login/", J, '{"username": "Foo", "password": "secret"}'),
    # milestone 3: security
    ("security_004", TS + "test_tutorial004.py::test_login", "POST", "/token", F, "username=johndoe&password=secret"),
    ("security_004", TS + "test_tutorial004.py::test_login_incorrect_password", "POST", "/token", F, "username=johndoe&password=incorrect"),
    ("security_004", TS + "test_tutorial004.py::test_login_incorrect_username", "POST", "/token", F, "username=foo&password=secret"),
    ("security_004", TS + "test_tutorial004.py::test_no_token", "GET", "/users/me/", {}, None),
    ("security_004", TS + "test_tutorial004.py::test_token", "GET", "/users/me/", {"Authorization": "Bearer sub=johndoe"}, None),
    ("security_004", TS + "test_tutorial004.py::test_incorrect_token", "GET", "/users/me/", {"Authorization": "Bearer nonexistent"}, None),
    ("security_004", TS + "test_tutorial004.py::test_incorrect_token_type", "GET", "/users/me/", {"Authorization": "Notexistent testtoken"}, None),
    ("security_004", TS + "test_tutorial004.py::test_token_no_sub", "GET", "/users/me/", {"Authorization": "Bearer data=foo"}, None),
    ("security_004", TS + "test_tutorial004.py::test_token_no_username", "GET", "/users/me/", {"Authorization": "Bearer sub=foo"}, None),
    ("security_004", TS + "test_tutorial004.py::test_token_nonexistent_user", "GET", "/users/me/", {"Authorization": "Bearer sub=username:bob"}, None),
    ("security_004", TS + "test_tutorial004.py::test_token_inactive_user", "POST", "/token", F, "username=alice&password=secretalice"),
    ("security_004", TS + "test_tutorial004.py::test_token_inactive_user", "GET", "/users/me/", {"Authorization": "Bearer sub=alice"}, None),
    ("security_004", TS + "test_tutorial004.py::test_read_items", "GET", "/users/me/items/", {"Authorization": "Bearer sub=johndoe"}, None),
    ("security_001", TS + "test_tutorial001.py::test_no_token", "GET", "/items", {}, None),
    ("security_001", TS + "test_tutorial001.py::test_token", "GET", "/items/", {"Authorization": "Bearer testtoken"}, None),
    ("security_001", TS + "test_tutorial001.py::test_incorrect_token", "GET", "/items/", {"Authorization": "Notexistent testtoken"}, None),
    ("security_002", TS + "test_tutorial002.py::test_no_token", "GET", "/users/me", {}, None),
    ("security_002", TS + "test_tutorial002.py::test_token", "GET", "/users/me", {"Authorization": "Bearer testtoken"}, None),
    ("security_003", TS + "test_tutorial003.py::test_login", "POST", "/token", F, "username=johndoe&password=secret"),
    ("security_003", TS + "test_tutorial003.py::test_login_incorrect_password", "POST", "/token", F, "username=johndoe&password=incorrect"),
    ("security_003", TS + "test_tutorial003.py::test_login_incorrect_username", "POST", "/token", F, "username=foo&password=secret"),
    ("security_003", TS + "test_tutorial003.py (missing form fields)", "POST", "/token", F, "grant_type=wrong&scope="),
    ("security_003", TS + "test_tutorial003.py (form without its content type)", "POST", "/token", {}, "username=johndoe&password=secret"),
    ("security_003", TS + "test_tutorial003.py (percent-encoded form)", "POST", "/token", F, "username=john%64oe&password=se+cret&&x"),
    ("security_003", TS + "test_tutorial003.py (percent-encoded form)", "POST", "/token", F, "username=johndoe&password=secret&username=alice"),
    ("security_003", TS + "test_tutorial003.py::test_no_token", "GET", "/users/me", {}, None),
    ("security_003", TS + "test_tutorial003.py::test_token", "GET", "/users/me", {"Authorization": "Bearer johndoe"}, None),
    ("security_003", TS + "test_tutorial003.py::test_incorrect_token", "GET", "/users/me", {"Authorization": "Bearer nonexistent"}, None),
    ("security_003", TS + "test_tutorial003.py::test_incorrect_token_type", "GET", "/users/me", {"Authorization": "Notexistent testtoken"}, None),
    ("security_003", TS + "test_tutorial003.py::test_inactive_user", "GET", "/users/me", {"Authorization": "Bearer alice"}, None),
    ("security_005", TS + "test_tutorial005.py::test_login", "POST", "/token", F, "username=johndoe&password=secret&scope=me items"),
    ("security_005", TS + "test_tutorial005.py::test_login_incorrect_password", "POST", "/token", F, "username=johndoe&password=incorrect"),
    ("security_005", TS + "test_tutorial005.py::test_no_token", "GET", "/users/me/", {}, None),
    ("security_005", TS + "test_tutorial005.py::test_token", "GET", "/users/me/", {"Authorization": "Bearer johndoe|me items"}, None),
    ("security_005", TS + "test_tutorial005.py::test_incorrect_token", "GET", "/users/me/", {"Authorization": "Bearer nonexistent"}, None),
    ("security_005", TS + "test_tutorial005.py::test_token_no_scope", "GET", "/users/me/", {"Authorization": "Bearer johndoe|"}, None),
    ("security_005", TS + "test_tutorial005.py::test_token_inexistent_user", "GET", "/users/me/", {"Authorization": "Bearer bob|me"}, None),
    ("security_005", TS + "test_tutorial005.py::test_token_inactive_user", "GET", "/users/me/", {"Authorization": "Bearer alice|me"}, None),
    ("security_005", TS + "test_tutorial005.py::test_read_items", "GET", "/users/me/items/", {"Authorization": "Bearer johndoe|me items"}, None),
    ("security_005", TS + "test_tutorial005.py::test_read_items", "GET", "/users/me/items/", {"Authorization": "Bearer johndoe|me"}, None),
    ("security_005", TS + "test_tutorial005.py::test_read_system_status", "GET", "/status/", {"Authorization": "Bearer johndoe|"}, None),
    ("security_005", TS + "test_tutorial005.py::test_read_system_status_no_token", "GET", "/status/", {}, None),
    ("security_006", TS + "test_tutorial006.py::test_security_http_basic", "GET", "/users/me", {"Authorization": BASIC}, None),
    ("security_006", TS + "test_tutorial006.py::test_security_http_basic_no_credentials", "GET", "/users/me", {}, None),
    ("security_006", TS + "test_tutorial006.py::test_security_http_basic_invalid_credentials", "GET", "/users/me", {"Authorization": "Basic notabase64token"}, None),
    ("security_006", TS + "test_tutorial006.py::test_security_http_basic_non_basic_credentials", "GET", "/users/me", {"Authorization": "Basic am9obnNlY3JldA=="}, None),
    ("security_006", TS + "test_tutorial006.py (padding and stray characters)", "GET", "/users/me", {"Authorization": "Basic am9o*bjpz ZWNyZXQ"}, None),
    ("security_006", TS + "test_tutorial006.py (padding ends the data)", "GET", "/users/me", {"Authorization": "Basic YTpi==Yzpk"}, None),
    ("security_006", TS + "test_tutorial006.py (non-ASCII credentials)", "GET", "/users/me", {"Authorization": "Basic w6k6dg=="}, None),
    ("security_006", TS + "test_tutorial006.py (scheme in another case)", "GET", "/users/me", {"Authorization": "bAsIc am9objpzZWNyZXQ="}, None),
    ("security_007", TS + "test_tutorial007.py::test_security_http_basic", "GET", "/users/me", {"Authorization": "Basic c3RhbmxleWpvYnNvbjpzd29yZGZpc2g="}, None),
    ("security_007", TS + "test_tutorial007.py::test_security_http_basic_invalid_credentials", "GET", "/users/me", {"Authorization": "Basic notabase64token"}, None),
    ("security_007", TS + "test_tutorial007.py::test_security_http_basic_non_basic_credentials", "GET", "/users/me", {"Authorization": "Basic am9obnNlY3JldA=="}, None),
    ("security_007", TS + "test_tutorial007.py::test_security_http_basic_invalid_username", "GET", "/users/me", {"Authorization": "Basic YWxpY2U6c3dvcmRmaXNo"}, None),
    ("security_api_key_query", "tests/test_security_api_key_query.py::test_security_api_key", "GET", "/users/me?key=secret", {}, None),
    ("security_api_key_query", "tests/test_security_api_key_query.py::test_security_api_key_no_key", "GET", "/users/me", {}, None),
    ("security_api_key_query", "tests/test_security_api_key_query.py (empty key)", "GET", "/users/me?key=", {}, None),
    ("security_api_key_header_optional", "tests/test_security_api_key_header_optional.py::test_security_api_key", "GET", "/users/me", {"key": "secret"}, None),
    ("security_api_key_header_optional", "tests/test_security_api_key_header_optional.py::test_security_api_key_no_key", "GET", "/users/me", {}, None),
    ("security_api_key_cookie", "tests/test_security_api_key_cookie.py::test_security_api_key", "GET", "/users/me", {"cookie": "key=secret"}, None),
    ("security_api_key_cookie", "tests/test_security_api_key_cookie.py::test_security_api_key_no_key", "GET", "/users/me", {}, None),
    ("security_http_base", "tests/test_security_http_base.py::test_security_http_base", "GET", "/users/me", {"Authorization": "Other foobar"}, None),
    ("security_http_base", "tests/test_security_http_base.py::test_security_http_base_no_credentials", "GET", "/users/me", {}, None),
    ("security_http_base", "tests/test_security_http_base.py (another scheme is accepted)", "GET", "/users/me", {"Authorization": "Bearer  foobar "}, None),
    ("security_http_base", "tests/test_security_http_base.py (no credentials after the scheme)", "GET", "/users/me", {"Authorization": "Other"}, None),
    ("security_http_bearer_optional", "tests/test_security_http_bearer_optional.py::test_security_http_bearer", "GET", "/users/me", {"Authorization": "Bearer foobar"}, None),
    ("security_http_bearer_optional", "tests/test_security_http_bearer_optional.py::test_security_http_bearer_no_credentials", "GET", "/users/me", {}, None),
    ("security_http_bearer_optional", "tests/test_security_http_bearer_optional.py::test_security_http_bearer_incorrect_scheme_credentials", "GET", "/users/me", {"Authorization": "Basic notreally"}, None),
    ("security_http_digest", "tests/test_security_http_digest.py::test_security_http_digest", "GET", "/users/me", {"Authorization": "Digest foobar"}, None),
    ("security_http_digest", "tests/test_security_http_digest.py::test_security_http_digest_no_credentials", "GET", "/users/me", {}, None),
    ("security_http_digest", "tests/test_security_http_digest.py::test_security_http_digest_incorrect_scheme_credentials", "GET", "/users/me", {"Authorization": "Other invalidauthorization"}, None),
    ("security_http_basic_realm", "tests/test_security_http_basic_realm.py::test_security_http_basic", "GET", "/users/me", {"Authorization": BASIC}, None),
    ("security_http_basic_realm", "tests/test_security_http_basic_realm.py::test_security_http_basic_no_credentials", "GET", "/users/me", {}, None),
    ("security_http_basic_realm", "tests/test_security_http_basic_realm.py::test_security_http_basic_invalid_credentials", "GET", "/users/me", {"Authorization": "Basic notabase64token"}, None),
    ("security_openid_connect_optional", "tests/test_security_openid_connect_optional.py::test_security_oauth2", "GET", "/users/me", {"Authorization": "Bearer footokenbar"}, None),
    ("security_openid_connect_optional", "tests/test_security_openid_connect_optional.py::test_security_oauth2_password_other_header", "GET", "/users/me", {"Authorization": "Other footokenbar"}, None),
    ("security_openid_connect_optional", "tests/test_security_openid_connect_optional.py::test_security_oauth2_password_bearer_no_header", "GET", "/users/me", {}, None),
    ("security_oauth2_authorization_code_bearer", "tests/test_security_oauth2_authorization_code_bearer.py::test_no_token", "GET", "/items", {}, None),
    ("security_oauth2_authorization_code_bearer", "tests/test_security_oauth2_authorization_code_bearer.py::test_incorrect_token", "GET", "/items/", {"Authorization": "Non-existent testtoken"}, None),
    ("security_oauth2_authorization_code_bearer", "tests/test_security_oauth2_authorization_code_bearer.py::test_token", "GET", "/items/", {"Authorization": "Bearer testtoken"}, None),
]


def exchanges():
    out = []
    for fx, upstream, method, url, headers, body in SCENARIOS:
        c = TestClient(FIXTURES[fx], follow_redirects=False, raise_server_exceptions=False)
        r = c.request(method, url, headers=headers, content=body.encode() if body is not None else None)
        out.append({
            "fixture": fx, "upstream": upstream, "method": method, "url": url,
            "request_headers": [[k.decode(), v.decode()] for k, v in r.request.headers.raw],
            "body": body,
            "status": r.status_code,
            "headers": [[k.decode(), v.decode()] for k, v in r.headers.raw],
            "response": r.content.decode("utf-8"),
        })
    return out


# Large inputs end to end: the lean-starlette bench sizes through the demo,
# and the critic's two timed cases through `bench`. Each request is a recipe
# (url = prefix + repeat * count; an optional header of `count` repeated
# characters; a body recipe), so the golden stays small. `budget_ms` is the
# Lean bound, set from FastAPI's time for the same request under uvicorn on
# the development machine: the dict body (FastAPI 55-78 ms, Lean ~87 ms) at
# about twice that; the 1 MiB header (FastAPI 20 ms, Lean ~52 ms: lean-json's
# printer echoing the 1 MiB input, ~33 ms, and lean-pydantic's digit scan,
# ~25 ms) at 100 ms. Doubling either input takes 1.9x (header) and 2.4x
# (dict) the time.
# The size cases have 2000 ms, which bounds a quadratic regression.
BENCH = [
    {"fixture": "demo", "name": "wide object body, 100000 keys", "method": "PUT", "prefix": "/items/1", "body": "wide:100000"},
    {"fixture": "demo", "name": "10000 keys colliding in Lean's String.hash buckets", "method": "PUT", "prefix": "/items/1", "body": "collide"},
    {"fixture": "demo", "name": "65000-char non-matching path", "method": "GET", "prefix": "/", "repeat": "a", "count": 65000},
    {"fixture": "demo", "name": "65000-digit item_id", "method": "GET", "prefix": "/items/", "repeat": "1", "count": 65000},
    {"fixture": "demo", "name": "65000-char str item_id", "method": "GET", "prefix": "/stock/", "repeat": "s", "count": 65000},
    {"fixture": "bench", "name": "1 MiB int header parameter", "method": "GET", "prefix": "/header-int",
     "header": ["x-n", "1", 1 << 20], "budget_ms": 100},
    {"fixture": "bench", "name": "dict[str, int] body, 100000 keys", "method": "POST", "prefix": "/dict", "body": "dict:100000",
     "budget_ms": 150},
]


# lean-json's fixture of keys that share a bucket under Lean's fixed-seed
# String.hash (tests/fixtures/collide-keys.txt there, from its collidegen).
COLLIDE_KEYS = HERE.parents[1] / ".lake" / "packages" / "LeanJson" / "tests" / "fixtures" / "collide-keys.txt"


def bench_body(recipe):
    if recipe is None:
        return None
    if recipe == "collide":
        keys = [k for k in COLLIDE_KEYS.read_text().split("\n") if k]
        return '{"name":"x","price":2,' + ",".join(f'"{k}":0' for k in keys) + '}'
    kind, n = recipe.split(":")
    members = ",".join(f'"k{i}":{i}' for i in range(int(n)))
    return '{"name":"x","price":2,' + members + '}' if kind == "wide" else '{' + members + '}'


REPEAT_MARK = "<<REPEAT>>"


def bench():
    out = []
    for case in BENCH:
        c = TestClient(FIXTURES[case["fixture"]], follow_redirects=False, raise_server_exceptions=False)
        body = bench_body(case.get("body"))
        headers = dict(J) if body else {}
        if "header" in case:
            name, ch, count = case["header"]
            headers[name] = ch * count
        url = case["prefix"] + case.get("repeat", "") * case.get("count", 0)
        r = c.request(case["method"], url, content=body.encode() if body else None, headers=headers)
        run = case["header"][1] * case["header"][2] if "header" in case else case.get("repeat", "") * case.get("count", 0)
        text = r.content.decode("utf-8")
        # The generated run, where a response echoes it, is written REPEAT_MARK.
        text = text.replace(run, REPEAT_MARK) if len(run) > 1000 else text
        out.append(dict(case, budget_ms=case.get("budget_ms", 2000),
                        request_headers=[[k.decode(), v.decode()] for k, v in r.request.headers.raw
                                         if "header" not in case or k.decode() != case["header"][0]],
                        status=r.status_code, headers=[[k.decode(), v.decode()] for k, v in r.headers.raw],
                        response=text))
    return out


def openapis():
    return [{"fixture": fx, "upstream": "tests/test_openapi_examples.py (app.openapi())", "openapi": app.openapi()}
            for fx, app in FIXTURES.items()]


def pyjson_corpus():
    """json.loads on handwritten and random near-JSON texts."""
    B = chr(92)
    texts = ['"' + B + 'u12"', '"' + B + 'u1234', '"' + B + 'uD800' + B + 'u', '01', '1.', '1e+', '[1,]', '{"a":1\n,\n}',
             '[1 , ]', '{"a":{"b":1]}', '[[[', '-Inf', '-Infinity', 'nul', '[1,,2]', '{,}', '"x"  y', '"é' + B + 'q"',
             '1' * 4301, '-' + '1' * 4300, '', '  ', '{"a" 1}', '{"a":}', 'NaN', 'Infinity', '"a\tb"', '[1e5, -0.0, 1E-2]']
    alphabet = ['{', '}', '[', ']', ',', ':', '"', B, 'u', 'a', '0', '1', '-', '.', 'e', '+', ' ', '\n', 'n', 't', 'N', 'I', '\x01', 'é']
    rng = random.Random(1729)
    for _ in range(3000):
        texts.append("".join(rng.choice(alphabet) for _ in range(rng.randint(0, 12))))
    for _ in range(1000):
        doc = json.dumps({"a": [1, 2.5, None, True, "x\"y"], "b": {"c": "é"}})
        i = rng.randrange(len(doc))
        texts.append(doc[:i] + rng.choice(alphabet) + doc[i + rng.randint(0, 2):])
    out = []
    for t in texts:
        try:
            json.loads(t.encode("utf-8"))
            out.append({"text": t, "ok": True})
        except json.JSONDecodeError as e:
            out.append({"text": t, "ok": False, "msg": e.msg, "pos": e.pos})
        except Exception:
            out.append({"text": t, "ok": False, "msg": None, "pos": None})
    return out


def b64_corpus():
    """base64.b64decode (what HTTPBasic runs) on handwritten and random texts:
    the bytes, or null where it raises; and the credentials HTTPBasic takes
    from them (ASCII, split at the first ':'), or null for its 401."""
    import base64, binascii
    texts = ["", "=", "==", "A", "AA", "AA=", "AA==", "AAA", "AAA=", "AAAA", "AA==AA==", "AA=A", "A===",
             "dXNlcjpwYXNz", "dXNlcjpwYXNz=", "dXNlcjpwYXNz==", "dXNl cjpw YXNz", "dXNlcjpwYXN", "dXNlcjpwYXNzZA",
             "dXNlcjpwYXNzZA==", "dXNlcjpwYXNzZA==ZA==", "dXNl-cjpwYXNz", "dXNlcjpwYXNz!", "dXNlcjpwYXNzé",
             "OnBhc3M=", "dXNlcjo=", "dXNlcg==", "w6k6eA==", "/w==", "-_8=", "dXNlcjpwYXNz\n", "\tdXNlcjpwYXNz"]
    rng = random.Random(4096)
    alphabet = list("ABCdz09+/=") + [" ", "-", "_", "\n", "!", "é", ":"]
    for _ in range(1500):
        texts.append("".join(rng.choice(alphabet) for _ in range(rng.randint(0, 14))))
    for _ in range(1500):
        raw = bytes(rng.choice([rng.randrange(32, 127), rng.randrange(256), 58]) for _ in range(rng.randint(0, 10)))
        t = base64.b64encode(raw).decode()
        if t and rng.random() < 0.5:
            i = rng.randrange(len(t))
            t = t[:i] + rng.choice(alphabet) + t[i + rng.randint(0, 2):]
        texts.append(t)
    out = []
    for t in texts:
        try:
            data = base64.b64decode(t)
        except (ValueError, binascii.Error):
            out.append({"text": t, "bytes": None, "creds": None})
            continue
        try:
            u, sep, pw = data.decode("ascii").partition(":")
            creds = [u, pw] if sep else None
        except UnicodeDecodeError:
            creds = None
        out.append({"text": t, "bytes": list(data), "creds": creds})
    return out


def form_corpus():
    """await request.form() on application/x-www-form-urlencoded bodies:
    the fields in order, or the 400 detail Starlette raises."""
    import asyncio
    from starlette.requests import Request
    from starlette.formparsers import MultiPartException
    bodies = [b"", b"a=1", b"a=1&b=2", b"a=1&a=2", b"a", b"a=", b"=1", b"&&a=1&&", b"a=1;b=2", b"a+b=c+d",
              b"a%20b=%41%42", b"a=%C3%A9", b"a=%E9", b"a=\xe9", b"a=%", b"a=%4", b"a=%zz", b"a==b", b"%26=%3D",
              b"x=" + b"y" * (1024 * 1024), b"x=" + b"y" * (1024 * 1024 - 1), b"&".join(b"f=1" for _ in range(1000)),
              b"&".join(b"f=1" for _ in range(1001)), b"a=1&" * 3, b" a = 1 "]
    rng = random.Random(1024)
    alphabet = [b"a", b"b", b"=", b"&", b";", b"+", b"%", b"2", b"0", b"4", b"1", b"C3", b"A9", b"\xe9", b" "]
    for _ in range(1500):
        bodies.append(b"".join(rng.choice(alphabet) for _ in range(rng.randint(0, 12))))

    async def form(body):
        sent = False
        async def receive():
            nonlocal sent
            if sent:
                return {"type": "http.disconnect"}
            sent = True
            return {"type": "http.request", "body": body, "more_body": False}
        scope = {"type": "http", "method": "POST", "path": "/", "query_string": b"",
                 "headers": [(b"content-type", b"application/x-www-form-urlencoded")]}
        try:
            async with Request(scope, receive).form() as f:
                return {"fields": [[k, v] for k, v in f.multi_items()]}
        except MultiPartException as e:  # Starlette's 400 inside an app
            return {"error": e.message}
    out = []
    for b in bodies:
        r = asyncio.run(form(b))
        if len(b) > 65536:  # stored as a recipe: "x=" then count copies of "y"
            r.update(prefix=b[:2].decode(), fill=b[2:3].decode(), count=len(b) - 2)
            assert b == b[:2] + b[2:3] * (len(b) - 2)
            if "fields" in r:
                r["fields"] = [[k, {"fill": v[:1], "count": len(v)}] for k, v in r["fields"]]
        else:
            r["body"] = b.decode("latin-1")
        out.append(r)
    return out


if __name__ == "__main__":
    (HERE / "fastapi.json").write_text(json.dumps({"exchanges": exchanges(), "openapi": openapis()}, indent=1, ensure_ascii=False) + "\n")
    (HERE / "bench.json").write_text(json.dumps(bench(), indent=1, ensure_ascii=False) + "\n")
    (HERE / "pyjson.json").write_text(json.dumps(pyjson_corpus(), indent=0, ensure_ascii=False) + "\n")
    (HERE / "b64.json").write_text(json.dumps(b64_corpus(), indent=0, ensure_ascii=False) + "\n")
    (HERE / "form.json").write_text(json.dumps(form_corpus(), indent=0, ensure_ascii=False) + "\n")
