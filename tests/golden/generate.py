"""Record fastapi 0.143.3's exact responses for the golden conformance cases.

Run locally (never in CI) with the upstream-spec venv:

    upstream-spec/.venv/bin/python -I tests/golden/generate.py

It writes tests/golden/fastapi.json (HTTP exchanges and app.openapi() per
fixture), tests/golden/bench.json (large inputs through the demo) and
tests/golden/pyjson.json (json.loads errors on a corpus).

Each fixture is an upstream tutorial app (imported from
upstream-spec/fastapi/docs_src, the real code) or an app defined below; its
Lean twin of the same name is in tests/apps/ and listed in
tests/Conformance.lean (`fixtures`). Every request is replayed in Lean with
the exact headers TestClient sent, and the status, the response headers and
the body are compared byte for byte.
"""
import importlib, json, random, sys, warnings
from pathlib import Path
from typing import Annotated

warnings.simplefilter("ignore")
HERE = Path(__file__).resolve().parent
UPSTREAM = HERE.parents[2] / "upstream-spec" / "fastapi"
sys.path.insert(0, str(UPSTREAM))

from fastapi import FastAPI, HTTPException  # noqa: E402
from fastapi.testclient import TestClient  # noqa: E402
from pydantic import BaseModel, Field  # noqa: E402


def tutorial(path):
    return importlib.import_module("docs_src." + path).app


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
}

J = {"content-type": "application/json"}
T = "tests/test_tutorial/"
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


# Large inputs through the demo, end to end (the lean-starlette bench sizes).
# Each request is a recipe, url = prefix + repeat * count and an optional
# wide object body of n keys, so the golden stays small.
BENCH = [
    ("wide object body, 100000 keys", "PUT", "/items/1", "", 0, 100000),
    ("10000 keys colliding in Lean's String.hash buckets", "PUT", "/items/1", "", 0, "collide"),
    ("65000-char non-matching path", "GET", "/", "a", 65000, None),
    ("65000-digit item_id", "GET", "/items/", "1", 65000, None),
    ("65000-char str item_id", "GET", "/stock/", "s", 65000, None),
]


# lean-json's fixture of keys that share a bucket under Lean's fixed-seed
# String.hash (tests/fixtures/collide-keys.txt there, from its collidegen).
COLLIDE_KEYS = HERE.parents[1] / ".lake" / "packages" / "LeanJson" / "tests" / "fixtures" / "collide-keys.txt"


def wide_body(n):
    if n == "collide":
        keys = [k for k in COLLIDE_KEYS.read_text().split("\n") if k]
        return '{"name":"x","price":2,' + ",".join(f'"{k}":0' for k in keys) + '}'
    return '{"name":"x","price":2,' + ",".join(f'"k{i}":{i}' for i in range(n)) + '}'


def bench():
    out = []
    c = TestClient(demo, follow_redirects=False, raise_server_exceptions=False)
    for name, method, prefix, repeat, count, n in BENCH:
        body = wide_body(n) if n is not None else None
        r = c.request(method, prefix + repeat * count, content=body.encode() if body else None,
                      headers=J if body else {})
        out.append({"name": name, "method": method, "prefix": prefix, "repeat": repeat, "count": count,
                    "wide": n, "request_headers": [[k.decode(), v.decode()] for k, v in r.request.headers.raw],
                    "status": r.status_code, "headers": [[k.decode(), v.decode()] for k, v in r.headers.raw],
                    "response": r.content.decode("utf-8")})
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


if __name__ == "__main__":
    (HERE / "fastapi.json").write_text(json.dumps({"exchanges": exchanges(), "openapi": openapis()}, indent=1, ensure_ascii=False) + "\n")
    (HERE / "bench.json").write_text(json.dumps(bench(), indent=1, ensure_ascii=False) + "\n")
    (HERE / "pyjson.json").write_text(json.dumps(pyjson_corpus(), indent=0, ensure_ascii=False) + "\n")
