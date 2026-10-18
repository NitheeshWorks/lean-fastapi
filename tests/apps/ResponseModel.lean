-- upstream: none (response_model cases of tests/test_response_model*.py; the
-- Python twin is `rm` in tests/golden/generate.py)
import LeanFastapi
open LeanFastapi

namespace Tests.ResponseModel

def app := FastAPI.new

structure Public where
  name : String
  price : Float
  deriving Model

@[get "/public" (response_model := Public)]
def getPublic : Handler Json :=
  return json% {"name": "Foo", "price": 1, "secret": "s3cr3t"}

@[get "/typed"]
def getTyped : Handler Public :=
  return { name := "Bar", price := 2.5 }

@[get "/count"]
def getCount : Handler Int :=
  return 3

@[post "/created" (status_code := 201) (tags := ["items"]) (summary := "Create")
  (response_description := "Made") (deprecated := true)]
def make (item : Public) : Handler Public :=
  return item

@[delete "/zap" (operation_id := "zap_it")]
def zap (item : Option Public := none) : Handler Json :=
  return json% {"had": item.isSome}

@[get "/multi"]
def multiGet : Handler Json :=
  return json% {"m": "get"}

@[post "/multi"]
def multiPost : Handler Json :=
  return json% {"m": "post"}

structure Count where
  n : Int
  deriving Model

@[post "/counted"]
def counted (c : Count) : Handler Count :=
  return c

end Tests.ResponseModel
