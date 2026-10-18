-- upstream: docs_src/query_params/tutorial005_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.QueryParams005

def app := FastAPI.new

@[get "/items/{item_id}"]
def readUserItem (item_id : String) (needy : String) : Handler Json :=
  return json% {"item_id": item_id, "needy": needy}

end Tests.QueryParams005
