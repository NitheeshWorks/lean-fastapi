-- upstream: docs_src/path_params/tutorial002_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.PathParams002

def app := FastAPI.new

@[get "/items/{item_id}"]
def readItem (item_id : Int) : Handler Json :=
  return json% {"item_id": item_id}

end Tests.PathParams002
