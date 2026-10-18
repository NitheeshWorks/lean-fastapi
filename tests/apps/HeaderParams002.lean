-- upstream: docs_src/header_params/tutorial002_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.HeaderParams002

def app := FastAPI.new

@[get "/items/"]
def readItems (strange_header : Header (Option String) (convert_underscores := false) := none) : Handler Json :=
  return json% {"strange_header": strange_header}

end Tests.HeaderParams002
