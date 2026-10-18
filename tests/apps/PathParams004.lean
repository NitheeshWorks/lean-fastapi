-- upstream: docs_src/path_params/tutorial004_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.PathParams004

def app := FastAPI.new

@[get "/files/{file_path:path}"]
def readFile (file_path : String) : Handler Json :=
  return json% {"file_path": file_path}

end Tests.PathParams004
