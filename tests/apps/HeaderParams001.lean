-- upstream: docs_src/header_params/tutorial001_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.HeaderParams001

def app := FastAPI.new

@[get "/items/"]
def readItems (user_agent : Header (Option String) := none) : Handler Json :=
  return json% {"User-Agent": user_agent}

end Tests.HeaderParams001
