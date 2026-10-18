-- upstream: docs_src/cookie_params/tutorial001_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.CookieParams001

def app := FastAPI.new

@[get "/items/"]
def readItems (ads_id : Cookie (Option String) := none) : Handler Json :=
  return json% {"ads_id": ads_id}

end Tests.CookieParams001
