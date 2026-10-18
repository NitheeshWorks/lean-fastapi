-- upstream: docs_src/dependencies/tutorial005_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Dependencies005

def app := FastAPI.new

def queryExtractor (q : Option String := none) : Option String := q

def queryOrCookieExtractor (q : Depends queryExtractor) (last_query : Cookie (Option String) := none) :
    Option String :=
  match q with
  | none | some "" => last_query
  | some q => some q

@[get "/items/"]
def readQuery (query_or_default : Depends queryOrCookieExtractor) : Handler Json :=
  return json% {"q_or_cookie": query_or_default}

end Tests.Dependencies005
