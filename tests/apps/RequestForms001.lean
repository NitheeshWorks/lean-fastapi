-- upstream: docs_src/request_forms/tutorial001_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.RequestForms001

def app := FastAPI.new

@[post "/login/"]
def login (username : Form String) (password : Form String) : Handler Json :=
  return json% {"username": username}

end Tests.RequestForms001
