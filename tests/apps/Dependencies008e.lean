-- upstream: docs_src/dependencies/tutorial008e_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Dependencies008e

def app := FastAPI.new

def getUsername : Yield String :=
  yieldFinally "Rick" (IO.println "Cleanup up before response is sent")

@[get "/users/me" (response_model := none)]
def getUserMe (username : Depends getUsername (scope := "function")) : Handler String :=
  return username

end Tests.Dependencies008e
