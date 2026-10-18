-- upstream: docs_src/first_steps/tutorial001_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.FirstSteps001

def app := FastAPI.new

@[get "/"]
def root : Handler Json :=
  return json% {"message": "Hello World"}

end Tests.FirstSteps001
