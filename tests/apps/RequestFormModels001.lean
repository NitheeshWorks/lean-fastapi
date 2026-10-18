-- upstream: docs_src/request_form_models/tutorial001_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.RequestFormModels001

def app := FastAPI.new

structure FormData where
  username : String
  password : String
  deriving Model

-- Python's `login` has no return annotation, so no response model.
@[post "/login/" (response_model := none)]
def login (data : Form FormData) : Handler FormData :=
  return data

end Tests.RequestFormModels001
