-- upstream: fastapi/dependencies/utils.py::_extract_form_body (a form model with an
-- aliased field, a list field and defaults: the value its 422s echo). Python twin:
-- `form_model_aliased_app` in tests/golden/generate.py.
import LeanFastapi
open LeanFastapi

namespace Tests.FormModelAliased

def app := FastAPI.new

structure AliasedForm where
  user_name : Alias "userName" String
  password : String
  tags : List String := []
  note : Option String := none
  count : Int := 3
  deriving Model

@[post "/login/" (response_model := none)]
def loginAliased (data : Form AliasedForm) : Handler AliasedForm :=
  return data

end Tests.FormModelAliased
