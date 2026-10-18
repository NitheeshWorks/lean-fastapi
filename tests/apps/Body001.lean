-- upstream: docs_src/body/tutorial001_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Body001

structure Item where
  name : String
  description : Option String := none
  price : Decimal
  tax : Option Decimal := none
  deriving Model

def app := FastAPI.new

-- `async def create_item(item: Item)` has no return annotation, so no response model
@[post "/items/" (response_model := none)]
def createItem (item : Item) : Handler Item :=
  return item

end Tests.Body001
