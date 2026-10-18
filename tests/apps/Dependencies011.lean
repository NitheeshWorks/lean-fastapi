-- upstream: docs_src/dependencies/tutorial011_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.Dependencies011

def app := FastAPI.new

structure FixedContentQueryChecker where
  fixed_content : String

/-- `__call__`. -/
def FixedContentQueryChecker.call (self : FixedContentQueryChecker) (q : String := "") : Bool :=
  if q.isEmpty then false else (q.splitOn self.fixed_content).length > 1

def checker := FixedContentQueryChecker.mk "bar"

@[get "/query-checker/"]
def readQueryCheck (fixed_content_included : Depends checker) : Handler Json :=
  return json% {"fixed_content_in_query": fixed_content_included}

end Tests.Dependencies011
