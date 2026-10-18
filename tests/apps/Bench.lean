-- upstream: none (the critic's timed cases on b6n01b9wts1z; the Python twin is
-- `bench_app` in tests/golden/generate.py)
import LeanFastapi
open LeanFastapi

namespace Tests.Bench

def app := FastAPI.new

@[get "/header-int"]
def headerInt (x_n : Header Int) : Handler Json := do
  let positive := decide (x_n > 0)
  return json% {"positive": positive}

@[post "/dict"]
def dictBody (d : LeanPydantic.Dict Int) : Handler Json := do
  let keys := d.entries.length
  return json% {"keys": keys}

end Tests.Bench
