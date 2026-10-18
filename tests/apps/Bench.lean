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

-- Large uploads (critic, pso2kuyvm4hr): 10 and 20 MiB through each file shape.
@[post "/bytes/"]
def uploadBytes (file : File Bytes) : Handler Json :=
  return json% {"size": (file.size)}

@[post "/upload/"]
def uploadOne (file : UploadFile) : Handler Json := do
  let data ← file.read
  return json% {"filename": (file.filename), "size": (data.size)}

@[post "/uploads/"]
def uploadMany (files : List UploadFile) : Handler Json := do
  let sizes ← files.mapM fun f => f.size
  return json% {"sizes": sizes}

end Tests.Bench
