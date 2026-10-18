-- upstream: docs_src/request_files/tutorial001_02_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.RequestFiles001_02

def app := FastAPI.new

@[post "/files/"]
def createFile (file : File (Option Bytes) := none) : Handler Json :=
  -- `if not file`: no file, or an empty one
  match file with
  | some f => if f.isEmpty then return json% {"message": "No file sent"} else return json% {"file_size": (f.size)}
  | none => return json% {"message": "No file sent"}

@[post "/uploadfile/"]
def createUploadFile (file : Option UploadFile := none) : Handler Json :=
  match file with
  | some f => return json% {"filename": (f.filename)}
  | none => return json% {"message": "No upload file sent"}

end Tests.RequestFiles001_02
