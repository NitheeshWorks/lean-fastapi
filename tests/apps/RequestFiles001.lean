-- upstream: docs_src/request_files/tutorial001_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.RequestFiles001

def app := FastAPI.new

@[post "/files/"]
def createFile (file : File Bytes) : Handler Json :=
  return json% {"file_size": (file.size)}

@[post "/uploadfile/"]
def createUploadFile (file : UploadFile) : Handler Json :=
  return json% {"filename": (file.filename)}

end Tests.RequestFiles001
