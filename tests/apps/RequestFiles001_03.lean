-- upstream: docs_src/request_files/tutorial001_03_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.RequestFiles001_03

def app := FastAPI.new

@[post "/files/"]
def createFile (file : File Bytes (description := "A file read as bytes")) : Handler Json :=
  return json% {"file_size": (file.size)}

@[post "/uploadfile/"]
def createUploadFile (file : File UploadFile (description := "A file read as UploadFile")) : Handler Json :=
  return json% {"filename": (file.filename)}

end Tests.RequestFiles001_03
