-- upstream: docs_src/request_forms_and_files/tutorial001_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.RequestFormsAndFiles001

def app := FastAPI.new

@[post "/files/"]
def createFile (file : File Bytes) (fileb : File UploadFile) (token : Form String) : Handler Json :=
  return json% {"file_size": (file.size), "token": token, "fileb_content_type": (fileb.content_type)}

end Tests.RequestFormsAndFiles001
