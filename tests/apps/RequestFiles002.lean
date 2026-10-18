-- upstream: docs_src/request_files/tutorial002_an_py310.py
import LeanFastapi
open LeanFastapi

namespace Tests.RequestFiles002

def app := FastAPI.new

@[post "/files/"]
def createFiles (files : File (List Bytes)) : Handler Json :=
  return json% {"file_sizes": (files.map (·.size))}

@[post "/uploadfiles/"]
def createUploadFiles (files : List UploadFile) : Handler Json :=
  return json% {"filenames": (files.map (·.filename))}

@[get "/"]
def main : Handler Response :=
  let content := "
<body>
<form action=\"/files/\" enctype=\"multipart/form-data\" method=\"post\">
<input name=\"files\" type=\"file\" multiple>
<input type=\"submit\">
</form>
<form action=\"/uploadfiles/\" enctype=\"multipart/form-data\" method=\"post\">
<input name=\"files\" type=\"file\" multiple>
<input type=\"submit\">
</form>
</body>
    "
  return HTMLResponse content

end Tests.RequestFiles002
