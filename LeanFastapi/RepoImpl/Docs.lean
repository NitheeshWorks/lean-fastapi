import LeanFastapi.RepoImpl.OpenApi

/-!
# RepoImpl: the interactive documentation pages

`fastapi/openapi/docs.py`: the HTML of `/docs` (Swagger UI), `/redoc` and
`/docs/oauth2-redirect`, byte for byte (`tests/golden/fastapi.json` checks
each against fastapi 0.143.3). The OAuth2 redirect page is Swagger UI's
`dist/oauth2-redirect.html` (v4.14.0, Apache-2.0), which FastAPI ships
verbatim.
-/

namespace LeanFastapi

open LeanJson (Json)

/-- `_html_safe_json`: `json.dumps(value)` (default separators) with `<`, `>`
and `&` escaped. -/
def htmlSafeJson (j : Json) : String :=
  let s := LeanJson.printStr j { indent := none }
  -- `json.dumps` writes `", "` and `": "`; the values used here are scalars.
  String.ofList (s.toList.flatMap fun c =>
    if c = '<' then "\\u003c".toList else if c = '>' then "\\u003e".toList
    else if c = '&' then "\\u0026".toList else [c])

/-- `swagger_ui_default_parameters`. -/
def swaggerUiDefaultParameters : List (String × Json) :=
  [("dom_id", .str "#swagger-ui"), ("layout", .str "BaseLayout"), ("deepLinking", .bool true),
   ("showExtensions", .bool true), ("showCommonExtensions", .bool true)]

/-- `get_swagger_ui_html(openapi_url=, title=, ...)`. -/
def getSwaggerUiHtml (openapi_url title : String)
    (swagger_js_url : String := "https://cdn.jsdelivr.net/npm/swagger-ui-dist@5/swagger-ui-bundle.js")
    (swagger_css_url : String := "https://cdn.jsdelivr.net/npm/swagger-ui-dist@5/swagger-ui.css")
    (swagger_favicon_url : String := "https://fastapi.tiangolo.com/img/favicon.png")
    (oauth2_redirect_url : Option String := none)
    (swagger_ui_parameters : List (String × Json) := []) : String :=
  let params := swagger_ui_parameters.foldl (fun acc (k, v) =>
    if acc.any (·.1 == k) then acc.map (fun p => if p.1 == k then (k, v) else p) else acc ++ [(k, v)])
    swaggerUiDefaultParameters
  "
    <!DOCTYPE html>
    <html>
    <head>
    <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">
    <link type=\"text/css\" rel=\"stylesheet\" href=\"" ++ swagger_css_url ++ "\">
    <link rel=\"shortcut icon\" href=\"" ++ swagger_favicon_url ++ "\">
    <title>" ++ title ++ "</title>
    </head>
    <body>
    <div id=\"swagger-ui\">
    </div>
    <script src=\"" ++ swagger_js_url ++ "\"></script>
    <!-- `SwaggerUIBundle` is now available on the page -->
    <script>
    const ui = SwaggerUIBundle({
        url: '" ++ openapi_url ++ "',
    " ++ String.join (params.map fun (k, v) => htmlSafeJson (.str k) ++ ": " ++ htmlSafeJson v ++ ",\n") ++
  (match oauth2_redirect_url with
    | some u => "oauth2RedirectUrl: window.location.origin + '" ++ u ++ "',"
    | none => "") ++ "
    presets: [
        SwaggerUIBundle.presets.apis,
        SwaggerUIBundle.SwaggerUIStandalonePreset
        ],
    })" ++ "
    </script>
    </body>
    </html>
    "

/-- `get_redoc_html(openapi_url=, title=, ...)`. -/
def getRedocHtml (openapi_url title : String)
    (redoc_js_url : String := "https://cdn.jsdelivr.net/npm/redoc@2/bundles/redoc.standalone.js")
    (redoc_favicon_url : String := "https://fastapi.tiangolo.com/img/favicon.png")
    (with_google_fonts : Bool := true) : String :=
  "
    <!DOCTYPE html>
    <html>
    <head>
    <title>" ++ title ++ "</title>
    <!-- needed for adaptive design -->
    <meta charset=\"utf-8\"/>
    <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">
    " ++ (if with_google_fonts then "
    <link href=\"https://fonts.googleapis.com/css?family=Montserrat:300,400,700|Roboto:300,400,700\" rel=\"stylesheet\">
    " else "") ++ "
    <link rel=\"shortcut icon\" href=\"" ++ redoc_favicon_url ++ "\">
    <!--
    ReDoc doesn't change outer page styles
    -->
    <style>
      body {
        margin: 0;
        padding: 0;
      }
    </style>
    </head>
    <body>
    <noscript>
        ReDoc requires Javascript to function. Please enable it to browse the documentation.
    </noscript>
    <redoc spec-url=\"" ++ openapi_url ++ "\"></redoc>
    <script src=\"" ++ redoc_js_url ++ "\"> </script>
    </body>
    </html>
    "

/-- `get_swagger_ui_oauth2_redirect_html()`. -/
def swaggerUiOauth2RedirectHtml : String :=
  "
    <!doctype html>
    <html lang=\"en-US\">
    <head>
        <title>Swagger UI: OAuth2 Redirect</title>
    </head>
    <body>
    <script>
        'use strict';
        function run () {
            var oauth2 = window.opener.swaggerUIRedirectOauth2;
            var sentState = oauth2.state;
            var redirectUrl = oauth2.redirectUrl;
            var isValid, qp, arr;

            if (/code|token|error/.test(window.location.hash)) {
                qp = window.location.hash.substring(1).replace('?', '&');
            } else {
                qp = location.search.substring(1);
            }

            arr = qp.split(\"&\");
            arr.forEach(function (v,i,_arr) { _arr[i] = '\"' + v.replace('=', '\":\"') + '\"';});
            qp = qp ? JSON.parse('{' + arr.join() + '}',
                    function (key, value) {
                        return key === \"\" ? value : decodeURIComponent(value);
                    }
            ) : {};

            isValid = qp.state === sentState;

            if ((
              oauth2.auth.schema.get(\"flow\") === \"accessCode\" ||
              oauth2.auth.schema.get(\"flow\") === \"authorizationCode\" ||
              oauth2.auth.schema.get(\"flow\") === \"authorization_code\"
            ) && !oauth2.auth.code) {
                if (!isValid) {
                    oauth2.errCb({
                        authId: oauth2.auth.name,
                        source: \"auth\",
                        level: \"warning\",
                        message: \"Authorization may be unsafe, passed state was changed in server. The passed state wasn't returned from auth server.\"
                    });
                }

                if (qp.code) {
                    delete oauth2.state;
                    oauth2.auth.code = qp.code;
                    oauth2.callback({auth: oauth2.auth, redirectUrl: redirectUrl});
                } else {
                    let oauthErrorMsg;
                    if (qp.error) {
                        oauthErrorMsg = \"[\"+qp.error+\"]: \" +
                            (qp.error_description ? qp.error_description+ \". \" : \"no accessCode received from the server. \") +
                            (qp.error_uri ? \"More info: \"+qp.error_uri : \"\");
                    }

                    oauth2.errCb({
                        authId: oauth2.auth.name,
                        source: \"auth\",
                        level: \"error\",
                        message: oauthErrorMsg || \"[Authorization failed]: no accessCode received from the server.\"
                    });
                }
            } else {
                oauth2.callback({auth: oauth2.auth, token: qp, isValid: isValid, redirectUrl: redirectUrl});
            }
            window.close();
        }

        if (document.readyState !== 'loading') {
            run();
        } else {
            document.addEventListener('DOMContentLoaded', function () {
                run();
            });
        }
    </script>
    </body>
    </html>
        "

end LeanFastapi
