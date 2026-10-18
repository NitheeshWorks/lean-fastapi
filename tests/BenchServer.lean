import tests.apps.Bench

/-! `lake exe benchserver [port]`: serve the timed fixture (`tests/apps/Bench.lean`)
on 127.0.0.1, default port 8001, to time it over TCP against its Python twin
(`bench_app` in `tests/golden/generate.py`) under uvicorn.

`lake exe benchserver --profile <MiB> <route>`: one upload of that size in
process, each stage timed with the process's resident memory after it. -/

open LeanFastapi

def rssKb (key : String := "VmRSS") : IO Nat := do
  let s ← IO.FS.readFile "/proc/self/status"
  let some l := (s.splitOn "\n").find? (·.startsWith key) | return 0
  return ((l.drop (key.length + 1)).trimAscii.toString.splitOn " ").head!.toNat!

def stage (name : String) (t0 : Nat) : IO Nat := do
  let t ← IO.monoMsNow
  IO.println s!"{name}: {t - t0} ms, RSS {(← rssKb) / 1024} MB, peak {(← rssKb "VmHWM") / 1024} MB"
  pure t

def profile (mib : Nat) (route : String) : IO Unit := do
  let field := if route == "/uploads/" then "files" else "file"
  let n := mib * 1048576
  let data := ByteArray.mk (Array.ofFn (n := n) fun i => (i.val * 2654435761 % 251).toUInt8)
  let head := s!"--b0undary\r\nContent-Disposition: form-data; name=\"{field}\"; filename=\"f\"\r\nContent-Type: application/octet-stream\r\n\r\n".toUTF8
  let body := head ++ data ++ "\r\n--b0undary--\r\n".toUTF8
  let ct := "multipart/form-data; boundary=b0undary"
  let t ← stage "body built" (← IO.monoMsNow)
  let parsed := LeanStarlette.formItems formLimits (some ct) body
  let t ← match parsed with
    | .ok items => stage s!"formItems ({items.length} items)" t
    | .error _ => stage "formItems error" t
  let req : LeanStarlette.Request :=
    { method := "POST", path := route, query_string := ""
      headers := LeanStarlette.Headers.ofList [("content-type", ct)], bodyBytes := body }
  let app := Tests.Bench.app.complete
  let r ← app.call req
  let _ ← stage s!"app.call {r.status_code} {r.text}" t

def main (args : List String) : IO Unit :=
  match args with
  | ["--profile", mib, route] => profile mib.toNat! route
  | _ => Tests.Bench.app.run (port := (args.head? >>= String.toNat?).getD 8001)
