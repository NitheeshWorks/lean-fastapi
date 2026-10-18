import demo.App

/-! `lake exe example`: serve the milestone 1 demo (`demo/App.lean`) on
http://127.0.0.1:8000. -/

def main : IO Unit := Demo.app.run (port := 8000)
