import Lean

def main : IO UInt32 := do
  for file in ["Test/Roundtrip.lean", "Test/Basic.lean", "Test/Witnesses.lean", "Main.lean", "Test/Worker.lean"] do
    IO.println s!"Testing {file}"
    let args := if file == "Test/Worker.lean" then #["env", "lean", "--run", file] else #["env", "lean", file]
    let child ← IO.Process.spawn { cmd := "lake", args, stdin := .null }
    let exitCode ← child.wait
    if exitCode != 0 then return exitCode
  return 0
