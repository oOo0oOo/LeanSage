import LeanSage.MathMLToAST

-- Same input and repetition count can be used with an older parser for comparison.
def main : IO Unit := do
  for count in [100, 200, 400, 800] do
    let input := "<list>" ++ String.join (List.replicate count "<item><cn>12</cn></item>") ++ "</list>"
    let start ← IO.monoMsNow
    for _ in [:10] do
      match LeanSage.mathMLToAST input with
      | some (.list values) => unless values.length == count do throw <| IO.userError "Wrong result size"
      | _ => throw <| IO.userError "Parse failed"
    IO.println s!"{count} items, 10 parses: {(← IO.monoMsNow) - start} ms"
