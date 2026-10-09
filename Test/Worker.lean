import LeanSage

open LeanSage

private def expect (command expected : String) (assumptions := "") : IO Unit := do
  match ← runSageCommand command assumptions with
  | .success _ result =>
    unless result == expected do throw <| IO.userError s!"{command}: expected {expected}, got {result}"
  | .error error => throw <| IO.userError error

def main : IO Unit := do
  expect "2^10" "1024"
  expect "'λ'" "'λ'"
  expect "(\n2 + 3\n)" "5"
  expect "bool(var('x') > 0)" "True" "assume(var('x') > 0)"
  expect "bool(var('x') > 0)" "False"
  match ← runSageCommand "not_a_sage_function()" with
  | .error _ => pure ()
  | .success _ _ => throw <| IO.userError "Failed to reject an invalid command"
  expect "factorial(5)" "120"
  match ← runSageCommand "__import__('os')._exit(0)" with
  | .error _ => pure ()
  | .success _ _ => throw <| IO.userError "Failed to notice a dead worker"
  expect "factorial(5)" "120"
  for malformed in ["<cn>1</ci>", "<cn>1", "<cn", "<math><cn>1</cn>"] do
    if (mathMLToAST malformed).isSome then
      throw <| IO.userError s!"Accepted malformed MathML: {malformed}"
  unless mathMLToAST "<cn type=\"integer\">12</cn>" == some (.nat 12) do
    throw <| IO.userError "Failed to parse attributed numeric MathML"
  let start ← IO.monoMsNow
  for _ in [:20] do expect "2^10" "1024"
  IO.println s!"Worker, isolation, error recovery and MathML tests passed; 20 warm requests: {(← IO.monoMsNow) - start} ms"
