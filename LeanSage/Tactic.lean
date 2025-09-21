import Lean
import Lean.Meta.Tactic.TryThis

import LeanSage.Core
import LeanSage.ExprToAST
import LeanSage.ASTToSage
import LeanSage.MathMLToAST
import LeanSage.ProofBuilder

open Lean Elab Tactic Meta Term

namespace LeanSage

abbrev SageChild := IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped }

initialize sageProcess : IO.Ref (Option SageChild) ← IO.mkRef none

private def getSageProcess : IO SageChild := do
  match ← sageProcess.get with
  | some proc => return proc
  | none =>
    let proc ← IO.Process.spawn {
      cmd := "sage"
      args := #["-q"]
      stdin := .piped
      stdout := .piped
      stderr := .piped
    }
    sageProcess.set (some proc)
    return proc

private def sageCodeTemplate : String :=
"reset()
import json
from sympy.printing.mathml import mathml
def to_mathml(expr):
    if hasattr(expr, '_sympy_'):
        return mathml(expr._sympy_())
    elif hasattr(expr, '__iter__') and not isinstance(expr, str):
        return '<list>' + ''.join(f'<item>{to_mathml(item)}</item>' for item in expr) + '</list>'
    else:
        return repr(expr)
try:
    {assumptions}
    res = ({cmd})
    a = res[-1] if isinstance(res, tuple) and 'assume' in '{cmd}' else res
    result = {'mathml': to_mathml(a), 'result': repr(a)}
except Exception as e:
    result = {'error': f'{type(e).__name__}: {e}', 'mathml': None, 'result': None}
print(json.dumps(result))

"

private def runSageCommand (cmd : String) (assumptions : String := ""): IO SageResponse := do
  let proc ← getSageProcess
  let py := sageCodeTemplate.replace "{cmd}" cmd |>.replace "{assumptions}" assumptions
  proc.stdin.putStr py
  proc.stdin.flush

  let line ← proc.stdout.getLine
  let jsonResponse := line.trim.replace "sage: " "" |>.replace "....: " ""

  match Lean.Json.parse jsonResponse with
  | .ok json => match json.getObjVal? "error" with
    | .ok errorMsg =>
      match errorMsg.getStr? with
      | .ok msg => return .error msg
      | .error _ => return .error "Parse error"
    | .error _ => match json.getObjVal? "mathml", json.getObjVal? "result" with
      | .ok mathmlJson, .ok resultJson =>
        match mathmlJson.getStr?, resultJson.getStr? with
        | .ok mathml, .ok result => return .success mathml result
        | _, _ => return .error "Invalid mathml/result format"
      | _, _ => return .error "Missing mathml/result fields"
  | .error err => return .error s!"JSON parse error: {err}"

private def handleProof (req : MathAST) (mathml plain sageCode : String) (silent : Bool) (ref : Syntax): TacticM Unit := do
  match LeanSage.analyzeProofIntent req with
  | "witness" =>
    let some resultAST ← pure (LeanSage.mathMLToAST mathml) | throwError s!"Could not parse MathML: {mathml}"
    let some tactics ← LeanSage.buildProof req resultAST | throwError s!"Could not extract witness: {plain} → {repr resultAST}"

    if !silent then
      logInfo s!"SageMath OK: {sageCode} → {plain}"

    let tacticSeq := String.intercalate "; " tactics
    Lean.Meta.Tactic.TryThis.addSuggestion ref tacticSeq

    for tactic in tactics do
      match Parser.runParserCategory (← getEnv) `tactic tactic with
      | .ok syn => evalTactic syn
      | .error err => throwError s!"Invalid tactic '{tactic}': {err}"

  | _ =>
    if (plain.splitOn "True").length > 1 then
      if !silent then logWarning s!"SageMath OK: {sageCode} → {plain}"
      evalTactic (← `(tactic| sorry))
    else
      throwError s!"SageMath failed: {sageCode} → {plain}"

private def getHypotheses : TacticM (List MathAST) := do
  let lctx ← getLCtx
  let mut hyps : List MathAST := []
  for localDecl in lctx.decls do
    if let some decl := localDecl then
      if !decl.isImplementationDetail then
        if ← Meta.isProp decl.type then
          if let some propAST ← LeanSage.exprToAST decl.type then
            hyps := (.hypothesis propAST) :: hyps
  return hyps.reverse

private def buildSageCode (goalAST : MathAST) (hyps : List MathAST) : String × String :=
  match goalAST with
  | .exists vars body =>
    let constraints := hyps.map (fun | .hypothesis prop => prop | ast => ast)
    let transformedAST := .exists vars (constraints.foldl (fun acc h => .and [acc, h]) body)
    ("", astToSage transformedAST)
  | _ =>
    let assumptions := String.intercalate "\n    " (hyps.map astToSage)
    (assumptions, astToSage goalAST)

elab ref:"sage": tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let silent := (← getOptions).getBool `leansage.silent false
    let hyps ← getHypotheses
    let some goalAST ← LeanSage.exprToAST (← goal.getType) | throwError "Failed to convert goal to AST"

    let (assumptions, baseSageCode) := buildSageCode goalAST hyps
    let sageCode := if LeanSage.analyzeProofIntent goalAST == "oracle" then s!"bool({baseSageCode})" else baseSageCode

    match ← runSageCommand sageCode assumptions with
    | .success mathml plain => handleProof goalAST mathml plain sageCode silent ref
    | .error msg => throwError s!"{sageCode} → ERROR: {msg}"

elab "#sage " expr:term : command => do
  let parsedExpr ← Command.liftTermElabM do
    let expr ← Term.elabTerm expr none
    Term.synthesizeSyntheticMVars
    instantiateMVars expr
  let some exprAST ← Command.liftTermElabM (LeanSage.exprToAST parsedExpr) | logError "Cannot translate expression to AST"
  let sageCode := LeanSage.astToSage exprAST

  match ← liftM (runSageCommand sageCode) with
  | .success _ plain => logInfo s!"SageMath result: {sageCode} → {plain}"
  | .error msg => logError s!"SageMath ERROR: {sageCode} → {msg}"

elab "sage%" expr:term : term => do
  let parsedExpr ← elabTerm expr none
  let some exprAST ← LeanSage.exprToAST parsedExpr | throwError "Cannot translate expression to AST"
  let sageCode := LeanSage.astToSage exprAST

  match ← liftM (runSageCommand sageCode) with
  | .success mathml _plain => do
    let some resultAST ← pure (LeanSage.mathMLToAST mathml) | throwError s!"Could not parse MathML: {mathml}"
    let leanResult := LeanSage.astToLean resultAST
    logInfo s!"SageMath OK: {sageCode} → {leanResult}"
    Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) leanResult
    return parsedExpr
  | .error msg => throwError s!"SageMath ERROR: {sageCode} → {msg}"

end LeanSage
