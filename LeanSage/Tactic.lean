import Lean
import Std.Sync.Mutex
import Lean.Meta.Tactic.TryThis

import LeanSage.Core
import LeanSage.ExprToAST
import LeanSage.ASTToSage
import LeanSage.MathMLToAST
import LeanSage.ProofBuilder

open Lean Elab Tactic Meta Term

namespace LeanSage

abbrev SageChild := IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit }

initialize sageProcess : Std.Mutex (Option SageChild) ← Std.Mutex.new none

private def sageWorker : String :=
"import sys, json, contextlib
import sage.all as sage_all
from sage.repl.preparse import preparse
from sympy.printing.mathml import mathml
def to_mathml(expr):
    if hasattr(expr, '_sympy_'):
        return mathml(expr._sympy_())
    elif hasattr(expr, '__iter__') and not isinstance(expr, str):
        return '<list>' + ''.join(f'<item>{to_mathml(item)}</item>' for item in expr) + '</list>'
    else:
        return repr(expr)
for line in sys.stdin:
    try:
        request = json.loads(line)
        namespace = dict(sage_all.__dict__)
        with contextlib.redirect_stdout(sys.stderr):
            sage_all.forget()
            exec(preparse(request['assumptions']), namespace)
            res = eval(preparse(request['cmd']), namespace)
            result = {'mathml': to_mathml(res), 'result': repr(res)}
    except Exception as e:
        result = {'error': f'{type(e).__name__}: {e}'}
    print(json.dumps(result), flush=True)
"

/-- Serialized access to a persistent, line-framed Sage Python worker. -/
def runSageCommand (cmd : String) (assumptions : String := "") : IO SageResponse :=
  sageProcess.atomically do
    try
      let proc ← match ← get with
        | some proc => pure proc
        | none => do
          let executable := (← IO.getEnv "LEANSAGE_SAGE").getD "sage"
          let proc ← IO.Process.spawn {
            -- The AppImage launcher expands $@ without quotes. Keep the bootstrap
            -- argument free of whitespace and send the actual worker through stdin.
            cmd := executable, args := #["-python", "-u", "-c",
              "exec(__import__('json').loads(__import__('sys').stdin.readline()))"],
            stdin := .piped, stdout := .piped, stderr := .inherit }
          set (some proc)
          proc.stdin.putStrLn (Json.str sageWorker).compress
          proc.stdin.flush
          pure proc
      let request := (Json.mkObj [("cmd", .str cmd), ("assumptions", .str assumptions)]).compress
      proc.stdin.putStrLn request
      proc.stdin.flush
      let line ← proc.stdout.getLine
      if line.isEmpty then
        let _ ← proc.wait
        set (none : Option SageChild)
        return .error "Sage exited before responding"
      match Json.parse line with
      | .error err => return .error s!"JSON parse error: {err}"
      | .ok json =>
        if let .ok (.str msg) := json.getObjVal? "error" then return .error msg
        match json.getObjVal? "mathml", json.getObjVal? "result" with
        | .ok (.str mathml), .ok (.str result) => return .success mathml result
        | _, _ => return .error "Missing mathml/result fields"
    catch e =>
      let failed : Option SageChild ← get
      set (none : Option SageChild)
      if let some child := failed then
        try child.kill; let _ ← child.wait; pure () catch _ => pure ()
      return .error e.toString

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
    if plain == "True" then
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
    let assumptions := String.intercalate "\n" (hyps.map astToSage)
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
