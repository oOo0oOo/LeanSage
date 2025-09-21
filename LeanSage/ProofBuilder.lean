import LeanSage.Core
import LeanSage.MathMLToAST
import LeanSage.ASTToLean
import Lean

open Lean Elab Term Meta

namespace LeanSage

def analyzeProofIntent (ast : MathAST) : String :=
  match ast with
  | .exists _ _ => "witness"
  | .eq _ _ | .lt _ _ | .le _ _ | .gt _ _ | .ge _ _ => "oracle"
  | .and args => if args.any (fun a => match a with | .exists _ _ => true | _ => false) then "witness" else "oracle"
  | .or args => if args.any (fun a => match a with | .exists _ _ => true | _ => false) then "witness" else "oracle"
  | _ => "computation"

-- Extract all equations from nested result structure
private def extractEquations (ast : MathAST) : List MathAST :=
  let rec go (ast : MathAST) : List MathAST :=
    match ast with
    | .eq (.var _ _) _ | .eq _ (.var _ _) => [ast]
    | .list items => items.flatMap go
    | _ => []
  go ast

-- Simplify expressions by substituting parametric variables with concrete values
private def concretize (ast : MathAST) : MathAST :=
  let rec eval (ast : MathAST) : MathAST :=
    match ast with
    | .var name _typ =>
      if (name.startsWith "r" || name.startsWith "t") && (name.drop 1).toList.all Char.isDigit then
        MathAST.nat 0
      else ast
    | .add args => .add (args.map eval)
    | .mul args => .mul (args.map eval)
    | .and args => .and (args.map eval)
    | .or args => .or (args.map eval)
    | .sub a b => .sub (eval a) (eval b)
    | .div a b => .div (eval a) (eval b)
    | .pow a b => .pow (eval a) (eval b)
    | .eq a b => .eq (eval a) (eval b)
    | .lt a b => .lt (eval a) (eval b)
    | .le a b => .le (eval a) (eval b)
    | .gt a b => .gt (eval a) (eval b)
    | .ge a b => .ge (eval a) (eval b)
    | .neg a => .neg (eval a)
    | .abs a => .abs (eval a)
    | .not a => .not (eval a)
    | .func name args => .func name (args.map eval)
    | .apply f args => .apply (eval f) (args.map eval)
    | .complex r i => .complex (eval r) (eval i)
    | .exists vars body => .exists vars (eval body)
    | .lambda var typ body => .lambda var typ (eval body)
    | atom => atom
  eval ast

-- Extract witnesses for existential statements
private def extractWitnesses (originalAST resultAST : MathAST) : Option (List MathAST) :=
  match originalAST with
  | .exists vars _ =>
    let equations := extractEquations resultAST
    if equations.isEmpty then
      -- No solutions found, use type-appropriate defaults
      some (vars.map fun (_, typeAST) =>
        let targetType := astToLean typeAST
        match targetType with
        | "Nat" | "Nat ()" | "ℕ" => MathAST.nat 1
        | "Int" | "Int ()" | "ℤ" => MathAST.int 0
        | "Real" | "Real ()" | "ℝ" => MathAST.real 0.0
        | "Complex" | "Complex ()" | "ℂ" => MathAST.complex (MathAST.real 0.0) (MathAST.real 0.0)
        | _ => MathAST.real 0.0)
    else
      -- Extract witnesses from equations - just take the first valid one per variable
      let witnesses := vars.map fun (varName, typeAST) =>
        let targetType := astToLean typeAST

        -- Find ALL candidate values for this variable
        let candidateValues := equations.filterMap fun eq =>
          match eq with
          | .eq (.var name _) value => if name == varName then some value else none
          | .eq value (.var name _) => if name == varName then some value else none
          | _ => none

        -- For Nat, prefer positive values; otherwise just take first
        match targetType with
        | "Nat" | "Nat ()" | "ℕ" =>
          candidateValues.find? (fun v =>
            let concrete := concretize v
            match concrete with
            | .nat n => n > 0
            | .int i => i > 0
            | _ => false
          ) |>.getD (MathAST.nat 1)
        | _ =>
          candidateValues.head?.map concretize |>.getD (MathAST.real 0.0)
      some witnesses
  | _ => none

def buildProof (originalAST resultAST : MathAST) : TermElabM (Option (List String)) := do
  match analyzeProofIntent originalAST with
  | "witness" =>
    match extractWitnesses originalAST resultAST with
    | some witnesses =>
      let witnessesStr := witnessesToLean witnesses
      return some [s!"use {witnessesStr}", "norm_num"]
    | none => return none
  | _ => return none

end LeanSage
