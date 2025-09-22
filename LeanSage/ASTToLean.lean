import Lean
import LeanSage.Core

open Lean Elab Term Meta

namespace LeanSage

-- Convert MathAST to Lean code as a string (much simpler!)
partial def astToLean (ast : MathAST) : String :=
  match ast with
  | .nat n => toString n
  | .int i => toString i
  | .real r => toString r
  | .bool true => "True"
  | .bool false => "False"
  | .string s => s!"\"{s}\""
  | .pi => "Real.pi"
  | .e => "Real.exp 1"
  | .complexI => "Complex.I"
  | .var name _typ => name

  | .add [arg] => astToLean arg
  | .add [lhs, rhs] => s!"({astToLean lhs} + {astToLean rhs})"
  | .add args =>
    let argStrs := args.map astToLean
    s!"({String.intercalate " + " argStrs})"
  | .mul [arg] => astToLean arg
  | .mul [lhs, rhs] => s!"({astToLean lhs} * {astToLean rhs})"
  | .mul args =>
    let argStrs := args.map astToLean
    s!"({String.intercalate " * " argStrs})"
  | .sub lhs rhs => s!"({astToLean lhs} - {astToLean rhs})"
  | .div lhs rhs => s!"({astToLean lhs} / {astToLean rhs})"
  | .pow base exp => s!"({astToLean base} ^ {astToLean exp})"
  | .neg arg => s!"-({astToLean arg})"
  | .abs arg => s!"abs ({astToLean arg})"
  | .mod lhs rhs => s!"({astToLean lhs} % {astToLean rhs})"

  -- Comparison operators
  | .eq lhs rhs => s!"({astToLean lhs} = {astToLean rhs})"
  | .lt lhs rhs => s!"({astToLean lhs} < {astToLean rhs})"
  | .le lhs rhs => s!"({astToLean lhs} ≤ {astToLean rhs})"
  | .gt lhs rhs => s!"({astToLean lhs} > {astToLean rhs})"
  | .ge lhs rhs => s!"({astToLean lhs} ≥ {astToLean rhs})"

  -- Logic operators
  | .and [arg] => astToLean arg
  | .and [lhs, rhs] => s!"({astToLean lhs} ∧ {astToLean rhs})"
  | .and args => s!"({String.intercalate " ∧ " (args.map astToLean)})"
  | .or [arg] => astToLean arg
  | .or [lhs, rhs] => s!"({astToLean lhs} ∨ {astToLean rhs})"
  | .or args => s!"({String.intercalate " ∨ " (args.map astToLean)})"
  | .not arg => s!"¬({astToLean arg})"

  -- Collections and structures
  | .complex real imag => s!"Complex.mk ({astToLean real}) ({astToLean imag})"
  | .list elems =>
    let elemStrs := elems.map astToLean
    s!"[{String.intercalate ", " elemStrs}]"
  | .tuple [a, b] => s!"({astToLean a}, {astToLean b})"
  | .tuple elems =>
    let elemStrs := elems.map astToLean
    s!"({String.intercalate ", " elemStrs})"

  -- Set operations
  | .union lhs rhs => s!"({astToLean lhs} ∪ {astToLean rhs})"
  | .intersection lhs rhs => s!"({astToLean lhs} ∩ {astToLean rhs})"
  | .setDiff lhs rhs => s!"({astToLean lhs} \\ {astToLean rhs})"
  | .membership set elem => s!"({astToLean elem} ∈ {astToLean set})"
  | .subset lhs rhs => s!"({astToLean lhs} ⊆ {astToLean rhs})"
  | .set elems =>
    let elemStrs := elems.map astToLean
    "{" ++ String.intercalate ", " elemStrs ++ "}"
  | .singleton elem => "{" ++ astToLean elem ++ "}"
  | .emptySet => "∅"

  -- Intervals
  | .interval lower upper leftOpen rightOpen =>
    let lowerStr := astToLean lower
    let upperStr := astToLean upper
    match leftOpen, rightOpen with
    | false, false => s!"Set.Icc ({lowerStr}) ({upperStr})"
    | true, true => s!"Set.Ioo ({lowerStr}) ({upperStr})"
    | false, true => s!"Set.Ico ({lowerStr}) ({upperStr})"
    | true, false => s!"Set.Ioc ({lowerStr}) ({upperStr})"

  -- Rational numbers
  | .rat num den =>
    if den == 1 then toString num
    else s!"({num} / {den})"

  -- Matrix construction
  | .matrix rows =>
    let rowStrs := rows.map fun row =>
      let elemStrs := row.map astToLean
      s!"![{String.intercalate ", " elemStrs}]"
    s!"!![{String.intercalate "; " rowStrs}]"

  -- Quantifiers
  | .exists vars body =>
    let varStrs := vars.map (fun (name, typ) => s!"{name} : {astToLean typ}")
    s!"∃ {String.intercalate " " varStrs}, {astToLean body}"

  -- Real/Complex functions
  | .func "sqrt" [arg] => s!"Real.sqrt ({astToLean arg})"
  | .func "sin" [arg] => s!"Real.sin ({astToLean arg})"
  | .func "cos" [arg] => s!"Real.cos ({astToLean arg})"
  | .func "tan" [arg] => s!"Real.tan ({astToLean arg})"
  | .func "exp" [arg] => s!"Real.exp ({astToLean arg})"
  | .func "log" [arg] => s!"Real.log ({astToLean arg})"
  | .func "ln" [arg] => s!"Real.log ({astToLean arg})"
  | .func "real" [arg] => s!"Complex.re ({astToLean arg})"
  | .func "imag" [arg] => s!"Complex.im ({astToLean arg})"

  -- Polynomial functions
  | .func "C" [arg] => s!"C ({astToLean arg})"
  | .func "eval" [poly, x] => s!"eval ({astToLean x}) ({astToLean poly})"
  | .func "eval2" [hom, x, poly] => s!"eval₂ ({astToLean hom}) ({astToLean x}) ({astToLean poly})"
  | .func "degree" [arg] => s!"({astToLean arg}).degree"
  | .func "natDegree" [arg] => s!"({astToLean arg}).natDegree"
  | .func "leadingCoeff" [arg] => s!"({astToLean arg}).leadingCoeff"
  | .func "polyDerivative" [arg] => s!"derivative ({astToLean arg})"
  | .func "coeff" [poly, n] => s!"coeff ({astToLean poly}) ({astToLean n})"
  | .func "monomial" [deg, coeff] => s!"monomial ({astToLean deg}) ({astToLean coeff})"
  | .func "factor" [arg] => s!"({astToLean arg}).factor"
  | .func "roots" [arg] => s!"({astToLean arg}).roots"

  -- Number theory functions
  | .func "natGcd" [a, b] => s!"Nat.gcd ({astToLean a}) ({astToLean b})"
  | .func "gcd" [a, b] => s!"Int.gcd ({astToLean a}) ({astToLean b})"
  | .func "lcm" [a, b] => s!"Nat.lcm ({astToLean a}) ({astToLean b})"
  | .func "factorial" [arg] => s!"Nat.factorial ({astToLean arg})"
  | .func "binomial" [n, k] => s!"Nat.choose ({astToLean n}) ({astToLean k})"
  | .func "euler_phi" [arg] => s!"Nat.totient ({astToLean arg})"
  | .func "is_prime" [arg] => s!"Nat.Prime ({astToLean arg})"
  | .func "prime_factors" [arg] => s!"Nat.primeFactors ({astToLean arg})"
  | .func "divisors" [arg] => s!"Nat.divisors ({astToLean arg})"
  | .func "rising_factorial" [a, n] => s!"Nat.ascFactorial ({astToLean a}) ({astToLean n})"
  | .func "falling_factorial" [a, n] => s!"Nat.descFactorial ({astToLean a}) ({astToLean n})"
  | .func "abs" [arg] => s!"Int.natAbs ({astToLean arg})"

  -- Matrix functions
  | .func "det" [arg] => s!"({astToLean arg}).det"
  | .func "trace" [arg] => s!"({astToLean arg}).trace"
  | .func "transpose" [arg] => s!"({astToLean arg}).transpose"
  | .func "rank" [arg] => s!"({astToLean arg}).rank"
  | .func "identity_matrix" [] => "1"

  -- Collection functions
  | .func "length" [arg] => match arg with
    | .list _ => s!"List.length ({astToLean arg})"
    | .set _ => s!"Finset.card ({astToLean arg})"
    | .string _ => s!"String.length ({astToLean arg})"
    | _ => s!"({astToLean arg}).length"
  | .func "append" [a, b] => s!"({astToLean a}) ++ ({astToLean b})"
  | .func "fst" [arg] => s!"({astToLean arg}).1"
  | .func "snd" [arg] => s!"({astToLean arg}).2"

  -- Polynomials
  | .polynomialVar name => name
  | .polynomialC c => s!"C ({astToLean c})"
  | .monomial var degree coeff =>
    let degreeStr := astToLean degree
    let coeffStr := astToLean coeff
    if degreeStr == "0" then
      s!"C ({coeffStr})"
    else if degreeStr == "1" then
      if coeffStr == "1" then var
      else s!"C ({coeffStr}) * {var}"
    else
      if coeffStr == "1" then s!"{var} ^ {degreeStr}"
      else s!"C ({coeffStr}) * {var} ^ {degreeStr}"

    -- Remove subs function
  | .func "subs" [expr, _eq] => astToLean expr

  -- Rational number functions
  | .func "numer" [arg] => s!"({astToLean arg}).num"
  | .func "denom" [arg] => s!"({astToLean arg}).den"

  -- Calculus functions
  | .func "derivative" [expr, var, order] =>
    match order with
    | .nat 1 => s!"deriv ({astToLean expr}) ({astToLean var})"
    | _ => s!"iteratedDeriv ({astToLean order}) ({astToLean expr}) ({astToLean var})"
  | .func "integral" [expr, var, lower, upper] =>
    s!"∫ {astToLean var} in ({astToLean lower})..({astToLean upper}), {astToLean expr}"
  | .func "integral" [expr, var] =>
    s!"∫ {astToLean var}, {astToLean expr} ∂volume"

  -- Lambda functions
  | .lambda var _varType body =>
    s!"fun {var} => {astToLean body}"

  -- Catch-all for other functions
  | .func name args =>
    let argStrs := args.map astToLean
    s!"{name} ({String.intercalate ") (" argStrs})"

  -- Calculus constructs
  | .derivative expr var order =>
    if order == 1 then
      s!"deriv (fun {var} => {astToLean expr}) "
    else
      s!"iteratedDeriv {order} (fun {var} => {astToLean expr}) "
  | .integral expr var (some lower) (some upper) =>
    s!"∫ {var} in ({astToLean lower})..({astToLean upper}), {astToLean expr}"
  | .integral expr var none none =>
    s!"∫ {var}, {astToLean expr} ∂volume"
  | .integral expr var _ _ =>
    s!"∫ {var}, {astToLean expr}"

  | .apply func args =>
    match func, args with
    | .lambda "t" _ (.derivative expr var order), [xval] =>
      -- Handle derivative evaluation at a point
      if order == 1 then
        s!"deriv (fun {var} => {astToLean expr}) ({astToLean xval})"
      else
        s!"iteratedDeriv {order} (fun {var} => {astToLean expr}) ({astToLean xval})"
    | _, _ =>
      let funcStr := astToLean func
      let argStrs := args.map astToLean
      s!"({funcStr}) ({String.intercalate ") (" argStrs})"

  | _ => "sorry"

def witnessesToLean (witnesses : List MathAST) : String :=
  match witnesses with
  | [] => "()"
  | [w] => astToLean w
  | ws =>
    let witnessStrs := ws.map astToLean
    String.intercalate ", " witnessStrs

end LeanSage
