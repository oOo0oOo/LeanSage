import LeanSage.Core

open LeanSage

namespace LeanSage

-- AST → Sage code translator
partial def astToSage (ast : MathAST) : String :=
  match ast with
  -- Literals and constants
  | .nat n => s!"{n}"
  | .int n => s!"{n}"
  | .real r => s!"{r}"
  | .rat num den => s!"Rational({num}, {den})"
  | .bool true => "True"
  | .bool false => "False"
  | .string s => s!"\"{s}\""
  | .pi => "pi"
  | .e => "e"
  | .infinity => "oo"

  -- Variables
  | .var name _typ => s!"var(\"{name}\")"

  -- Arithmetic operations
  | .add args =>
    let argStrs := args.map astToSage
    s!"({String.intercalate " + " argStrs})"
  | .mul args =>
    let argStrs := args.map astToSage
    s!"({String.intercalate " * " argStrs})"
  | .sub lhs rhs => s!"({astToSage lhs} - {astToSage rhs})"
  | .div lhs rhs => s!"({astToSage lhs} / {astToSage rhs})"
  | .pow base exp => s!"({astToSage base}^{astToSage exp})"
  | .neg arg => s!"-({astToSage arg})"
  | .abs arg => s!"abs({astToSage arg})"
  | .mod lhs rhs => s!"({astToSage lhs} % {astToSage rhs})"

  -- Comparison and logic
  | .eq lhs rhs => s!"{astToSage lhs} == {astToSage rhs}"
  | .lt lhs rhs => s!"{astToSage lhs} < {astToSage rhs}"
  | .le lhs rhs => s!"{astToSage lhs} <= {astToSage rhs}"
  | .gt lhs rhs => s!"{astToSage lhs} > {astToSage rhs}"
  | .ge lhs rhs => s!"{astToSage lhs} >= {astToSage rhs}"
  | .and args =>
    let argStrs := args.map astToSage
    s!"({String.intercalate " and " argStrs})"
  | .or args =>
    let argStrs := args.map astToSage
    s!"({String.intercalate " or " argStrs})"
  | .not arg => s!"not {astToSage arg}"

  -- Functions
  | .func name args =>
    let argStrs := args.map astToSage

    let standardFunc (funcName : String) : String :=
      s!"{funcName}({String.intercalate ", " argStrs})"

    let methodCall (methodName : String) : String :=
      s!"({argStrs[0]!}).{methodName}()"

    match name with
    | "sqrt" | "sin" | "cos" | "tan" | "exp" | "log" | "ln" | "gcd" | "lcm" | "factorial" | "binomial" | "is_prime" | "euler_phi" | "abs" | "falling_factorial" | "rising_factorial" =>
      standardFunc name
    | "real" | "imag" | "numer" | "denom" | "det" | "trace" | "transpose" | "rank" | "inverse" | "charpoly" =>
      methodCall (match name with
        | "numer" => "numer"
        | "denom" => "denom"
        | _ => name)
    | "natGcd" => standardFunc "gcd"
    | "prime_factors" =>
      s!"set([p for p, e in factor({argStrs[0]!}) for _ in range(e)])"
    | "divisors" =>
      s!"set(divisors({argStrs[0]!}))"
    | "diff" => standardFunc "diff"
    | "cons" => s!"[{argStrs[0]!}] + {argStrs[1]!}"
    | "append" => s!"{argStrs[0]!} + {argStrs[1]!}"
    | "length" => s!"len({argStrs[0]!})"
    | "fst" => s!"({argStrs[0]!})[0]"
    | "snd" => s!"({argStrs[0]!})[1]"
    | "subs" =>
      if argStrs.length == 2 then
        s!"({argStrs[0]!}).subs({argStrs[1]!})"
      else
        s!"({argStrs[0]!}).subs({String.intercalate ", " argStrs.tail!})"
    | "radical" =>
      s!"({argStrs[0]!}).radical()"
    | "eval" =>
      s!"({argStrs[0]!}).substitute(X={argStrs[1]!})"
    | "degree" =>
      s!"({argStrs[0]!}).degree(X)"
    | "leadingCoeff" =>
      s!"({argStrs[0]!}).leading_coefficient(X)"
    | "coeff" =>
      s!"({argStrs[0]!}).coefficient(X, {argStrs[1]!})"
    | "C" => argStrs[0]!
    | "polyDerivative" =>
      s!"diff({argStrs[0]!}, X)"
    | "factor" =>
      s!"factor({argStrs[0]!})"
    | "roots" =>
      s!"set([r for r, m in ({argStrs[0]!}).roots()])"
    | "identity_matrix" => "identity_matrix(RR, 2)"
    | _ => standardFunc name

  -- Function application
  | .apply func args =>
    match func with
    | .lambda var _varType body =>
      if args.length == 1 then
        let bodyStr := astToSage body
        let argStr := astToSage args[0]!
        s!"({bodyStr}).substitute({var}={argStr})"
      else
        let funcStr := astToSage func
        let argStrs := args.map astToSage
        s!"({funcStr})({String.intercalate ", " argStrs})"
    | _ =>
      -- Regular function application
      let funcStr := astToSage func
      let argStrs := args.map astToSage
      s!"({funcStr})({String.intercalate ", " argStrs})"

  -- Collections
  | .list elems =>
    let elemStrs := elems.map astToSage
    s!"[{String.intercalate ", " elemStrs}]"
  | .set elems =>
    let elemStrs := elems.map astToSage
    s!"set([{String.intercalate ", " elemStrs}])"
  | .tuple elems =>
    let elemStrs := elems.map astToSage
    s!"({String.intercalate ", " elemStrs})"
  | .matrix rows =>
    let rowStrs := rows.map fun row =>
      let elemStrs := row.map astToSage
      s!"[{String.intercalate ", " elemStrs}]"
    s!"Matrix([{String.intercalate ", " rowStrs}])"

  -- Complex numbers
  | .complex real imag => s!"({astToSage real} + {astToSage imag}*I)"
  | .complexI => "I"

  -- Polynomials
  | .polynomialVar var => s!"var(\"{var}\")"
  | .polynomialC C => astToSage C
  | .monomial var degree coeff =>
    let degreeStr := astToSage degree
    let coeffStr := astToSage coeff
    if degreeStr == "0" then
      s!"{coeffStr}"
    else if degreeStr == "1" then
      s!"{coeffStr}*{var}"
    else
      s!"{coeffStr}*{var}^{degreeStr}"

  -- Quantifiers and special forms
  | .exists vars body =>
    let varNames := vars.map (·.1)
    let bodyStr := astToSage body
    let allTypes := vars.map (fun (_, typeAST) => astToSage typeAST)

    if allTypes.all (· ∈ ["ℤ", "ℕ", "Int", "Nat"]) then
      if varNames.length == 2 then
        s!"solve_diophantine({bodyStr})"
      else
        s!"solve({bodyStr}, [{String.intercalate ", " varNames}], domain=\"integer\")"
    else
      s!"solve({bodyStr}, [{String.intercalate ", " varNames}])"

  | .lambda _ _ body =>
    astToSage body -- handle substitution in .apply case

  -- Domain-specific constructs
  | .derivative expr var order =>
    if order == 1 then
      s!"diff({astToSage expr}, {var})"
    else
      s!"diff({astToSage expr}, {var}, {order})"

  | .integral expr var lower upper =>
    match lower, upper with
    | some l, some u => s!"integral({astToSage expr}, ({var}, {astToSage l}, {astToSage u}))"
    | _, _ => s!"integral({astToSage expr}, {var})"

  | .interval lower upper leftOpen rightOpen =>
    let lowerStr := astToSage lower
    let upperStr := astToSage upper
    match leftOpen, rightOpen with
    | false, false => s!"RealSet.closed({lowerStr}, {upperStr})"
    | true, true => s!"RealSet.open({lowerStr}, {upperStr})"
    | false, true => s!"RealSet.closed_open({lowerStr}, {upperStr})"
    | true, false => s!"RealSet.open_closed({lowerStr}, {upperStr})"

  | .ideal ring generators =>
    let genStrs := generators.flatMap fun gen =>
      match gen with
      | .set elems => elems.map astToSage
      | .singleton elem => [astToSage elem]
      | _ => [astToSage gen]
    let genList := s!"[{String.intercalate ", " genStrs}]"
    match ring with
    | "Int" | "ℤ" => s!"ZZ.ideal({genList})"
    | "Rat" | "ℚ" => s!"QQ.ideal({genList})"
    | "Real" | "ℝ" => s!"RR.ideal({genList})"
    | _ => s!"ZZ.ideal({genList})"

  -- Sets and membership
  | .membership elem set =>
    match set with
    | .ideal ringName generators =>
      let genStrs := generators.flatMap fun gen =>
        match gen with
        | .set elems => elems.map astToSage
        | .singleton elem => [astToSage elem]
        | _ => [astToSage gen]
      let genList := s!"[{String.intercalate ", " genStrs}]"
      let ringPrefix := match ringName with
        | "Int" | "ℤ" => "ZZ"
        | "Rat" | "ℚ" => "QQ"
        | "Real" | "ℝ" => "RR"
        | _ => "ZZ"
      s!"{ringPrefix}.ideal({genList}).reduce({astToSage elem}) == 0"
    | _ => s!"{astToSage set} in {astToSage elem}"
  | .subset lhs rhs => s!"{astToSage lhs}.issubset({astToSage rhs})"
  | .union lhs rhs => s!"{astToSage lhs}.union({astToSage rhs})"
  | .intersection lhs rhs => s!"{astToSage lhs}.intersection({astToSage rhs})"
  | .setDiff lhs rhs => s!"{astToSage lhs}.difference({astToSage rhs})"
  | .complement set => s!"complement({astToSage set})"
  | .emptySet => "set()"
  | .singleton elem => s!"set([{astToSage elem}])"

  | .hypothesis prop =>
    s!"assume({astToSage prop})"

end LeanSage
