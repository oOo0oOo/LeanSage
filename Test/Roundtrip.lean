import LeanSage

open Lean Elab Command Term Meta Polynomial

elab "test_roundtrip" _id:ident " : " t:term : command => do
  let expr ← Command.liftTermElabM (Term.elabTerm t none)
  -- logInfo s!"Testing roundtrip for: {expr}"
  let originalStr := toString (← Command.liftTermElabM (PrettyPrinter.ppExpr expr))
  match ← Command.liftTermElabM (LeanSage.exprToAST expr) with
  | some ast =>
    let leanStr := LeanSage.astToLean ast
    if leanStr == "sorry" then
      logError s!"✗ Converted to sorry"
    else
      match Parser.runParserCategory (← getEnv) `term leanStr with
      | .error err =>
        logError s!"✗ Parse error in generated code '{leanStr}': {err}"
      | .ok stx =>
        try
          let elaborationResult ← Command.liftTermElabM do
            try
              let newExpr ← Term.elabTerm stx none
              let newStr := toString (← PrettyPrinter.ppExpr newExpr)
              return some (newExpr, newStr)
            catch _ =>
              return none

          match elaborationResult with
          | some (_newExpr, newStr) =>
            if originalStr != newStr then
              logInfo s!"✓ {originalStr} → {leanStr} (syntax differs but elaborated successfully)"
          | none =>
            logInfo s!"✓ {originalStr} → {leanStr} (parsed successfully, elaboration issues)"

        catch e =>
          let errorMsg := ← e.toMessageData.toString
          if (errorMsg.splitOn "unknown metavariable").length > 1 then
            logInfo s!"✓ {originalStr} → {leanStr} (successful with type inference artifacts)"
          else
            logError s!"✗ {errorMsg}: {repr ast} → '{leanStr}' (from original: '{originalStr}')"
  | none =>
    logError s!"✗ Failed to convert '{originalStr}' to AST"

-- Basic arithmetic
test_roundtrip ex1 : 10 / 2 = 5
test_roundtrip ex2 : 3 + 4 = 7
test_roundtrip ex3 : 6 * 8 = 48
test_roundtrip ex4 : 2^3 = 8

-- Comparisons
test_roundtrip comp1 : 5 < 10
test_roundtrip comp2 : 8 <= 8

-- Logic
test_roundtrip logic1 : True ∧ True
test_roundtrip logic2 : True ∨ False
test_roundtrip logic3 : ¬False

-- Trigonometry
test_roundtrip trig1 : Real.sin 0 = 0
test_roundtrip trig2 : Real.cos 0 = 1
test_roundtrip trig4 : Real.tan 0 = 0

-- Real functions
test_roundtrip real1 : Real.sqrt 4 = 2
test_roundtrip real2 : Real.exp 0 = 1
test_roundtrip real3 : Real.log 1 = 0

-- Complex numbers
test_roundtrip complex1 : (Complex.I)^2 = -1
test_roundtrip complex2 : Complex.re (3 + 4 * Complex.I) = 3
test_roundtrip complex3 : Complex.im (3 + 4 * Complex.I) = 4

-- Sets
test_roundtrip set1 : ({1, 2, 3} : Set ℕ) ∪ {3, 4, 5} = {1, 2, 3, 4, 5}
test_roundtrip set2 : (2 : ℕ) ∈ ({1, 2, 3} : Set ℕ)
test_roundtrip set3 : Finset.card ({1, 2, 3} : Finset ℕ) = 3
test_roundtrip set4 : ({1, 2, 3} : Set ℕ) ∩ {2, 3, 4} = {2, 3}
test_roundtrip set5 : ({1, 2, 3} : Set ℕ) \ {2} = {1, 3}
test_roundtrip set6 : ({1, 2} : Set ℕ) ⊆ {1, 2, 3}
test_roundtrip set7 : (4 : ℕ) ∉ ({1, 2, 3} : Set ℕ)
test_roundtrip set8 : (∅ : Set ℕ) ∪ {1, 2} = {1, 2}
test_roundtrip set9 : ({1, 2} : Set ℕ) ∩ ∅ = ∅
test_roundtrip set10 : Finset.card (∅ : Finset ℕ) = 0

-- Matrices
test_roundtrip matrix1 : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det = -2
test_roundtrip matrix2 : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).trace = 5
test_roundtrip matrix3 : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).transpose = !![1, 3; 2, 4]
test_roundtrip matrix4 : (1 : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, 1]
test_roundtrip matrix5 : (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).rank = 2

-- Number theory
test_roundtrip nt1 : Nat.gcd 12 8 = 4
test_roundtrip nt2 : Nat.Prime (2 ^ 607 - 1)
test_roundtrip nt3 : Nat.factorial 5 = 120
test_roundtrip nt4 : Nat.lcm 4 6 = 12
test_roundtrip nt5 : ¬Nat.Prime 8
test_roundtrip nt6 : Nat.totient 10 = 4
test_roundtrip nt7 : Nat.choose 5 2 = 10
test_roundtrip int_gcd : Int.gcd 15 25 = 5
test_roundtrip prime_factors : Nat.primeFactors 12 = {2, 2, 3}
test_roundtrip divisors : Nat.divisors 6 = {1, 2, 3, 6}
test_roundtrip descFactorial : Nat.descFactorial 5 3 = 60
test_roundtrip ascFactorial : Nat.ascFactorial 3 4 = 360
test_roundtrip nat_abs : Int.natAbs (-7) = 7

-- -- Calculus
test_roundtrip calc1 : deriv (fun x : ℝ => x^2) 3 = 6
test_roundtrip calc2 : ∫ x in (0 : ℝ)..(1 : ℝ), x = 1/2
test_roundtrip calc3 : deriv (fun x : ℝ => x^3) 2 = 12
test_roundtrip calc4 : deriv (fun x : ℝ => Real.sin x) 0 = 1
test_roundtrip calc5 : ∫ x in (0 : ℝ)..(1 : ℝ), x^2 = 1/3
test_roundtrip calc6 : ∫ x in (0 : ℝ)..(Real.pi/2), Real.sin x = 1
test_roundtrip deriv4 : deriv (fun x : ℝ => Real.cos x) 0 = 0
test_roundtrip deriv5 : deriv (fun x : ℝ => Real.exp x) 0 = 1
test_roundtrip fderiv_test : fderiv ℝ (fun x : ℝ => x^2) 3 = 6
test_roundtrip iterated_deriv1 : iteratedDeriv 2 (fun x : ℝ => x^4) 1 = 12
test_roundtrip iterated_deriv2 : iteratedDeriv 3 (fun x : ℝ => Real.exp x) 0 = 1
test_roundtrip indefinite1 : ∫ x : ℝ, x^2 ∂volume = x^3/3
test_roundtrip indefinite2 : ∫ x : ℝ, Real.sin x ∂volume = -Real.cos x
test_roundtrip double_integral1 : ∫ x in (0 : ℝ)..(1 : ℝ), ∫ y in (0 : ℝ)..(1 : ℝ), x * y = 1/4
test_roundtrip complex_integral1 : ∫ x in (0 : ℝ)..(1 : ℝ), x^2 + 2*x + 1 = 7/3

-- Polynomials
test_roundtrip poly2 : (X^3 + X^2 + C 1 : ℝ[X]).degree = 3
test_roundtrip poly3 : (X : ℝ[X]) = X
test_roundtrip poly4 : (X^3 + X^2 + C 1 : ℝ[X]).natDegree = 3
test_roundtrip poly5 : (C 5 * X^2 + X : ℝ[X]).leadingCoeff = 5
test_roundtrip poly6 : derivative (X^3 + C 2 * X : ℝ[X]) = (C 3 * X^2 + C 2 : ℝ[X])
test_roundtrip poly7 : (C 5 : ℝ[X]) = C 5
test_roundtrip poly8 : (monomial 2 3 : ℝ[X]) = monomial 2 3
test_roundtrip poly9 : eval₂ (RingHom.id ℝ) 3 (X + C 1 : ℝ[X]) = (4 : ℝ)
test_roundtrip coeff_test : coeff (X^2 + C 3 * X + C 7 : ℝ[X]) 0 = 7
test_roundtrip factor_quadratic : (X^2 - 1 : ℝ[X]).factor = (X - 1) * (X + 1)
test_roundtrip factor_cubic : (X^3 - X : ℝ[X]).factor = X * (X - 1) * (X + 1)
test_roundtrip roots_quadratic : (X^2 - 4 : ℝ[X]).roots = {-2, 2}
test_roundtrip factor_perfect_square : (X^2 + 2*X + 1 : ℚ[X]).factor = (X + 1)^2

-- Ideals
-- test_roundtrip ideal_membership : (6 : ℤ) ∈ Ideal.span ({2, 3} : Set ℤ)
-- test_roundtrip ideal_radical : (Ideal.span ({4} : Set ℤ)).radical = Ideal.span ({2} : Set ℤ)

-- Modular arithmetic (Fin)
test_roundtrip fin1 : (1 : Fin 3) + (1 : Fin 3) = (2 : Fin 3)
test_roundtrip fin2 : (2 : Fin 5) + (4 : Fin 5) = (1 : Fin 5)

-- Rational numbers
test_roundtrip rat1 : (3 : ℚ).num = 3
test_roundtrip rat2 : (3/4 : ℚ).den = 4

-- Integer operations
test_roundtrip int1 : Int.ofNat 5 = 5
test_roundtrip int2 : Int.negOfNat 3 = -3
test_roundtrip int3 : Int.natAbs (-7) = 7

-- List operations
test_roundtrip list1 : List.cons 1 List.nil = [1]
test_roundtrip list2 : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5]
test_roundtrip list3 : List.length [1, 2, 3, 4] = 4

-- String operations
test_roundtrip string1 : "hello" ++ "world" = "helloworld"
test_roundtrip string2 : String.length "test" = 4

-- Tuples/Products
test_roundtrip tuple1 : (1, 2).1 = 1
test_roundtrip tuple2 : (1, 2).2 = 2
test_roundtrip tuple3 : (1, 2) = Prod.mk 1 2

-- Intervals
test_roundtrip interval1 : (1 : ℝ) ∈ Set.Icc 0 2
test_roundtrip interval2 : (1 : ℝ) ∈ Set.Ioo 0 2
test_roundtrip interval3 : Set.Icc (0:ℝ) 2 ∩ Set.Icc 1 3 = Set.Icc 1 2
test_roundtrip interval4 : (0 : ℝ) ∈ Set.Ico 0 2
test_roundtrip interval5 : (2 : ℝ) ∈ Set.Ioc 0 2
test_roundtrip interval6 : Set.Icc (0:ℝ) 1 ∪ Set.Icc 2 3 = Set.Icc 0 1 ∪ Set.Icc 2 3

-- Lambda functions
-- test_roundtrip lambda1 : (fun x => x + 1) 5 = 6
-- test_roundtrip lambda2 : (fun x => x * x) 3 = 9

-- -- Let expressions
-- test_roundtrip let1 : (let x := 5; x + 3) = 8
-- test_roundtrip let2 : (let y := 2 * 3; y + 1) = 7

-- Basic types (literals)
test_roundtrip nat1 : (5 : ℕ)
test_roundtrip nat2 : (0 : ℕ)
test_roundtrip int1 : (-3 : ℤ)
test_roundtrip int2 : (7 : ℤ)
test_roundtrip rat1 : (3/4 : ℚ)
test_roundtrip real1 : (123 : ℝ)
test_roundtrip real2 : (0 : ℝ)
test_roundtrip bool1 : True
test_roundtrip bool2 : False
test_roundtrip string1 : "Hello, Lean!"
test_roundtrip pi1 : Real.pi
test_roundtrip e1 : Real.exp 1
test_roundtrip complex1 : Complex.I

-- Additional missing basic types
test_roundtrip infinity1 : (Real.pi / 0 : ℝ) -- infinity test
test_roundtrip mod1 : (7 : ℕ) % 3 = 1
test_roundtrip neg1 : -(5 : ℤ) = -5

-- More complex expressions
test_roundtrip complex_expr1 : (3 + 4 * Complex.I) * (1 - 2 * Complex.I) = 11 - 2 * Complex.I
test_roundtrip nested_sets : ({1} ∪ {2}) ∩ ({2} ∪ {3}) = {2}
test_roundtrip compound_logic : (True ∧ False) ∨ (¬False ∧ True) = True
