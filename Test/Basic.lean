import LeanSage

set_option leansage.silent true
open Polynomial

macro "test_sage" e:term " : " t:term : command =>
  `(/--
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : $t := by sage)

macro "test_sage_witness" e:term " : " t:term : command =>
  `(example : $t := by sage)

macro "test_sage_counterexample" e_:term " : " t:term : command =>
  `(example : $t := by sage)

-- Basic arithmetic
test_sage ex1 : 10 / 2 = 5
test_sage ex2 : 3 + 4 = 7
test_sage ex3 : 6 * 8 = 48
test_sage ex4 : 2^3 = 8

-- Comparisons
test_sage comp1 : 5 < 10
test_sage comp2 : 8 <= 8

-- Logic
test_sage logic1 : True ∧ True
test_sage logic2 : True ∨ False
test_sage logic3 : ¬False

-- Trigonometry
test_sage trig1 : Real.sin 0 = 0
test_sage trig2 : Real.cos 0 = 1

-- Real functions
test_sage real1 : Real.sqrt 4 = 2
test_sage real2 : Real.exp 0 = 1
test_sage real3 : Real.log 1 = 0
test_sage real4 : Real.tan 0 = 0

-- Complex numbers
test_sage complex1 : (Complex.I)^2 = -1
test_sage complex2 : Complex.re (3 + 4 * Complex.I) = 3
test_sage complex3 : Complex.im (3 + 4 * Complex.I) = 4

-- Sets
test_sage set1 : ({1, 2, 3} : Set ℕ) ∪ {3, 4, 5} = {1, 2, 3, 4, 5}
test_sage set2 : (2 : ℕ) ∈ ({1, 2, 3} : Set ℕ)
test_sage set3 : Finset.card ({1, 2, 3} : Finset ℕ) = 3
test_sage set4 : ({1, 2, 3} : Set ℕ) ∩ {2, 3, 4} = {2, 3}
test_sage set5 : ({1, 2, 3} : Set ℕ) \ {2} = {1, 3}
test_sage set6 : ({1, 2} : Set ℕ) ⊆ {1, 2, 3}
test_sage set7 : (4 : ℕ) ∉ ({1, 2, 3} : Set ℕ)
test_sage set8 : (∅ : Set ℕ) ∪ {1, 2} = {1, 2}
test_sage set9 : ({1, 2} : Set ℕ) ∩ ∅ = ∅
test_sage set10 : Finset.card (∅ : Finset ℕ) = 0

-- Matrices
test_sage matrix1 : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det = -2
test_sage matrix2 : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).trace = 5
test_sage matrix3 : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).transpose = !![1, 3; 2, 4]
test_sage matrix4 : (1 : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, 1]
test_sage matrix5 : (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).rank = 2

-- Number theory
test_sage nt1 : Nat.gcd 12 8 = 4
test_sage nt2 : Nat.Prime (2 ^ 607 - 1)
test_sage nt3 : Nat.factorial 5 = 120
test_sage nt4 : Nat.lcm 4 6 = 12
test_sage nt5 : ¬Nat.Prime 8
test_sage nt6 : Nat.totient 10 = 4
test_sage nt7 : Nat.choose 5 2 = 10
test_sage int_gcd : Int.gcd 15 25 = 5
test_sage prime_factors : Nat.primeFactors 12 = {2, 2, 3}
test_sage divisors : Nat.divisors 6 = {1, 2, 3, 6}
test_sage descFactorial : Nat.descFactorial 5 3 = 60
test_sage ascFactorial : Nat.ascFactorial 3 4 = 360
test_sage nat_abs : Int.natAbs (-7) = 7

-- Calculus
test_sage calc1 : deriv (fun x : ℝ => x^2) 3 = 6
test_sage calc2 : ∫ x in (0 : ℝ)..(1 : ℝ), x = 1/2
test_sage calc3 : deriv (fun x : ℝ => x^3) 2 = 12
test_sage calc4 : deriv (fun x : ℝ => Real.sin x) 0 = 1
test_sage calc5 : ∫ x in (0 : ℝ)..(1 : ℝ), x^2 = 1/3
test_sage calc6 : ∫ x in (0 : ℝ)..(Real.pi/2), Real.sin x = 1
test_sage deriv4 : deriv (fun x : ℝ => Real.cos x) 0 = 0
test_sage deriv5 : deriv (fun x : ℝ => Real.exp x) 0 = 1
test_sage fderiv_test : fderiv ℝ (fun x : ℝ => x^2) 3 = 6
test_sage iterated_deriv1 : iteratedDeriv 2 (fun x : ℝ => x^4) 1 = 12
test_sage iterated_deriv2 : iteratedDeriv 3 (fun x : ℝ => Real.exp x) 0 = 1
test_sage indefinite1 : ∫ x : ℝ, x^2 ∂volume = x^3/3
test_sage indefinite2 : ∫ x : ℝ, Real.sin x ∂volume = -Real.cos x
test_sage double_integral1 : ∫ x in (0 : ℝ)..(1 : ℝ), ∫ y in (0 : ℝ)..(1 : ℝ), x * y = 1/4
test_sage complex_integral1 : ∫ x in (0 : ℝ)..(1 : ℝ), x^2 + 2*x + 1 = 7/3

-- Polynomials
test_sage poly1 : eval 2 (X^2 + C 1 : ℝ[X]) = (5 : ℝ)
test_sage poly2 : (X^3 + X^2 + C 1 : ℝ[X]).degree = 3
test_sage poly3 : (X : ℝ[X]) = X
test_sage poly4 : (X^3 + X^2 + C 1 : ℝ[X]).natDegree = 3
test_sage poly5 : (C 5 * X^2 + X : ℝ[X]).leadingCoeff = 5
test_sage poly6 : derivative (X^3 + C 2 * X : ℝ[X]) = (C 3 * X^2 + C 2 : ℝ[X])
test_sage poly7 : (C 5 : ℝ[X]) = C 5
test_sage poly8 : (monomial 2 3 : ℝ[X]) = monomial 2 3
test_sage poly9 : eval₂ (RingHom.id ℝ) 3 (X + C 1 : ℝ[X]) = (4 : ℝ)
test_sage coeff_test : coeff (X^2 + C 3 * X + C 7 : ℝ[X]) 0 = 7
test_sage factor_quadratic : (X^2 - 1 : ℝ[X]).factor = (X - 1) * (X + 1)
test_sage factor_cubic : (X^3 - X : ℝ[X]).factor = X * (X - 1) * (X + 1)
test_sage roots_quadratic : (X^2 - 4 : ℝ[X]).roots = {-2, 2}
test_sage factor_perfect_square : (X^2 + 2*X + 1 : ℚ[X]).factor = (X + 1)^2

-- Ideals
test_sage ideal_membership : (6 : ℤ) ∈ Ideal.span ({2, 3} : Set ℤ)
test_sage ideal_radical : (Ideal.span ({4} : Set ℤ)).radical = Ideal.span ({2} : Set ℤ)

-- Modular arithmetic (Fin)
test_sage fin1 : (1 : Fin 3) + (1 : Fin 3) = (2 : Fin 3)
test_sage fin2 : (2 : Fin 5) + (4 : Fin 5) = (1 : Fin 5)

-- Rational numbers
test_sage rat1 : (3 : ℚ).num = 3
test_sage rat2 : (3/4 : ℚ).den = 4

-- Integer operations
test_sage int1 : Int.ofNat 5 = 5
test_sage int2 : Int.negOfNat 3 = -3
test_sage int3 : Int.natAbs (-7) = 7

-- List operations
test_sage list1 : List.cons 1 List.nil = [1]
test_sage list2 : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5]
test_sage list3 : List.length [1, 2, 3, 4] = 4

-- Array operations
test_sage array1 : Array.mk [1, 2, 3] = #[1, 2, 3]
test_sage array2 : Array.size #[1, 2, 3, 4] = 4
test_sage array3 : #[1, 2] ++ #[3, 4] = #[1, 2, 3, 4]

-- String operations
test_sage string1 : "hello" ++ "world" = "helloworld"
test_sage string2 : String.length "test" = 4

-- Tuples/Products
test_sage tuple1 : (1, 2).1 = 1
test_sage tuple2 : (1, 2).2 = 2
test_sage tuple3 : (1, 2) = Prod.mk 1 2

-- Intervals
test_sage interval1 : (1 : ℝ) ∈ Set.Icc 0 2
test_sage interval2 : (1 : ℝ) ∈ Set.Ioo 0 2
test_sage interval3 : Set.Icc (0:ℝ) 2 ∩ Set.Icc 1 3 = Set.Icc 1 2
test_sage interval4 : (0 : ℝ) ∈ Set.Ico 0 2
test_sage interval5 : (2 : ℝ) ∈ Set.Ioc 0 2
test_sage interval6 : Set.Icc (0:ℝ) 1 ∪ Set.Icc 2 3 = Set.Icc 0 1 ∪ Set.Icc 2 3

-- Lambda functions
test_sage lambda1 : (fun x => x + 1) 5 = 6
test_sage lambda2 : (fun x => x * x) 3 = 9

-- Let expressions
test_sage let1 : (let x := 5; x + 3) = 8
test_sage let2 : (let y := 2 * 3; y + 1) = 7

-- Witness extraction (existentials) - expect info messages
test_sage_witness ex_wit1 : ∃ x : ℕ, x^2 = 9
test_sage_witness ex_wit2 : ∃ x : ℤ, x + 5 = 0
test_sage_witness ex_wit3 : ∃ x : ℝ, x^2 = 2
test_sage_witness wit1 : ∃ x : ℕ, x^3 = 27
test_sage_witness wit2 : ∃ x y : ℝ, x^2 + y^2 = 25
test_sage_witness wit3 : ∃ z : ℂ, z^2 = -1
test_sage_witness wit4 : ∃ x : ℝ, Real.sin x = 1
test_sage_witness exists_perfect_square : ∃ x : ℕ, x^2 = 25
test_sage_witness exists_power_of_two : ∃ x : ℕ, 2^x = 64
test_sage_witness linear_diophantine : ∃ x y : ℚ, 3*x + 5*y = 1

-- Counterexamples for universals
-- test_sage_counterexample c1 : ∀ x : ℕ, x^2 + x + 41 = 0

-- Hypothesis
def pos_sum_gt (a b c : ℝ) (h₁ : a > 0) (h₂ : b > 0) (h₃ : c > 0) : a + b + c > 0 := by sage
