import LeanSage

-- set_option leansage.silent true

open Polynomial

-- By default SageMath is used as an oracle. Inserts `sorry` if successful.
def arithmetic : 2^10 = 1024 := by sage
def trigonometry : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by sage
def complex_analysis : Complex.exp (Complex.I * Real.pi) = -1 := by sage
def linear_algebra : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det = -2 := by sage
def calculus : deriv (fun x : ℝ => x^3) 2 = 12 := by sage
def integration : ∫ x in (0 : ℝ)..(Real.pi/2), Real.sin x = 1 := by sage
def number_theory : Nat.gcd 48 18 = 6 := by sage
def polynomials : eval 3 (X^2 - 2*X + 1 : ℝ[X]) = 4 := by sage
def quadratic_roots : (X^2 - 4 : ℝ[X]).roots = {-2, 2} := by sage
def set_theory : ({1, 2} : Set ℕ) ∪ {2, 3} = {1, 2, 3} := by sage
def modular_arithmetic : (7 : Fin 12) * (5 : Fin 12) = (11 : Fin 12) := by sage
def prime_check : Nat.Prime (2 ^ 607 - 1) := by sage
def log_monotone (x y : ℝ) (h₁ : 0 < x) (h₂ : x < y) : Real.log x < Real.log y := by sage
def interval_mem : (2 : ℝ) ∈ Set.Ioc 0 2 := by sage
def ideal_mem : (6 : ℤ) ∈ Ideal.span ({2, 3} : Set ℤ) := by sage

-- SageMath can provide witnesses, resulting in valid Lean proofs
def pythagorean_witness : ∃ x : ℕ, x^2 + 12^2 = 13^2 := by sage
def quadratic_root : ∃ x : ℝ, x^2 - 3*x + 2 = 0 := by sage
def rational_solution : ∃ x y : ℚ, 3*x + 5*y = 1 := by sage
def matrix_eigenvalue : ∃ l : ℝ, (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).det - l * (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).trace + l^2 = 0 := by sage
def complex_root : ∃ z : ℂ, z^2 + 1 = 0 := by sage
def bounded_polynomial_root : ∃ x : ℝ, x^3 - 6*x^2 + 11*x - 6 = 0 ∧ 0 < x ∧ x < 5 := by sage

-- Use the sage% term elaborator to evaluate terms and get a "Try this" suggestion
theorem poly_factorization : (X^2 - 5*X + 6 : ℝ[X]) = sage% (X^2 - 5*X + 6 : ℝ[X]).factor := by grind
theorem poly_integration : ∫ x in (0 : ℝ)..(1), (3*x^2 + 2*x + 1) = sage% ∫ x in (0 : ℝ)..(1), (3*x^2 + 2*x + 1) := by sage

-- SageMath as computation backend
#sage deriv (fun x : ℝ => x^4 - 4*x^3 + 6*x^2 - 4*x + 1) 1
#sage ∫ x in (0 : ℝ)..(Real.pi/4), Real.sin x * Real.cos x
#sage Complex.exp (Complex.I * Real.pi / 3) + Complex.exp (Complex.I * 2 * Real.pi / 3)
#sage eval (Real.pi/4) (X^3 - 3*X + 1 : ℝ[X])
#sage Nat.gcd (Nat.factorial 12) (Nat.factorial 8)
#sage ∫ x in (0 : ℝ)..(1), x^2 * Real.exp x
#sage Matrix.trace ((!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) ^ 3)
#sage eval (Complex.I) (X^2 + 1 : ℂ[X])
#sage ∃ x y : ℚ, 7*x + 5*y = 1

def main : IO Unit :=
  IO.println s!"LeanSage!"
