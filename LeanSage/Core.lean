import Lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Batteries.Data.Rat.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

open Lean Meta

register_option leansage.silent : Bool := {
  defValue := false
  descr := "Suppress info messages"
}

namespace LeanSage

inductive MathAST where
  -- Literals and constants
  | nat (n : Nat)
  | int (n : Int)
  | rat (num : Int) (den : Nat)
  | real (r : Float)
  | bool (b : Bool)
  | string (s : String)
  | pi | e | infinity

  -- Variables and placeholders
  | var (name : String) (typ : String)

  -- Arithmetic operations
  | add (args : List MathAST)
  | mul (args : List MathAST)
  | sub (lhs rhs : MathAST)
  | div (lhs rhs : MathAST)
  | pow (base exp : MathAST)
  | neg (arg : MathAST)
  | abs (arg : MathAST)
  | mod (lhs rhs : MathAST)

  -- Comparison and logic
  | eq (lhs rhs : MathAST)
  | lt (lhs rhs : MathAST)
  | le (lhs rhs : MathAST)
  | gt (lhs rhs : MathAST)
  | ge (lhs rhs : MathAST)
  | and (args : List MathAST)
  | or (args : List MathAST)
  | not (arg : MathAST)

  -- Functions
  | func (name : String) (args : List MathAST)
  | apply (func : MathAST) (args : List MathAST)

  -- Collections
  | list (elems : List MathAST)
  | set (elems : List MathAST)
  | tuple (elems : List MathAST)
  | matrix (rows : List (List MathAST))

  -- Complex numbers
  | complex (real imag : MathAST)
  | complexI

  -- Quantifiers and special forms
  | exists (vars : List (String × MathAST)) (body : MathAST)  -- (name, type) pairs
  | lambda (var : String) (varType : MathAST) (body : MathAST)
  -- | forall_ (vars : List (String × MathAST)) (body : MathAST)  -- (name, type) pairs

  -- Domain-specific constructs
  | polynomialVar (var : String)
  | polynomialC (C : MathAST)
  | monomial (var : String) (degree : MathAST) (coeff : MathAST)
  | derivative (expr : MathAST) (var : String) (order : Nat)
  | integral (expr : MathAST) (var : String) (lower : Option MathAST) (upper : Option MathAST)
  | interval (lower upper : MathAST) (leftOpen rightOpen : Bool)
  | ideal (ring : String) (generators : List MathAST)

  -- Sets and membership
  | membership (elem set : MathAST)
  | subset (lhs rhs : MathAST)
  | union (lhs rhs : MathAST)
  | intersection (lhs rhs : MathAST)
  | setDiff (lhs rhs : MathAST)
  | complement (set : MathAST)
  | emptySet
  | singleton (elem : MathAST)

  -- Hypothesis-related constructs
  | hypothesis (proposition : MathAST)

  deriving Repr, BEq, Inhabited

inductive SageResponse
| success (mathml : String) (plain : String)
| error (msg : String)

end LeanSage
