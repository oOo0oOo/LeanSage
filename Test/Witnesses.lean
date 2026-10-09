import LeanSage
import Lean.Util.CollectAxioms

set_option leansage.silent true

theorem naturalWitness : ∃ x : ℕ, x^2 + 12^2 = 13^2 := by sage
theorem realWitness : ∃ x : ℝ, x^2 - 3*x + 2 = 0 := by sage
theorem rationalWitness : ∃ x y : ℚ, 3*x + 5*y = 1 := by sage
theorem boundedWitness : ∃ x : ℝ, x^3 - 6*x^2 + 11*x - 6 = 0 ∧ 0 < x ∧ x < 5 := by sage

elab "assert_no_sorry " name:ident : command => do
  let axioms ← Lean.collectAxioms name.getId
  if axioms.contains ``sorryAx then
    throwError "Witness proof {name.getId} depends on sorryAx"

assert_no_sorry naturalWitness
assert_no_sorry realWitness
assert_no_sorry rationalWitness
assert_no_sorry boundedWitness
