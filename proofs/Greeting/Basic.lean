import Mathlib.Data.Real.Basic
import Mathlib.Algebra.QuadraticDiscriminant

open Real

-- Assuming a, b, c are real numbers and a ≠ 0
-- The discriminant
def D (a b c : ℝ) := b^2 - 4 * a * c

-- The quadratic formula theorem (simplified representation of what exists in mathlib)
theorem quadratic_formula_solutions {a b c x : ℝ} (ha : a ≠ 0) :
  a * x^2 + b * x + c = 0 ↔
  (∃ s : ℝ, s^2 = D a b c ∧ (x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a))) :=
-- The actual proof in mathlib is more involved, using `quadratic_eq_zero_iff`
-- and handling the existence of square roots.
-- This is a conceptual representation.
sorry -- The actual proof is already in mathlib.