import Mathlib

open Finset Nat

/-- 
Erdős Problem 13:
Let A ⊆ {1, ..., N} be such that there are no a, b, c ∈ A 
such that a ∣ (b + c) and a < min b c. 
Then |A| ≤ N / 3 + O(1).

Problem definition from: https://www.erdosproblems.com/13
-/
theorem erdos_problem_13 : 
  ∃ C : ℝ, ∀ N : ℕ, ∀ A : Finset ℕ, 
  (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) → 
  (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < min b c → ¬ (a ∣ (b + c))) → 
  (A.card : ℝ) ≤ (N : ℝ) / 3 + C := by
  sorry
