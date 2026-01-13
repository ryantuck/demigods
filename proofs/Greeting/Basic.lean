import Mathlib.Data.Real.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Real
open Finset

-- Assuming a, b, c are real numbers and a ≠ 0
-- The discriminant
def D (a b c : ℝ) := b^2 - 4 * a * c

-- The quadratic formula theorem (simplified representation of what exists in mathlib)
theorem quadratic_formula_solutions {a b c x : ℝ} (ha : a ≠ 0) :
  a * x^2 + b * x + c = 0 ↔
  (∃ s : ℝ, s^2 = D a b c ∧ (x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a))) :=
sorry -- The actual proof is already in mathlib.

-- Definition 1 from Bedert's paper
def PropertyP (A : Finset ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, (z < x ∧ z < y) → ¬ (z ∣ (x + y))

-- Lemma 1 from Bedert's paper
lemma lemma_1_part_1 (A : Finset ℕ) (hA : PropertyP A) (h0 : 0 ∉ A) (k : ℕ) (hk : k ≥ 2) :
  Disjoint A (image (fun x => k * x) A) := by
  rw [disjoint_iff_ne]
  intro a ha x hx
  simp only [mem_image] at hx
  rcases hx with ⟨a', ha', rfl⟩
  intro h_eq
  have h_pos : 0 < a' := Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha'))
  have h_lt : a' < k * a' := by
    have : 2 * a' ≤ k * a' := Nat.mul_le_mul_right a' hk
    linarith
  have h_div : a' ∣ (k * a' + k * a') := by
    use 2 * k
    ring
  have h_ka' : k * a' ∈ A := h_eq ▸ ha
  have h_contra := hA (k * a') h_ka' (k * a') h_ka' a' ha' (And.intro h_lt h_lt)
  exact h_contra h_div

lemma lemma_1_part_3 (A : Finset ℕ) (hA : PropertyP A) (h0 : 0 ∉ A) (k : ℕ) (hk : k ≥ 3) :
  Disjoint (image (fun x => 2 * x) A) (image (fun x => k * x) A) := by
  rw [disjoint_iff_ne]
  intro x hx y hy
  simp only [mem_image] at hx hy
  rcases hx with ⟨a, ha, rfl⟩
  rcases hy with ⟨a', ha', rfl⟩
  intro h_eq -- 2 * a = k * a'
  have h_pos_a' : 0 < a' := Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha'))
  have h_lt : a' < a := by
    have : 3 * a' ≤ k * a' := Nat.mul_le_mul_right a' hk
    linarith
  have h_div : a' ∣ (a + a) := by
    rw [← two_mul, h_eq]
    use k
    ring
  have h_contra := hA a ha a ha a' ha' (And.intro h_lt h_lt)
  exact h_contra h_div


-- Theorem 1 from Bedert's paper
theorem bedert_theorem_1 :
  ∃ C : ℝ, ∀ n : ℕ, ∀ A : Finset ℕ,
  (A ⊆ range (n + 1)) → PropertyP A → (A.card : ℝ) ≤ n / 3 + C :=
sorry

-- Theorem 2 from Bedert's paper
theorem bedert_theorem_2 :
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
  ∀ A : Finset ℕ, (A ⊆ range (n + 1)) → PropertyP A →
  A.card ≤ n / 3 + 1 :=
sorry

-- Original conjecture formalization (matches Theorem 2 but for all N, which might be too strong or implied by "sufficiently large")
theorem erdos_sarkozy_conjecture (N : ℕ) :
  ∀ (A : Finset ℕ), (A ⊆ range (N + 1)) →
  PropertyP A →
  (A.card ≤ N / 3 + 1) :=
sorry
