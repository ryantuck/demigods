import Mathlib.Data.Real.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

open Real
open Finset

def PropertyP (A : Finset ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, (z < x ∧ z < y) → ¬ (z ∣ (x + y))

lemma lemma_1_part_1 (A : Finset ℕ) (hA : PropertyP A) (h0 : 0 ∉ A) (k : ℕ) (hk : k ≥ 2) :
  Disjoint A (image (fun x => k * x) A) := by
  rw [disjoint_iff_ne]
  rintro a ha _ hx
  rcases mem_image.mp hx with ⟨a', ha', rfl⟩
  intro h_eq
  have h_pos : 0 < a' := Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha'))
  have h_lt : a' < k * a' := by
    nth_rewrite 1 [← one_mul a']
    apply Nat.mul_lt_mul_of_pos_right _ h_pos
    linarith
  have h_div : a' ∣ (k * a' + k * a') := by
    use 2 * k
    ring
  exact hA (k * a') (h_eq ▸ ha) (k * a') (h_eq ▸ ha) a' ha' ⟨h_lt, h_lt⟩ h_div

lemma lemma_1_part_3 (A : Finset ℕ) (hA : PropertyP A) (h0 : 0 ∉ A) (k : ℕ) (hk : k ≥ 3) :
  Disjoint (image (fun x => 2 * x) A) (image (fun x => k * x) A) := by
  rw [disjoint_iff_ne]
  rintro _ hx _ hy
  rcases mem_image.mp hx with ⟨a, ha, rfl⟩
  rcases mem_image.mp hy with ⟨a', ha', rfl⟩
  intro h_eq
  have h_pos : 0 < a' := Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha'))
  have h_lt : a' < a := by
    have : 2 * a' < 2 * a := by
      rw [h_eq]
      apply Nat.mul_lt_mul_of_pos_right _ h_pos
      linarith
    linarith
  have h_div : a' ∣ (a + a) := by
    rw [← two_mul, h_eq]
    use k
    ring
  exact hA a ha a ha a' ha' ⟨h_lt, h_lt⟩ h_div

lemma bedert_lemma_2 (n : ℕ) (A : Finset ℕ) (hA : PropertyP A)
  (k q a : ℕ) (hk : k ≥ 1) (hq : q ≥ 1) (α : ℝ)
  (B : Finset ℕ) (I : Finset ℕ)
  (h_subset : image (fun x => k * x) B ⊆ I)
  (h_cong : ∀ y ∈ image (fun x => k * x) B, y ≡ a [MOD q])
  (h_kB_multiples : ∀ b ∈ B, ∃ x ∈ A, (x : ℝ) ≤ α * n ∧ x ∣ (k * b))
  (A_alpha_1 : Finset ℕ := A.filter (fun x => α * n < x)) :
  (B.card : ℝ) + ((Finset.image₂ (· + ·) A_alpha_1 A_alpha_1) ∩ I ∩ (I.filter (fun x => x ≡ a [MOD q]))).card < (I.card : ℝ) / q + 1 := by
  sorry

-- Theorem 2 from Bedert's paper (Assumed as base for Theorem 1)
theorem bedert_theorem_2 :
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
  ∀ A : Finset ℕ, (A ⊆ range (n + 1)) → PropertyP A →
  A.card ≤ n / 3 + 1 :=
sorry

-- Theorem 1 from Bedert's paper
theorem bedert_theorem_1 :
  ∃ C : ℝ, ∀ n : ℕ, ∀ A : Finset ℕ,
  (A ⊆ range (n + 1)) → PropertyP A → (A.card : ℝ) ≤ n / 3 + C :=
sorry

theorem erdos_sarkozy_conjecture (N : ℕ) :
  ∀ (A : Finset ℕ), (A ⊆ range (N + 1)) →
  PropertyP A →
  (A.card ≤ N / 3 + 1) :=
sorry
