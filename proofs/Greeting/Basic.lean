import Mathlib.Data.Real.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

open Real
open Finset

-- Definition 1
def PropertyP (A : Finset ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, (z < x ∧ z < y) → ¬ (z ∣ (x + y))

-- Section 3: Preliminaries

-- Lemma 1 (1)
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

-- Lemma 1 (2)
lemma lemma_1_part_2 (A : Finset ℕ) (hA : PropertyP A) (h0 : 0 ∉ A) (k : ℕ) (hk : k ≥ 2) :
  PairwiseDisjoint (Set.range (fun (i : ℕ) => image (fun x => k ^ i * x) A)) id := by
  intro s hs t ht h_ne
  rw [Set.mem_range] at hs ht
  rcases hs with ⟨i, rfl⟩
  rcases ht with ⟨j, rfl⟩
  rw [disjoint_iff_ne]
  rintro x hx y hy h_xy
  rcases mem_image.mp hx with ⟨a, ha, rfl⟩
  rcases mem_image.mp hy with ⟨b, hb, rfl⟩
  wlog h_ij : i < j generalizing i j a b
  · exact (this j t ⟨j, rfl⟩ i s ⟨i, rfl⟩ h_ne.symm y hy x hx h_xy.symm (le_of_not_lt h_ij)).symm
  
  have h_pow : k^i ∣ k^j := Nat.pow_dvd_pow k (le_of_lt h_ij)
  rw [h_xy] at h_pow
  have h_div_eq : a = k^(j-i) * b := by
    rw [← Nat.pow_sub_mul_pow k (le_of_lt h_ij)] at h_xy
    apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (Nat.lt_of_succ_le (le_trans (by norm_num) hk)) i) h_xy

  let K := k^(j - i)
  have hK : K ≥ 2 := by
    apply le_trans hk
    apply Nat.le_self_pow (Nat.le_sub_of_add_le (Nat.succ_le_of_lt h_ij)) (by linarith)
    
  have h_inter : ¬ Disjoint A (image (fun x => K * x) A) := by
    rw [disjoint_iff_ne]
    push_neg
    use a, ha, a
    constructor
    · apply mem_image.mpr
      use b, hb
      rw [h_div_eq]
    · rfl
    
  have h_disj_K := lemma_1_part_1 A hA h0 K hK
  contradiction

-- Lemma 1 (3)
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

-- Lemma 2
lemma card_Ico_filter_mode_le (l r q a : ℕ) (hq : q ≥ 1) :
  ((Ico l r).filter (fun x => x ≡ a [MOD q])).card ≤ (r - l + q - 1) / q := by
  let S := (Ico l r).filter (fun x => x ≡ a [MOD q])
  if h : S = ∅ then
    rw [h, card_empty]
    apply Nat.div_nonneg
    linarith
  else
    have h_nonempty : S.Nonempty := Finset.nonempty_of_ne_empty h
    let x_min := S.min' h_nonempty
    let x_max := S.max' h_nonempty
    have h_min_mem : x_min ∈ S := S.min'_mem h_nonempty
    have h_max_mem : x_max ∈ S := S.max'_mem h_nonempty
    
    let f : ℕ → ℕ := fun x => (x - x_min) / q
    
    have h_inj_on : Set.InjOn f S := by
      intro x hx y hy h_eq
      rw [mem_filter] at hx hy
      have h_mod_x : x ≡ x_min [MOD q] := by trans a; exact hx.2; exact h_min_mem.2.symm
      have h_mod_y : y ≡ x_min [MOD q] := by trans a; exact hy.2; exact h_min_mem.2.symm
      
      have h_dvd_x : q ∣ (x - x_min) := Nat.modeq_iff_dvd.mp h_mod_x.symm
      have h_dvd_y : q ∣ (y - x_min) := Nat.modeq_iff_dvd.mp h_mod_y.symm
      
      have h_q_pos : 0 < q := Nat.pos_of_succ_le hq

      rw [Nat.div_eq_iff_eq_mul_left h_q_pos h_dvd_x] at h_eq
      rw [Nat.div_eq_iff_eq_mul_left h_q_pos h_dvd_y] at h_eq
      
      linarith
    
    have h_image_bound : ∀ y ∈ S.image f, y ≤ (x_max - x_min) / q := by
      intro k hk
      rcases mem_image.mp hk with ⟨x, hx, rfl⟩
      apply Nat.div_le_div_right
      apply Nat.sub_le_sub_right
      exact S.le_max' x hx

    let M := (x_max - x_min) / q
    have h_sub : S.image f ⊆ range (M + 1) := by
      intro k hk
      rw [mem_range]
      apply Nat.lt_succ_of_le
      exact h_image_bound k hk
      
    have h_card : S.card ≤ M + 1 := by
      rw [← card_image_of_injOn h_inj_on]
      exact card_le_card h_sub

    have h_gap : (S.card - 1) * q ≤ x_max - x_min := by
      have h_le : S.card - 1 ≤ M := Nat.le_sub_one_of_lt (Nat.lt_succ_of_le h_card)
      apply le_trans (Nat.mul_le_mul_right q h_le)
      apply Nat.div_mul_le_self
    
    rw [mem_filter] at h_min_mem h_max_mem
    have h_min_ge : x_min ≥ l := (mem_Ico.mp h_min_mem.1).1
    have h_max_lt : x_max < r := (mem_Ico.mp h_max_mem.1).2
    
    have h_ineq : (S.card - 1) * q ≤ r - l - 1 := by
      have : x_max - x_min < r - l := by
         apply lt_of_le_of_lt (Nat.sub_le_sub_left h_min_ge x_max)
         apply Nat.sub_lt_sub_right (by linarith) h_max_lt
      apply le_pred_of_lt
      apply lt_of_le_of_lt h_gap this

    if h_pos : r - l > 0 then
      rw [le_div_iff_mul_le (Nat.pos_of_succ_le hq)]
      have h_pred : r - l + q - 1 = (r - l - 1) + q := by
        rw [Nat.add_sub_assoc]
        rw [Nat.add_comm]
        apply Nat.le_pred_of_lt h_pos
      rw [h_pred]
      rw [Nat.add_div (Nat.pos_of_succ_le hq)]
      rw [Nat.div_self (Nat.pos_of_succ_le hq)]
      apply Nat.le_add_of_sub_le h_ineq
    else
      simp at h_pos
      contradiction

lemma bedert_lemma_2 (n : ℕ) (A : Finset ℕ) (hA : PropertyP A)
  (k q a : ℕ) (hk : k ≥ 1) (hq : q ≥ 1) (α : ℝ)
  (B : Finset ℕ) (I : Finset ℕ)
  (hI : ∃ l r, I = Ico l r)
  (h_subset : image (fun x => k * x) B ⊆ I)
  (h_cong : ∀ y ∈ image (fun x => k * x) B, y ≡ a [MOD q])
  (h_kB_multiples : ∀ b ∈ B, ∃ x ∈ A, (x : ℝ) ≤ α * n ∧ x ∣ (k * b))
  (A_alpha_1 : Finset ℕ := A.filter (fun x => α * n < x)) :
  (B.card : ℝ) + ((Finset.image₂ (· + ·) A_alpha_1 A_alpha_1) ∩ I ∩ (I.filter (fun x => x ≡ a [MOD q]))).card < (I.card : ℝ) / q + 1 := by
  
  let kB := image (fun x => k * x) B
  let S2 := (image₂ (· + ·) A_alpha_1 A_alpha_1) ∩ I ∩ (I.filter (fun x => x ≡ a [MOD q]))
  
  have h_inj : Function.Injective (fun x => k * x) := by
    intro x y h
    simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero] at h
    cases h with
    | inl h => exact h
    | inr h => 
      have : k ≠ 0 := by linarith
      contradiction
  have h_kB_card : kB.card = B.card := card_image_of_injective _ h_inj

  have h_disjoint : Disjoint kB S2 := by
    rw [disjoint_iff_ne]
    rintro y hy z hz rfl
    rcases mem_image.mp hy with ⟨b, hb, rfl⟩
    rcases mem_inter.mp (mem_inter.mp hz).1 with ⟨h_sum, _⟩
    rcases mem_image2.mp h_sum with ⟨u, hu, v, hv, rfl⟩
    rw [mem_filter] at hu hv
    rcases hu with ⟨huA, hu_gt⟩
    rcases hv with ⟨hvA, hv_gt⟩
    rcases h_kB_multiples b hb with ⟨x, hxA, hx_le, hx_div⟩
    have h_lt_u : x < u := by
      apply lt_of_le_of_lt _ hu_gt
      exact hx_le
    have h_lt_v : x < v := by
      apply lt_of_le_of_lt _ hv_gt
      exact hx_le
    exact hA u huA v hvA x hxA ⟨h_lt_u, h_lt_v⟩ hx_div

  have h_kB_sub : kB ⊆ I.filter (fun x => x ≡ a [MOD q]) := by
    intro y hy
    rw [mem_filter]
    constructor
    · exact h_subset hy
    · exact h_cong y hy
  
  have h_S2_sub : S2 ⊆ I.filter (fun x => x ≡ a [MOD q]) := by
    intro y hy
    rcases mem_inter.mp hy with ⟨_, h_filt⟩
    exact h_filt

  let Target := I.filter (fun x => x ≡ a [MOD q])
  have h_union_sub : kB ∪ S2 ⊆ Target := union_subset h_kB_sub h_S2_sub
  
  have h_card_sum : kB.card + S2.card = (kB ∪ S2).card := card_union_of_disjoint h_disjoint
  
  rcases hI with ⟨l, r, rfl⟩
  have h_target_card_le : Target.card ≤ (r - l + q - 1) / q := card_Ico_filter_mode_le l r q a hq
  
  have h_target_card_lt : (Target.card : ℝ) < (Ico l r).card / q + 1 := by
    rw [card_Ico]
    have h_bound : ((r - l + q - 1) / q : ℝ) < (r - l : ℝ) / q + 1 := by
       have hq_pos : (q : ℝ) > 0 := Nat.cast_pos.mpr (Nat.pos_of_succ_le hq)
       rw [div_lt_iff hq_pos]
       rw [add_mul, div_mul_cancel _ (ne_of_gt hq_pos)]
       rw [mul_comm ((r - l : ℝ) / q) q, div_mul_cancel _ (ne_of_gt hq_pos)]
       
       have h_floor : ((r - l + q - 1) / q : ℝ) * q ≤ (r - l + q - 1 : ℝ) := by
         rw [← Nat.cast_mul]
         norm_cast
         exact Nat.div_mul_le_self _ _
       
       apply lt_of_le_of_lt h_floor
       norm_cast
       linarith
    
    apply lt_of_le_of_lt _ h_bound
    norm_cast
    exact h_target_card_le

  rw [← h_kB_card]
  apply lt_of_le_of_lt _ h_target_card_lt
  norm_cast
  rw [h_card_sum]
  apply card_le_card h_union_sub

-- Lemma 3
lemma bedert_lemma_3 (U : Finset ℕ) (k m q : ℕ) (a : ℕ)
  (hk : k ≥ 1) (hm : m ≥ 1) (hq : q ≥ 1)
  (h_subset : U ⊆ Ico (k + 1) (k + m + 1))
  (h_card : (U.card : ℝ) ≥ (m : ℝ) / 2 + (q : ℝ) / 2) :
  let U_plus_U := image₂ (· + ·) U U
  (U_plus_U.filter (fun x => x ≡ a [MOD q])).card ≥ (2 / (q : ℝ)) * U.card - 1 :=
sorry

-- Lemma 4
lemma bedert_lemma_4 (U : Finset ℕ) (k d m q : ℕ) (a : ℕ)
  (hk : k ≥ 1) (hd : d ≥ 1) (hm : m ≥ 1) (hq : q ≥ 1)
  (h_coprime : Nat.gcd d q = 1)
  (h_subset : U ⊆ image (fun i => k + i * d) (Ico 1 (m + 1)))
  (h_card : (U.card : ℝ) ≥ (m : ℝ) / 2 + (q : ℝ) / 2) :
  let U_plus_U := image₂ (· + ·) U U
  (U_plus_U.filter (fun x => x ≡ a [MOD q])).card ≥ (2 / (q : ℝ)) * U.card - 1 :=
sorry

-- Helper definitions for Theorem 4
def gcd_star (A : Finset ℤ) : ℕ :=
  if A.Nonempty then
    let diffs := (A.product A).image (fun x => Int.natAbs (x.1 - x.2))
    diffs.gcd id
  else 0

-- Theorem 4 (External Result)
axiom theorem_4 (S T : Finset ℤ) (hS : S.Nonempty) (hT : T.Nonempty) :
  let ST := image₂ (· + ·) S T
  (ST.card ≥ S.card + T.card + min S.card T.card - 3) ∨
  (∃ (Q : Finset ℤ) (d : ℕ),
    d = gcd_star ST ∧
    (∃ (a : ℤ), Q = image (fun i => a + i * d) (Ico 0 (S.card + T.card - 1))) ∧
    Q ⊆ ST
  )

-- Setup for Theorem 5

-- Constants
def δ : ℝ := 1/100
def C : ℝ := 1000000

-- Interval definitions
def A_interval (A : Finset ℕ) (n : ℕ) (α β : ℝ) : Finset ℕ :=
  A.filter (fun x => α * n < x ∧ (x : ℝ) ≤ β * n)

def A_interval_mod (A : Finset ℕ) (n : ℕ) (α β : ℝ) (a q : ℕ) : Finset ℕ :=
  (A_interval A n α β).filter (fun x => x ≡ a [MOD q])

-- Case 1 Skeleton
lemma case_1 (n : ℕ) (A : Finset ℕ) (hP : PropertyP A)
  (h_large : n > 1000000) -- Sufficiently large
  (h_case : (A_interval A n (2/3) 1).card ≥ (2 * n : ℝ) / 9 + 4/3) :
  (A.card : ℝ) ≤ max (⌈(n : ℝ) / 3⌉) ((1/3 - δ) * n + C) := by
  
  let S := A_interval A n (2/3) 1
  let S_Z : Finset ℤ := S.image Int.ofNat
  have hS_card : S_Z.card = S.card := card_image_of_injective _ Int.ofNat.inj
  
  have hS_nonempty : S_Z.Nonempty := by
    rw [← Finset.card_pos, hS_card]
    have : (2 * n : ℝ) / 9 + 4/3 > 0 := by
      apply add_pos
      apply div_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (lt_trans (by norm_num) h_large))) (by norm_num)
      norm_num
    linarith [h_case]
    
  -- Apply Theorem 4
  have h_thm4 := theorem_4 S_Z S_Z hS_nonempty hS_nonempty
  rcases h_thm4 with h_case1 | h_case2
  
  -- Case 4.1: |S+S| >= 3|S| - 3
  · have h_SS_bound : (image₂ (· + ·) S_Z S_Z).card ≤ ⌈(2 * n : ℝ) / 3⌉ := by
      -- S+S subset of (4n/3, 2n]
      sorry
    rw [hS_card] at h_case1
    have h_contra : False := by
       -- 3(2n/9 + 4/3) - 3 = 6n/9 + 4 - 3 = 2n/3 + 1
       -- But |S+S| <= 2n/3 (approx).
       -- Exact logic: |S+S| <= floor(2n) - floor(4n/3).
       -- 2n - 4n/3 = 2n/3.
       -- For large n, this is tight.
       sorry
    contradiction

  -- Case 4.2: Arithmetic Progression
  · rcases h_case2 with ⟨Q, d, hd_eq, ⟨a, hQ_def⟩, hQ_sub⟩
    
    -- Subcase d >= 2
    by_cases hd : d ≥ 2
    · have h_size_bound : (S.card : ℝ) ≤ (n : ℝ) / 6 + 1 := by
         -- S contained in AP of diff d >= 2 in (2n/3, n]
         -- Number of elements is <= length/d + 1
         -- length = n/3.
         -- |S| <= n/6 + 1.
         sorry
      have h_contra : False := by
         -- 2n/9 + 4/3 > n/6 + 1 for large n
         -- 2/9 = 4/18, 1/6 = 3/18.
         -- 4n/18 > 3n/18.
         sorry
      contradiction
      
    -- Subcase d = 1
    have hd1 : d = 1 := by
       have : d ≥ 1 := sorry -- derived from |S| >= 2 which follows from h_case and large n
       linarith
    
    -- Q is interval of length 2|S| - 1
    have hQ_len : Q.card = 2 * S_Z.card - 1 := by
       -- Theorem 4 says length is |S|+|T|-1
       rw [hS_card]
       sorry -- Need to extract length from hQ_def
       
    have h_min_A : ∀ x ∈ A, (x : ℝ) > 4 * n / 9 + 1 := by
       intro x hx
       by_contra h_le
       -- Assume x <= 4n/9 + 1
       -- Q length ~ 2(2n/9) = 4n/9.
       -- Q contains interval of length > 4n/9.
       -- Any number y <= length(Q) has multiple in Q?
       -- Yes, if Q is interval [L, R] and R-L+1 >= y.
       -- Here Q is interval of integers.
       -- Q \subset S+S \subset (4n/3, 2n].
       -- x <= 4n/9+1. Multiple m of x in Q?
       -- x < 4n/3 < m. So x < m.
       -- m = a1+a2. x < a1, a2 (since a1 > 2n/3).
       -- So x | a1+a2 is violation.
       sorry
       
    have hA_nonempty : A.Nonempty := by
       -- S is subset of A, S nonempty.
       exact Finset.nonempty_of_ne_empty (fun h => by rw [h] at hS_nonempty; exact Finset.not_nonempty_empty hS_nonempty)
       
    let s := A.min' hA_nonempty
    have hs_mem : s ∈ A := A.min'_mem hA_nonempty
    have hs_gt : (s : ℝ) > 4 * n / 9 + 1 := h_min_A s hs_mem
    
    -- Bound A
    -- |A| <= 1 + (s-1)/2 + (n - 2s)
    -- |A| <= n + 1/2 - 3s/2
    have h_bound : (A.card : ℝ) ≤ n + 1/2 - 3/2 * s := by
       sorry

    have h_final : (A.card : ℝ) ≤ n / 3 + 1 := by
       -- n + 0.5 - 1.5(4n/9) = n + 0.5 - 2n/3 = n/3 + 0.5
       -- Need to be careful with +1s.
       sorry
       
    apply le_trans h_final
    apply le_max_left


-- Case 2 Skeleton
lemma case_2 (n : ℕ) (A : Finset ℕ) (hP : PropertyP A)
  (h_large : n > 1000000)
  (h_lower : (n : ℝ) / 6 + 24 ≤ (A_interval A n (2/3) 1).card)
  (h_upper : ((A_interval A n (2/3) 1).card : ℝ) < 2 * n / 9 + 4/3) :
  (A.card : ℝ) ≤ max (⌈(n : ℝ) / 3⌉) ((1/3 - δ) * n + C) := by
  
  let S := A_interval A n (2/3) 1
  
  -- Construct B1 from A \cap [2n/3]
  -- B1 \subset (n/3, 2n/3]
  have h_decomp : ∃ B1 : Finset ℕ, B1 ⊆ Ioc (n / 3) (2 * n / 3) ∧ A.card = B1.card + S.card ∧
    (∀ b ∈ B1, ∃ a ∈ A, a ∣ b) ∧
    -- Multiples of B1 properties for Lemma 2
    (∀ b ∈ B1, 3 * b ∈ image (fun x => 3 * x) B1) ∧ -- Trivial, but need structure for 3*B1 and 4*B1
    Disjoint S B1 := by
    -- Proof of B1 construction
    sorry
    
  rcases h_decomp with ⟨B1, hB1_sub, hA_eq, hB1_prop, _, h_disj⟩

  -- Apply Lemma 3 to S with q=12
  -- S \subset (2n/3, n]. Length m = n/3.
  -- Condition: |S| >= m/2 + q/2 = n/6 + 6.
  -- We have |S| >= n/6 + 24.
  have h_lemma3 : ∀ j ∈ range 12, 
    ((image₂ (· + ·) S S).filter (fun x => x ≡ j [MOD 12])).card ≥ (S.card : ℝ) / 6 - 1 := by
    intro j hj
    -- apply bedert_lemma_3
    sorry

  -- Apply Lemma 2 to parts of B1
  -- Split B1 into B1_L (left half) and B1_R (right half)
  -- B1_L \subset (n/3, n/2], B1_R \subset (n/2, 2n/3]
  -- 4*B1_L \subset (4n/3, 2n]. Matches S+S.
  -- 3*B1_R \subset (3n/2, 2n]. Matches S+S.
  
  have h_B1_bound : (B1.card : ℝ) < 2 * n / 3 - 3 * S.card + 20 := by
    -- Derived from summing Lemma 2 inequalities
    sorry
    
  have h_final : (A.card : ℝ) < n / 3 := by
    rw [hA_eq]
    calc (B1.card : ℝ) + S.card 
      _ < (2 * n / 3 - 3 * S.card + 20) + S.card := by linarith
      _ = 2 * n / 3 - 2 * S.card + 20 := by ring
      _ ≤ 2 * n / 3 - 2 * (n / 6 + 24) + 20 := by linarith [h_lower]
      _ = 2 * n / 3 - n / 3 - 48 + 20 := by ring
      _ = n / 3 - 28 := by ring
      _ < n / 3 := by linarith
      
  apply le_trans (le_of_lt h_final)
  apply le_max_left


-- Case 3 Skeleton
lemma case_3 (n : ℕ) (A : Finset ℕ) (hP : PropertyP A)
  (h_large : n > 1000000)
  (h_case : ((A_interval A n (2/3) 1).card : ℝ) < n / 6 + 24) :
  (A.card : ℝ) ≤ max (⌈(n : ℝ) / 3⌉) ((1/3 - δ) * n + C) := by
  
  let S := A_interval A n (2/3) 1
  let A_half := A_interval A n (1/2) 1
  
  -- Partition A_half into mod 3 classes
  let A0 := A_half.filter (fun x => x ≡ 0 [MOD 3])
  let A1 := A_half.filter (fun x => x ≡ 1 [MOD 3])
  let A2 := A_half.filter (fun x => x ≡ 2 [MOD 3])
  
  -- Case 3.1: |A1| + |A2| >= 2/3 |A_half|
  -- Case 3.2: |A0| >= 1/3 |A_half|
  
  have h_split : (A1.card : ℝ) + A2.card ≥ 2/3 * A_half.card ∨ (A0.card : ℝ) ≥ 1/3 * A_half.card := by
    -- |A_half| = |A0| + |A1| + |A2|
    sorry
    
  rcases h_split with h31 | h32
  
  -- Subcase 3.1
  · -- Apply Theorem 4 to A1 + A2
    -- Construct auxiliary sets B2, B3, Z...
    -- Derive bounds
    sorry
    
  -- Subcase 3.2
  · -- Apply Theorem 4 to A0 + A0
    -- Derive bounds
    sorry

-- Theorem 5
theorem theorem_5 :
  ∃ (δ : ℝ) (C : ℝ), δ > 0 ∧
  ∀ (n : ℕ) (A : Finset ℕ), A ⊆ range (n + 1) → PropertyP A →
  (A.card : ℝ) ≤ max (⌈(n : ℝ) / 3⌉) ((1/3 - δ) * n + C) := by
  use δ, C
  constructor
  · simp [δ]; norm_num
  intro n A h_sub hP
  
  by_cases h_large : n > 1000000
  · let S := A_interval A n (2/3) 1
    by_cases h1 : (S.card : ℝ) ≥ 2 * n / 9 + 4/3
    · exact case_1 n A hP h_large h1
    
    by_cases h2 : (S.card : ℝ) ≥ n / 6 + 24
    · push_neg at h1
      exact case_2 n A hP h_large h2 h1
      
    · push_neg at h1 h2
      exact case_3 n A hP h_large h2
  · -- Small n
    apply le_trans _ (le_max_right _ _)
    simp [C]
    have h_card_le : (A.card : ℝ) ≤ n + 1 := by
      norm_cast
      rw [← card_range (n+1)]
      exact card_le_card h_sub
    have h_bound : (n : ℝ) + 1 ≤ (1/3 - 1/100) * n + 1000000 := by
      -- n <= 10^6.
      -- LHS <= 10^6 + 1. RHS >= 0 + 10^6.
      -- Coefficient of n is positive (~0.32).
      -- Wait, if n is small, this holds easily if C is large enough.
      linarith
    linarith

-- Theorem 1 Corollary
theorem bedert_theorem_1 :
  ∃ C' : ℝ, ∀ n : ℕ, ∀ A : Finset ℕ,
  (A ⊆ range (n + 1)) → PropertyP A → (A.card : ℝ) ≤ n / 3 + C' := by
  rcases theorem_5 with ⟨δ, C, hδ, h_thm5⟩
  use max 1 C
  intro n A h_sub hP
  specialize h_thm5 n A h_sub hP
  apply le_trans h_thm5
  apply max_le
  · -- ceil(n/3) <= n/3 + 1
    rw [div_eq_mul_inv]
    calc ⌈(n : ℝ) * 3⁻¹⌉ 
      _ ≤ (n : ℝ) * 3⁻¹ + 1 := ceil_le_add_one _
      _ = (n : ℝ) / 3 + 1 := by rw [div_eq_mul_inv]
      _ ≤ (n : ℝ) / 3 + max 1 C := add_le_add_left (le_max_left _ _) _
  · -- (1/3 - δ)n + C <= n/3 + C
    linarith [h_sub] -- Need to show (1/3-delta)n <= n/3. delta > 0, n >= 0.
    have h_n_nonneg : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
    calc (1/3 - δ) * n + C
      _ = n/3 - δ * n + C := by ring
      _ ≤ n/3 - 0 + C := by 
          apply add_le_add_right
          apply sub_le_sub_left
          apply mul_nonneg (le_of_lt hδ) h_n_nonneg
      _ ≤ n/3 + max 1 C := by simp; apply le_max_right

-- Theorem 2 Corollary
theorem bedert_theorem_2 :
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
  ∀ A : Finset ℕ, (A ⊆ range (n + 1)) → PropertyP A →
  A.card ≤ ⌈(n : ℝ) / 3⌉ := by
  rcases theorem_5 with ⟨δ, C, hδ, h_thm5⟩
  -- Choose N such that (1/3 - δ)n + C <= n/3
  -- C <= δ n <=> n >= C/δ
  let N := Nat.ceil (C / δ)
  use N
  intro n hn A h_sub hP
  specialize h_thm5 n A h_sub hP
  rw [max_eq_left_iff] at h_thm5
  · norm_cast at h_thm5
  · -- Prove (1/3 - δ)n + C <= ceil(n/3)
    -- It suffices to show (1/3 - δ)n + C <= n/3
    rw [div_eq_mul_inv]
    have h_ineq : (1/3 - δ) * n + C ≤ (n : ℝ) * 3⁻¹ := by
      linarith [hn, hδ] -- C <= δ * n
      have : C / δ ≤ n := by
        apply le_trans (le_ceil _)
        norm_cast
      -- n >= C/delta => delta * n >= C
      rw [div_le_iff hδ] at this
      linarith
    apply le_trans h_ineq
    apply le_ceil


