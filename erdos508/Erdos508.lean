/-!
# Erdős Problem 508: the chromatic number of the plane

Source: https://www.erdosproblems.com/508

> What is the chromatic number of the plane? That is, what is the smallest
> number of colours required to colour `ℝ²` such that no two points of the
> same colour are distance `1` apart?

This is also known as the **Hadwiger–Nelson problem**. The problem is open:
an equilateral triangle shows `χ ≥ 3`, small unit-distance graphs (the Moser
spindle, the Golomb graph) show `χ ≥ 4`, Aubrey de Grey (2018) showed
`χ ≥ 5`, and a hexagonal tiling argument of Isbell shows `χ ≤ 7`, so the
best known bounds are `5 ≤ χ ≤ 7`.

## Design of the formalization

This file is intentionally **dependency-free** (it builds with a bare Lean 4
toolchain, no Mathlib), so it cannot use Mathlib's `ℝ`. Instead it is
*axiom-free and assumption-explicit*: we define the class
`CompleteOrderedField` of Dedekind-complete linearly ordered fields — a
classical theorem says any such field is isomorphic to `ℝ`, so the class
characterizes the real numbers up to (unique) isomorphism — and we state the
problem for every model `R` of that class. Since the property "the chromatic
number of the plane over `R` is `n`" transfers along field isomorphisms,
quantifying over all models is faithful to the original problem about `ℝ²`.

Two further notes:

* "Distance `1`" is expressed by the *squared* Euclidean distance being `1`
  (`(p₁ - q₁)² + (p₂ - q₂)² = 1`). For nonnegative reals, `d = 1 ↔ d² = 1`,
  and this avoids needing square roots.
* A colouring with `n` colours is just a function `R × R → Fin n`; no
  regularity (measurability, etc.) is imposed, matching the original problem.
-/

namespace Erdos508

/--
A **Dedekind-complete linearly ordered field**: a field equipped with a
linear order compatible with the field operations, in which every nonempty
set that is bounded above has a least upper bound.

Any two such fields are isomorphic via a unique field isomorphism, and the
real numbers form one, so this class pins down `ℝ` up to canonical
isomorphism.
-/
class CompleteOrderedField (R : Type) extends Add R, Mul R, Neg R, LE R where
  zero : R
  one : R
  /- field axioms (commutative ring with `0 ≠ 1` and inverses for nonzero
  elements; the multiplicative inverse is stated existentially so that the
  structure carries no `⁻¹` operation) -/
  add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, zero + a = a
  neg_add_cancel : ∀ a : R, -a + a = zero
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  mul_comm : ∀ a b : R, a * b = b * a
  one_mul : ∀ a : R, one * a = a
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  zero_ne_one : zero ≠ one
  exists_mul_inv : ∀ a : R, a ≠ zero → ∃ b : R, a * b = one
  /- linear order axioms -/
  le_refl : ∀ a : R, a ≤ a
  le_trans : ∀ a b c : R, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ a b : R, a ≤ b → b ≤ a → a = b
  le_total : ∀ a b : R, a ≤ b ∨ b ≤ a
  /- compatibility of the order with the field operations -/
  add_le_add_left : ∀ a b : R, a ≤ b → ∀ c : R, c + a ≤ c + b
  mul_nonneg : ∀ a b : R, zero ≤ a → zero ≤ b → zero ≤ a * b
  /-- Dedekind completeness: every nonempty set of elements of `R` that is
  bounded above has a least upper bound. (Sets are predicates `R → Prop`.) -/
  exists_lub : ∀ S : R → Prop, (∃ x, S x) → (∃ b, ∀ x, S x → x ≤ b) →
    ∃ u : R, (∀ x, S x → x ≤ u) ∧ ∀ b : R, (∀ x, S x → x ≤ b) → u ≤ b

variable {R : Type}

instance [CompleteOrderedField R] : OfNat R 0 := ⟨CompleteOrderedField.zero⟩
instance [CompleteOrderedField R] : OfNat R 1 := ⟨CompleteOrderedField.one⟩
instance [CompleteOrderedField R] : Sub R := ⟨fun a b => a + -b⟩

/-- The squared Euclidean distance between two points of the plane `R × R`. -/
def sqDist [CompleteOrderedField R] (p q : R × R) : R :=
  (p.1 - q.1) * (p.1 - q.1) + (p.2 - q.2) * (p.2 - q.2)

/-- Two points of the plane are at (Euclidean) distance `1` from each other
iff their squared distance is `1`. -/
def UnitDist [CompleteOrderedField R] (p q : R × R) : Prop :=
  sqDist p q = 1

/--
`PlaneColorable R n` says the plane over `R` can be properly coloured with
`n` colours: there is an assignment of one of `n` colours to every point of
the plane such that no two points at distance `1` receive the same colour.
-/
def PlaneColorable (R : Type) [CompleteOrderedField R] (n : Nat) : Prop :=
  ∃ c : R × R → Fin n, ∀ p q : R × R, UnitDist p q → c p ≠ c q

/--
`IsChromaticNumberOfPlane R n` says `n` is **the** chromatic number of the
plane over `R`: `n` colours suffice, and no smaller number does.
-/
def IsChromaticNumberOfPlane (R : Type) [CompleteOrderedField R] (n : Nat) : Prop :=
  PlaneColorable R n ∧ ∀ m : Nat, PlaneColorable R m → n ≤ m

/--
**Erdős Problem 508** (the Hadwiger–Nelson problem).

What is the chromatic number of the plane? That is, what is the smallest
number of colours required to colour `ℝ²` such that no two points of the
same colour are distance `1` apart?

Formally: `statement n` says that `n` is the chromatic number of the plane
over every Dedekind-complete linearly ordered field (equivalently, over `ℝ`).
The problem asks to determine the (necessarily unique, see
`isChromaticNumberOfPlane_unique`) `n` for which `statement n` holds; it is
open, and the best known bounds are `5 ≤ n ≤ 7`.
-/
def statement (n : Nat) : Prop :=
  ∀ (R : Type) [CompleteOrderedField R], IsChromaticNumberOfPlane R n

/-- The best known lower bound, due to Aubrey de Grey (2018): the plane
cannot be properly coloured with `4` colours, hence `χ(ℝ²) ≥ 5`. -/
def knownLowerBound : Prop :=
  ∀ (R : Type) [CompleteOrderedField R], ¬ PlaneColorable R 4

/-- The best known upper bound, via Isbell's hexagonal tiling argument:
`7` colours suffice, hence `χ(ℝ²) ≤ 7`. -/
def knownUpperBound : Prop :=
  ∀ (R : Type) [CompleteOrderedField R], PlaneColorable R 7

/-!
## Sanity checks

A few easy lemmas confirming that the definitions above behave as intended.
-/

/-- Colourability is monotone in the number of colours. -/
theorem planeColorable_mono [CompleteOrderedField R] {m n : Nat} (h : m ≤ n)
    (hc : PlaneColorable R m) : PlaneColorable R n :=
  match hc with
  | ⟨c, hproper⟩ =>
    ⟨fun p => (c p).castLE h, fun p q hpq heq => by
      have hval : ((c p).castLE h).val = ((c q).castLE h).val := congrArg Fin.val heq
      exact hproper p q hpq (Fin.ext hval)⟩

/-- The plane has a point, so it is not colourable with `0` colours. -/
theorem not_planeColorable_zero (R : Type) [CompleteOrderedField R] :
    ¬ PlaneColorable R 0 :=
  fun ⟨c, _⟩ => (c (0, 0)).elim0

/-- The chromatic number of the plane is unique (so the answer to the
problem, if it exists, is a single natural number). -/
theorem isChromaticNumberOfPlane_unique (R : Type) [CompleteOrderedField R]
    {m n : Nat} (hm : IsChromaticNumberOfPlane R m)
    (hn : IsChromaticNumberOfPlane R n) : m = n :=
  Nat.le_antisymm (hm.2 n hn.1) (hn.2 m hm.1)

end Erdos508
