# Erdős Problem 508 — formalized in Lean 4

A formalization of the statement of [Erdős problem 508](https://www.erdosproblems.com/508),
also known as the **Hadwiger–Nelson problem**:

> What is the chromatic number of the plane? That is, what is the smallest
> number of colours required to colour ℝ² such that no two points of the same
> colour are distance 1 apart?

The problem is open. Known bounds: 5 ≤ χ(ℝ²) ≤ 7 (lower bound by Aubrey de
Grey, 2018; upper bound via Isbell's hexagonal tiling).

## Contents

Everything lives in [`Erdos508.lean`](./Erdos508.lean):

- `CompleteOrderedField` — a self-contained axiomatization of a
  Dedekind-complete linearly ordered field. Any such field is isomorphic to
  ℝ, so the class characterizes the reals up to (unique) isomorphism.
- `UnitDist p q` — points `p q : R × R` are at distance 1 (stated via the
  squared distance, avoiding square roots).
- `PlaneColorable R n` — the plane over `R` admits a proper colouring with
  `n` colours (a function `R × R → Fin n` giving distinct colours to points
  at unit distance).
- `IsChromaticNumberOfPlane R n` — `n` colours suffice and no fewer do.
- `Erdos508.statement n` — **the problem**: `n` is the chromatic number of
  the plane over every model of the reals. The problem asks to determine the
  unique such `n`.
- `knownLowerBound` / `knownUpperBound` — statements of the best known
  bounds (χ ≥ 5 and χ ≤ 7).
- A few proved sanity-check lemmas (monotonicity of colourability,
  non-colourability with 0 colours, uniqueness of the chromatic number).

## Design notes

The project is **dependency-free** (no Mathlib), so it builds in seconds
with a bare Lean toolchain. Since ℝ is therefore unavailable, the statement
is made *axiom-free* by quantifying over all Dedekind-complete linearly
ordered fields instead of using a fixed ℝ; this is faithful because the
chromatic number of the plane transfers along field isomorphisms.
`#print axioms` confirms the statement and lemmas depend on no axioms.

For a Mathlib-based version of the same problem (using `EuclideanSpace ℝ (Fin 2)`
and `SimpleGraph.chromaticNumber`), see
[google-deepmind/formal-conjectures, ErdosProblems/508.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/508.lean).

## Building

Requires Lean 4 (the toolchain is pinned to `v4.21.0` in
[`lean-toolchain`](./lean-toolchain); with [elan](https://github.com/leanprover/elan)
installed it is fetched automatically):

```sh
cd erdos508
lake build
```
