/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCofinalIndex

/-!
# General six-orientation letters, and the orbit regrouping counts

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoCofinalIndex.lean`
justified its multiplicities by reading a six-orientation letter as *diagonal* --- the full `S_3`
orbit of a single coarse cell.  **That reading is not available**, and this module replaces it.

## Why the letters must be general

A `symSixPartition` letter is a six-tuple of *independent* coarse cells:
`card_symSixPartition_support` gives `15 ^ 6` letters, not `15`.  The count side forces the general
family.  `hcount` demands `dwz63TrueCopyRate ^ (6 n)` retained blocks, and
`dwz63TrueCopyRate = 2.9718157...` is a rate *per oriented letter*, of which there are `6 n`; so

`log(required) = 6 n * log 2.9718157 = 6.5350 n`.

Diagonal words of length `n` over the fifteen cells number at most `exp(n * H(dwz63Alpha))`, and
`H(dwz63Alpha) = 2.0133` nats, giving `2.0133 n` --- short by `4.5218` nats per symbol, i.e. by a
factor `exp(4.5218 n)`.  General words whose six orientation projections are each
`dwz63Alpha`-typical number `exp(6 n H) = exp(12.0796 n)`, comfortably above `6.5350 n`.  So
`markedWords` is the per-orientation-typical family and every retained constituent is an external
product, in word order, of `6 n` oriented constituents at *independent* cells.

## What survives, and what changes

The **multiplicities are unchanged**: in the diagonal reading each of the `dwz63Alpha i * t`
positions at cell `i` contributed six oriented letters at `i`; in the general reading each of the
six orientations independently carries `dwz63Alpha i * t` letters at cell `i`.  Both give oriented
multiplicity `6 * dwz63Alpha i * t`.  So `six_mul_dwz63CofinalIndex`,
`sum_oriented_multiplicity` and `exp_dwz63LogVal_pow_six_mul_cofinalIndex` remain correct as
stated; only their justification changes, and `six_mul_position_multiplicity` should be read as
the *oriented* count, not a per-position one.

What is new is the **orbit regrouping**.  The three cells of the `(1,1,2)` orbit carry no
non-rotational weight, so their oriented letters cannot be weighed one at a time; they must be
gathered into cyclic triples isomorphic to `sym_3` of the component.  The stabiliser of the
`(1,1,2)` address is `{id, swapXY}`, so each of the three even tags receives exactly
`2 * (alpha_112 + 2 * alpha_121) * t` oriented letters, and the triples number the same.  The
counts below record that partition and the two certificate classes drawn from it.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

/-! ## The three cells of the `(1,1,2)` orbit -/

/-- `alpha` at the `(1,1,2)` cell (component index `6`). -/
def dwz63Alpha112 : ℕ := 20088623

/-- `alpha` at the `(1,2,1)` cell (component index `7`); the `(2,1,1)` cell carries the same
mass. -/
def dwz63Alpha121 : ℕ := 20734458

theorem dwz63Alpha_six : dwz63Alpha 6 = dwz63Alpha112 := by
  decide +kernel

theorem dwz63Alpha_seven : dwz63Alpha 7 = dwz63Alpha121 := by
  decide +kernel

theorem dwz63Alpha_ten : dwz63Alpha 10 = dwz63Alpha121 := by
  decide +kernel

/-! ## Oriented and orbit counts at scale `t` -/

/-- Oriented letters at cell `i`: six orientations, each carrying `dwz63Alpha i * t`. -/
def dwz63OrientedCount (i : Fin 15) (t : ℕ) : ℕ := 6 * (dwz63Alpha i * t)

/-- Oriented letters belonging to the `(1,1,2)` orbit: its three cells together. -/
def dwz63OrbitOrientedCount (t : ℕ) : ℕ := 6 * ((dwz63Alpha112 + 2 * dwz63Alpha121) * t)

theorem dwz63OrbitOrientedCount_eq (t : ℕ) :
    dwz63OrientedCount 6 t + dwz63OrientedCount 7 t + dwz63OrientedCount 10 t =
      dwz63OrbitOrientedCount t := by
  unfold dwz63OrientedCount dwz63OrbitOrientedCount
  rw [dwz63Alpha_six, dwz63Alpha_seven, dwz63Alpha_ten]
  ring

/-- Oriented orbit letters carrying one even tag.  The stabiliser of the `(1,1,2)` address is
`{id, swapXY}`, so each cell hits each of the three even tags exactly twice. -/
def dwz63OrbitTagCount (t : ℕ) : ℕ := 2 * ((dwz63Alpha112 + 2 * dwz63Alpha121) * t)

/-- The three even tags partition the orbit's oriented letters. -/
theorem three_mul_dwz63OrbitTagCount (t : ℕ) :
    3 * dwz63OrbitTagCount t = dwz63OrbitOrientedCount t := by
  unfold dwz63OrbitTagCount dwz63OrbitOrientedCount
  ring

/-- The number of cyclic triples the orbit's oriented letters form: one per even tag class, so
equal to the tag count. -/
def dwz63OrbitTripleCount (t : ℕ) : ℕ := dwz63OrbitTagCount t

/-- Triples assigned the `b`-split certificate of the `(1,1,2)` component. -/
def dwz63BTripleCount (t : ℕ) : ℕ := 2 * (dwz63Alpha112 * t)

/-- Triples assigned the `beta`-split certificate of the `(1,2,1)` and `(2,1,1)` components. -/
def dwz63BetaTripleCount (t : ℕ) : ℕ := 4 * (dwz63Alpha121 * t)

/-- **The two certificate classes exhaust the orbit's triples**, with nothing left over. -/
theorem dwz63BTripleCount_add_dwz63BetaTripleCount (t : ℕ) :
    dwz63BTripleCount t + dwz63BetaTripleCount t = dwz63OrbitTripleCount t := by
  unfold dwz63BTripleCount dwz63BetaTripleCount dwz63OrbitTripleCount dwz63OrbitTagCount
  ring

/-! ## Divisibility at the cofinal index -/

/-- At the cofinal index the scale is `t = Mass * (j + 1)`. -/
theorem dwz63CofinalIndex_scale (Mass j : ℕ) :
    dwz63CofinalIndex Mass j = 100000000 * (Mass * (j + 1)) := by
  unfold dwz63CofinalIndex
  ring

/-- **The `b`-certificate constraint.**  If the certificate's group mass divides `Mass`, it divides
the number of triples assigned to it, so those triples group into whole certificates. -/
theorem bMass_dvd_dwz63BTripleCount {Mb Mass : ℕ} (hMb : Mb ∣ Mass) (j : ℕ) :
    Mb ∣ dwz63BTripleCount (Mass * (j + 1)) := by
  obtain ⟨c, hc⟩ := hMb
  exact ⟨2 * dwz63Alpha112 * (c * (j + 1)), by unfold dwz63BTripleCount; rw [hc]; ring⟩

/-- **The `beta`-certificate constraint**, likewise. -/
theorem betaMass_dvd_dwz63BetaTripleCount {Mbeta Mass : ℕ} (hMbeta : Mbeta ∣ Mass) (j : ℕ) :
    Mbeta ∣ dwz63BetaTripleCount (Mass * (j + 1)) := by
  obtain ⟨c, hc⟩ := hMbeta
  exact ⟨4 * dwz63Alpha121 * (c * (j + 1)), by unfold dwz63BetaTripleCount; rw [hc]; ring⟩

/-- **The oriented letters exhaust `6 n`, in the general reading.**  Summing
`dwz63OrientedCount i t` over the fifteen cells at `t = Mass * (j + 1)` returns
`6 * dwz63CofinalIndex Mass j`. -/
theorem sum_dwz63OrientedCount (Mass j : ℕ) :
    ∑ i, dwz63OrientedCount i (Mass * (j + 1)) = 6 * dwz63CofinalIndex Mass j := by
  unfold dwz63OrientedCount
  have hmass : ∑ i, dwz63Alpha i = 100000000 := by
    simpa [WordType.profileMass] using profileMass_dwz63Alpha
  calc ∑ i, 6 * (dwz63Alpha i * (Mass * (j + 1)))
      = 6 * ((∑ i, dwz63Alpha i) * (Mass * (j + 1))) := by
        rw [Finset.sum_mul, Finset.mul_sum]
    _ = 6 * dwz63CofinalIndex Mass j := by
        rw [hmass, dwz63CofinalIndex_scale]

end AlgebraicComplexity.Examples
