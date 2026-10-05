/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellJoined

set_option autoImplicit false

/-!
# The three orbit regions of the fine leaf, and the one fact the certificate lane owes

Layer 4 (`AlgebraicComplexity/Examples/`).  Twelve of the fifteen cells of `[duan2023faster]`'s
section 6.3 leaf now have a fine-route weight (nine off-split, two zero-`Z`, and `(2,2,0)` in
another lane).  The remaining three --- `(1,1,2)`, `(1,2,1)`, `(2,1,1)`, the rows `6`, `7`, `10` of
`dwz63Alpha` --- are the cells with **no** zero coordinate, and they behave differently for a
reason that is structural, not technical.

## Why the plain per-region weight is not available

`T_{1,1,2}` is the unique level-two component that is not a matrix-multiplication tensor.
`Examples/DuanWuZhouLevelTwoConstituentValues.lean` records the consequence for the one route the
tree has: zeroing it onto a direct sum of matrix-multiplication tensors keeps at most `q ^ (2 tau)`
(one off-diagonal block) or `2 q ^ tau` (the two diagonal blocks), both far below the table's
`27.09`.  `[duan2023faster]`'s `note:T112` (`papers/sources/2210.10173/second_power.tex:235`) says
the same thing about the paper: `T_{1,1,2}` "is the only component without a non-rotational value
bound".  So

`HasTauWeight K (orbit region).realize dwz63Tau (published value)` has **no certificate supplied
by the paper or by the committed route**,

and no amount of counting supplies one: it is a statement about the tensor, not about the fibre.
This is a statement about what is available, not an impossibility: neither the paper nor
`Examples/DuanWuZhouLevelTwoConstituentValues.lean:409-430` proves an upper bound on that plain
value or a metatheoretic obstruction to it.  What the paper does supply is the three-symmetrized
value `V^{(3)}` (`papers/sources/2210.10173/second_power.tex:151,255` and
`papers/sources/2210.10173/global_value.tex:341-347`), which is why this formalization takes the
symmetrized route, and why the committed chain
(`exists_eventually_dwz112LeafHasTauWeight`, `Examples/DuanWuZhouLevelTwoLeafTauWeight.lean:454`)
states its weight on `Tensor.power (symThree K (cw112PartitionedTensor K 6).realize) …`.

## Why the committed chain does not already cover these regions

The chain's weight is for the **uncut** power.  The leaf's orbit region is that power *cut* by the
`alphatilde` row on `Z` --- and row `6` is not a point mass: it is the `b`-split
`(b, 1-2b, b)` at mass `2 * 10 ^ 8` (`42030 = 2b * 10 ^ 8`,
`199915940 = 2(1-2b) * 10 ^ 8`), all three letters of coarse degree `2`.  Rows `7` and `10` are the
symmetric degree-`1` split; their `beta` enters through the three-symmetrization, not through the
`Z` split.

A cut object is *smaller* than the uncut one (`Restricts.partitionedSelect`), and `HasTauWeight`
is monotone the other way, so the chain's weight does **not** descend to the region.  Nor can the
region be restricted onto the chain's object: `symThree` of a power is larger still.  The
certificate is attached to `(cw112PartitionedTensor K q).realize` by construction
(`cw112SymmetricCanonicalDegenerationValueCertificate :
CyclicDegenerationCertificate K (cw112PartitionedTensor K q).realize tau`), the typicality lives in
its buckets and survivors, and `RationalTypedLeaf` is pure data --- a profile, coordinates and
dimensions --- never a tensor.  **There is therefore no committed object for the fine orbit region
to be compared with.**

## What this module does, and what it does not

It states the interface, and derives everything downstream of it.  `hcut` below is exactly the
statement the certificate lane must deliver in
`Examples/CoppersmithWinograd112TypedRestriction.lean`: the committed chain's own eventual
`symThree` shape, with the **cut** region in place of the uncut power.  Given it,
`dwz63_symSix_orbitRegionEntry_of_symThree` is a one-line `HasTauWeight.symSix_pow_two`, which is
precisely a region entry of the `sym₆` regional law.

This module does **not** attempt the identification; that is the certificate lane's file and it is
not started here.

## The regional shape this targets

Stage D's `SegmentedRegionalSymSixWeights` asks, for the last region,

`HasTauWeight K (symSix K (P.segmentedLocalizedSplittingPower f s.size M seg
  (SegmentedSplitRestriction.ofLeg c₀ s.type) target).realize) τ s.value`,

so the per-region obligation is at the `sym₆` level, not the plain one --- which is what makes the
orbit cells reachable at all.  Its module is not in the accepted-image list at the time of writing,
so the statements below are phrased against that quoted shape and against the one-segment-supported
type `fun t ↦ if t = t₀ then … else 0` that stage D's cell join uses; if the shape shifts,
only `dwz63OrbitRegion` moves.

Primary source: `[duan2023faster]` --- Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.3 (the level-two global-value
example), `papers/sources/2210.10173/global_value.tex:332-348` (the three orbit rows at
`:341-347`); `note:T112` is the footnote at `papers/sources/2210.10173/second_power.tex:235`, and
`lem:non-rot-values` (d) is `papers/sources/2210.10173/second_power.tex:144-152` (line 151), used
at `:255`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-! ## The three orbit cells -/

/-- The `dwz63Alpha` row index of each orbit cell: `(1,1,2)`, `(1,2,1)`, `(2,1,1)`. -/
def dwz63OrbitRow : Fin 3 → Fin 15 := ![6, 7, 10]

/-- The published logarithmic value of each orbit cell.  `(1,2,1)` and `(2,1,1)` share
`dwz63LogVal121`, evaluated at the free split `beta`, and `dwz63Val121 > dwz63Val112`, so the two
rotations do **not** follow from `(1,1,2)` by `HasTauWeight.mono`. -/
noncomputable def dwz63OrbitLogVal : Fin 3 → ℝ :=
  ![dwz63LogVal112, dwz63LogVal121, dwz63LogVal121]

/-- The coarse target of an orbit region: the constant word of the cell's three degrees. -/
def dwz63OrbitTarget (o : Fin 3) (n : ℕ) :
    BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n) :=
  ofLegs (V := fun _ : Leg ↦ PositiveWord (Fin 5) n)
    (positiveWordConst (![1, 1, 2] o) n) (positiveWordConst (![1, 2, 1] o) n)
    (positiveWordConst (![2, 1, 1] o) n)

/-- **The orbit targets are the committed table's addresses.**  This is the check of the three
degree triples written above against the committed table `dwz63Component`, so that the degrees of
rows `6`, `7`, `10` are not transcribed a second time here but read off the table that already
carries them. -/
theorem dwz63OrbitTarget_eq_component (o : Fin 3) (n : ℕ) (c : Leg) :
    dwz63OrbitTarget o n c = positiveWordConst (dwz63Component (dwz63OrbitRow o) c) n := by
  fin_cases o <;> cases c <;> rfl

/-- The `(1,1,2)` split row has coarse degree `2` on every occurring letter --- the `b`-split. -/
theorem dwz63_alphaTildeDegree_six :
    ∀ p : PositiveWord CWBlock 1, dwz63AlphaTilde 6 p ≠ 0 → cwSquareBlockDegree p = 2 := by
  rintro ⟨x, y⟩ h
  revert h
  cases x <;> cases y <;> decide

/-- The `(1,2,1)` split row has coarse degree `1` on every occurring letter. -/
theorem dwz63_alphaTildeDegree_seven :
    ∀ p : PositiveWord CWBlock 1, dwz63AlphaTilde 7 p ≠ 0 → cwSquareBlockDegree p = 1 := by
  rintro ⟨x, y⟩ h
  revert h
  cases x <;> cases y <;> decide

/-- The `(2,1,1)` split row has coarse degree `1` on every occurring letter. -/
theorem dwz63_alphaTildeDegree_ten :
    ∀ p : PositiveWord CWBlock 1, dwz63AlphaTilde 10 p ≠ 0 → cwSquareBlockDegree p = 1 := by
  rintro ⟨x, y⟩ h
  revert h
  cases x <;> cases y <;> decide

/-! ## The orbit region -/

variable (K : Type u) [CommRing K] (q : ℕ)

/-- **One orbit region of the fine leaf.**  The `M`-segment localized splitting power carried on
the single segment `t₀`, at the orbit cell's coarse target, cut by the proportional refinement of
its `alphatilde` row.  This is the object the certificate lane must weigh. -/
noncomputable def dwz63OrbitRegion (o : Fin 3) {M : ℕ} (t₀ : Fin M) (n j : ℕ) :=
  ((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
    cwSquareDegreeMap n M (fun _ ↦ t₀)
    (SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
      (fun t ↦ if t = t₀ then
        WordType.proportionalCounts (dwz63AlphaTilde (dwz63OrbitRow o)) j else 0))
    (dwz63OrbitTarget o n)

/-! ## The interface, and the one-line step -/

/-- **The `sym₆` region entry from the `sym₃` weight the certificate lane owes.**

`HasTauWeight.symSix_pow_two` and nothing else: a three-symmetrized weight `w` on the region is a
six-symmetrized weight `w ^ 2` on the same region, which is a region entry of
`SegmentedRegionalSymSixWeights` verbatim. -/
theorem dwz63_symSix_orbitRegionEntry_of_symThree (o : Fin 3) {M : ℕ} (t₀ : Fin M) (n j : ℕ)
    {w : ℝ} (hw : 0 ≤ w)
    (hcut : HasTauWeight K (symThree K (dwz63OrbitRegion K q o t₀ n j).realize) dwz63Tau w) :
    HasTauWeight K (symSix K (dwz63OrbitRegion K q o t₀ n j).realize) dwz63Tau (w ^ 2) :=
  hcut.symSix_pow_two hw

/-- **The orbit region entry, in the eventual shape the other twelve cells present.**

`hcut` is the obligation of `Examples/CoppersmithWinograd112TypedRestriction.lean`: the committed
chain's `exists_eventually_dwz112LeafHasTauWeight` shape --- an eventual `symThree` weight --- with
the leaf's **cut** orbit region in place of `Tensor.power (symThree K (cw112PartitionedTensor K
6).realize) (dwz112Mass * k)`, and the published value backed off by an arbitrary positive `eps`
(the deficit convention of the other cells).  `eps` stays a binder here and no comparison with the
certificate lane's own reserve of `10 ^ (-22)` nats is asserted: a client that wants to discharge
`hcut` from that reserve owes the explicit comparison `10 ^ (-22) ≤ eps`, which is a real
condition, not automatic --- it fails for every positive `eps < 10 ^ (-22)`.

Given it, the conclusion is the region entry at
`exp (mass * j * (dwz63OrbitLogVal o - eps)) ^ 6`, matching
`dwz63_exists_joinedFineCellWeight_…` for the other cells. -/
theorem dwz63_exists_symSix_orbitRegionEntry (o : Fin 3) {M : ℕ} (t₀ : Fin M) (ε : ℝ)
    (hcut : ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = 200000000 * j →
      HasTauWeight K (symThree K (dwz63OrbitRegion K q o t₀ n j).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63OrbitLogVal o - ε)) ^ 3)) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = 200000000 * j →
      HasTauWeight K (symSix K (dwz63OrbitRegion K q o t₀ n j).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63OrbitLogVal o - ε)) ^ 6) := by
  obtain ⟨N, hN⟩ := hcut
  refine ⟨N, fun j hj n hn ↦ ?_⟩
  have h := dwz63_symSix_orbitRegionEntry_of_symThree K q o t₀ n j
    (by positivity) (hN j hj n hn)
  rw [← pow_mul] at h
  exact h

end AlgebraicComplexity.Examples
