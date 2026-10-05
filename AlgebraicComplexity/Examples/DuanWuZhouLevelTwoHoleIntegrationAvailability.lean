/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedAvailableWordNonempty
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineConfigurationWitness
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFinePairSum
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSegmentationData

set_option autoImplicit false

/-!
# What an available word already knows about its coarse `Z`-word

Layer 4 (`AlgebraicComplexity/Examples/`).  Two facts about
`SegmentedAvailableWord (dwz63Seg K n w) alphaTilde`, both needed by the hole-side integration of
`[duan2023faster]` §6.3's Additional Zeroing-Out Step 2.

## The fifteen rows sit over their own coarse degree

`dwz63AlphaTilde t` (`Examples/DuanWuZhouLevelTwoAlphaTilde.lean`) is a profile on one fine letter
`(k_l, k_r)`, and every row is supported on the pairs whose degrees sum to that cell's `Z`
coordinate --- row `t` splits the `Z`-block of component `t` and nothing else.
`dwz63_alphaTilde_zDegree` is that, checked against the committed table itself rather than assumed:
fifteen rows times nine letters, by destructuring the pair (the type
`PositiveWord CWBlock 1` is not enumerated, only its two digits are).

## Availability therefore *determines* the coarse `Z`-word

A position of segment `t` carries cell `t`'s coarse letter on all three legs
(`dwz63_relabelledAddress_eq_dwz63Cell`, and here directly through
`dwz63Cell_dwz63CellIndex`), and its fine letter is one the segment type gives positive mass to.
The two together say that coarsening an available word on the `Z` leg returns the *reference
word's own* `Z`-word --- `dwz63_coarseZ_of_segmentedAvailable`.  This is what makes an
isolation-deleted word a competitor *through the owner's own large `Z`-block*, which is the
hypothesis `Seed.zHash_eq_of_commonBucket` needs to put the competitor in the owner's bucket.

## `hpos` at the section 6.3 instance

`dwz63_card_segmentedAvailableWord_pos` is residual `R7` of the assembly telescope, discharged
from `card_segmentedAvailableWord_pos`
(`MatrixMultiplication/SegmentedAvailableWordNonempty.lean`) and the reference word's own cell
profile `multiplicity (dwz63Seg K n wRef) t = 2 * 10 ^ 8 * (dwz63Alpha t * s)`, which is exactly
what `dwz63_exists_referenceWord` produces.  The masses match because every row of
`dwz63AlphaTilde` has mass `2 * 10 ^ 8` (`dwz63_profileMass_alphaTilde`).

The split profile is spelled `fun t ↦ proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s)`,
which is `dwz63JoinedAlphaTilde s` by `rfl` (`dwz63JoinedAlphaTilde_apply`).  That module is not
imported here: it is the assembly, and the assembly consumes this file.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3, `global_value.tex` and `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-! ## The support of each split row -/

/-- **Every fine letter the split row `t` charges has cell `t`'s coarse `Z`-degree.**

Checked against the committed fifteen-by-nine table: destructure the fine letter into its two
`CWBlock` digits, then decide each of the one hundred and thirty-five entries. -/
theorem dwz63_alphaTilde_zDegree (t : Fin 15) (k : PositiveWord CWBlock 1)
    (h : dwz63AlphaTilde t k ≠ 0) : cwSquareDegreeMap Leg.Z k = dwz63ZIndex t := by
  revert h
  obtain ⟨l, r⟩ := k
  fin_cases t <;> cases l <;> cases r <;> decide

/-- The same for the joined profile of the assembly, `dwz63JoinedAlphaTilde s`. -/
theorem dwz63_joinedAlphaTilde_zDegree (s : ℕ) (t : Fin 15) (k : PositiveWord CWBlock 1)
    (h : WordType.proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s) k ≠ 0) :
    cwSquareDegreeMap Leg.Z k = dwz63ZIndex t := by
  refine dwz63_alphaTilde_zDegree t k fun hzero ↦ h ?_
  show dwz63AlphaTilde t k * (dwz63Alpha t * s) = 0
  rw [hzero, Nat.zero_mul]

/-! ## Availability determines the coarse `Z`-word -/

/-- **Coarsening an available word on the `Z` leg returns the reference word's `Z`-word.**

Position `i` sits in segment `dwz63CellIndex s`, where `s` is the coarse letter of `w` at `i`; the
segment type gives its fine letter positive mass, so that letter's degree is the cell's `Z`
coordinate, which is `s .Z` because `dwz63CellIndex` is a left inverse of `dwz63Cell` on the
coarse support. -/
theorem dwz63_coarseZ_of_segmentedAvailable (K : Type u) [CommRing K] (n : ℕ)
    (w : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (α : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (hα : ∀ t k, α t k ≠ 0 → cwSquareDegreeMap Leg.Z k = dwz63ZIndex t)
    (z : SegmentedAvailableWord (dwz63Seg K n w) α) :
    positiveWordMap (cwSquareDegreeMap Leg.Z) n z.1 =
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n w Leg.Z := by
  refine (positiveWordEquiv (Fin 5) n).injective ?_
  rw [positiveWordEquiv_map,
    positiveWordEquiv_positiveSupportWordBlockAddress (A := fun _ : Leg ↦ Fin 5)
      ((cwSquarePartitionedTensor K dwz63Q).support) n w Leg.Z]
  funext i
  set zw := positiveWordEquiv (PositiveWord CWBlock 1) n z.1 with hzw
  set ww := positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n w with hww
  set t : Fin 15 := dwz63Seg K n w i with ht
  have hmemi : i ∈ Finset.univ.filter fun j ↦ dwz63Seg K n w j = t ∧ zw j = zw i :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩
  have hcardpos :
      0 < (Finset.univ.filter fun j ↦ dwz63Seg K n w j = t ∧ zw j = zw i).card :=
    Finset.card_pos.mpr ⟨i, hmemi⟩
  have havail : segmentMultiplicity (dwz63Seg K n w) zw t (zw i) = α t (zw i) :=
    congrFun (z.2 t) (zw i)
  have hcard : segmentMultiplicity (dwz63Seg K n w) zw t (zw i) =
      (Finset.univ.filter fun j ↦ dwz63Seg K n w j = t ∧ zw j = zw i).card := rfl
  have hne : α t (zw i) ≠ 0 := by
    rw [← havail, hcard]
    omega
  have hdeg : cwSquareDegreeMap Leg.Z (zw i) = dwz63ZIndex t := hα t (zw i) hne
  have hs : ((ww i : BlockAddress fun _ : Leg ↦ Fin 5)) ∈ cwSquareSupport := (ww i).2
  have hcell : dwz63Cell (dwz63CellIndex ((ww i : BlockAddress fun _ : Leg ↦ Fin 5)))
      = (ww i).1 := dwz63Cell_dwz63CellIndex hs
  show cwSquareDegreeMap Leg.Z (zw i) = (ww i).1 Leg.Z
  rw [hdeg]
  exact congrFun hcell Leg.Z

/-! ## `hpos` at the section 6.3 instance -/

/-- **Residual `R7`: the available alphabet of the section 6.3 reference leaf is nonempty.**

The hypothesis is exactly `dwz63_exists_referenceWord`'s conclusion, and the profile is
`dwz63JoinedAlphaTilde s` up to `rfl`. -/
theorem dwz63_card_segmentedAvailableWord_pos (K : Type u) [CommRing K] (n s : ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hmu : ∀ t : Fin 15,
      WordType.multiplicity (dwz63Seg K n wRef) t = 200000000 * (dwz63Alpha t * s)) :
    0 < Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef)
      (fun t ↦ WordType.proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s))) := by
  refine card_segmentedAvailableWord_pos _ _ fun t ↦ ?_
  have hmass : ∑ k, WordType.proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s) k =
      WordType.profileMass (dwz63AlphaTilde t) * (dwz63Alpha t * s) :=
    WordType.mem_types.mp
      (WordType.proportionalCounts_mem_types (dwz63AlphaTilde t) (dwz63Alpha t * s))
  rw [hmass, dwz63_profileMass_alphaTilde, card_fiber_dwz63Seg, hmu t]

end AlgebraicComplexity.Examples
