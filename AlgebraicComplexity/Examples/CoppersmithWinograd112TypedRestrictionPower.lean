/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112TypedRestriction
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellOrbit
import AlgebraicComplexity.Tensor.PartitionedBlockMapPower

set_option autoImplicit false

/-!
# The `(1,1,2)` orbit region of the fine leaf, addressed as a typed cut of the `112` partition

Layer 4 (`AlgebraicComplexity/Examples/`).  This completes the identification recorded as the first
open item of `Examples/DuanWuZhouLevelTwoLeafTauWeight.lean`: the `[duan2023faster]` section 6.3
fine leaf's `(1,1,2)` orbit region — a word-type cut of a power of the **raw** CW square — is
carried exactly onto the corresponding `alphatilde`-typed cut of a power of
`cw112PartitionedTensor`, the object the committed `T_{1,1,2}` value chain is attached to.

The letter-level dictionary and blockwise maps come from
`Examples/CoppersmithWinograd112TypedRestriction.lean`, their propagation through positive powers
from `Tensor/PartitionedBlockMapPower.lean`.  What is added here is the *type transport*: the
dictionary is invertible on the cell (`cw112RawDictInv`), so a `Z`-word has the `alphatilde` type
exactly when its dictionary image has the pushed-forward type, and the two cut supports correspond
bijectively.  Without invertibility only one direction would hold, and the support hypothesis of
`Restricts.partitionedBlockMap` is an equality.

## The two spellings of the region

`dwz63OrbitRegion` (image 104) is a `segmentedLocalizedSplittingPower`, i.e. a `select` of the raw
square's `n`-th power by *two* conditions: a constant coarse target, and the per-segment `Z` type.
The first says exactly that every letter lies in the `(1,1,2)` cell
(`dwz63_orbitTarget_iff_cellKeep`), so the region is the same object as the `alphatilde`-typed cut
of the power of the **cell**; the constant segmentation collapses the per-segment type to a plain
word type (`dwz63_segmentMultiplicity_constSeg`).  The two spellings are related by a support
identity, not definitionally, because `select` normalises differently on the two sides.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3, `note:T112`.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3),
`papers/sources/2210.10173/second_power.tex:234-237` (`note:T112`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The dictionary is invertible on the cell -/

/-- **The inverse block dictionary.**  On each leg it names the raw pair that the `112` block
label stands for. -/
def cw112RawDictInv : ∀ c : Leg, CW112Block c → PositiveWord CWBlock 1
  | .X, .first => (CWBlock.middle, CWBlock.zero)
  | .X, .second => (CWBlock.zero, CWBlock.middle)
  | .Y, .first => (CWBlock.middle, CWBlock.zero)
  | .Y, .second => (CWBlock.zero, CWBlock.middle)
  | .Z, .firstCorner => (CWBlock.zero, CWBlock.last)
  | .Z, .secondCorner => (CWBlock.last, CWBlock.zero)
  | .Z, .grid => (CWBlock.middle, CWBlock.middle)

/-- Every `112` block label is the dictionary image of its inverse. -/
@[simp] theorem cw112RawDict_dictInv (c : Leg) (b : CW112Block c) :
    cw112RawDict c (cw112RawDictInv c b) = b := by
  cases c <;> cases b <;> rfl

/-- The inverse is inverse on the cell letters. -/
theorem cw112RawDictInv_dict (c : Leg) (a : PositiveWord CWBlock 1)
    (ha : cwSquareDegreeMap c a = cwSquare112 c) :
    cw112RawDictInv c (cw112RawDict c a) = a := by
  obtain ⟨x, y⟩ := a
  revert ha
  cases c <;> cases x <;> cases y <;> intro ha <;>
    first
      | rfl
      | exact absurd ha (by decide)

/-- Every inverse image is a cell letter. -/
theorem cw112RawCellKeep_dictInv (c : Leg) (b : CW112Block c) :
    cwSquareDegreeMap c (cw112RawDictInv c b) = cwSquare112 c := by
  cases c <;> cases b <;> rfl

/-! ## The constant segmentation collapses to a plain word type -/

/-- With a constant segmentation there is only one nonempty segment, and its type is the word's
own multiplicity. -/
theorem dwz63_segmentMultiplicity_constSeg {I : Type u} [DecidableEq I] {n m : ℕ}
    (t₀ : Fin m) (word : Fin n → I) (t : Fin m) :
    segmentMultiplicity (fun _ ↦ t₀) word t =
      if t = t₀ then WordType.multiplicity word else 0 := by
  classical
  by_cases h : t = t₀
  · subst h
    rw [if_pos rfl]
    funext a
    unfold segmentMultiplicity WordType.multiplicity
    congr 1
    ext i
    simp
  · rw [if_neg h]
    funext a
    unfold segmentMultiplicity
    have hempty : (Finset.univ.filter fun i ↦ (fun _ ↦ t₀) i = t ∧ word i = a) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨h1, -⟩
      exact h h1.symm
    rw [hempty]
    rfl

/-! ## The coarse target is the letterwise cell condition -/

/-- A word lies over the constant `(1,1,2)` coarse target exactly when each of its letters lies in
the `(1,1,2)` cell. -/
theorem dwz63_orbitTarget_iff_cellKeep (n : ℕ) (c : Leg)
    (word : PositiveWord (PositiveWord CWBlock 1) n) :
    positiveWordMap (cwSquareDegreeMap c) n word = dwz63OrbitTarget 0 n c ↔
      ∀ i, cw112RawCellKeep c (positiveWordEquiv (PositiveWord CWBlock 1) n word i) := by
  constructor
  · intro h i
    have hmap := congrArg (positiveWordEquiv (Fin 5) n) h
    rw [positiveWordEquiv_map] at hmap
    have hconst : dwz63OrbitTarget 0 n c = positiveWordConst (cwSquare112 c) n := by
      cases c <;> rfl
    rw [hconst, positiveWordEquiv_const] at hmap
    exact congrFun hmap i
  · intro h
    refine (positiveWordEquiv (Fin 5) n).injective ?_
    have hconst : dwz63OrbitTarget 0 n c = positiveWordConst (cwSquare112 c) n := by
      cases c <;> rfl
    rw [positiveWordEquiv_map, hconst, positiveWordEquiv_const]
    funext i
    exact h i

/-! ## The cell power and the region -/

variable (K : Type u) [CommRing K] (q : ℕ)

/-- The `(1,1,2)` cell of the raw square, as a partitioned tensor. -/
noncomputable abbrev cw112RawCell :=
  ((cwPartitionedTensor K q).positivePower 1).select cw112RawCellKeep

/-- Membership in a power of the cell is membership in the power of the raw square together with
the letterwise cell condition. -/
theorem dwz63_mem_orbitCellPower_support_iff :
    ∀ (n : ℕ) (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)),
      s ∈ ((cw112RawCell K q).positivePower n).support ↔
        s ∈ (((cwPartitionedTensor K q).positivePower 1).positivePower n).support ∧
          ∀ c i, cw112RawCellKeep c
            (positiveWordEquiv (PositiveWord CWBlock 1) n (s c) i)
  | 0, s =>
      ⟨fun hs ↦
        ⟨((PartitionedTensor.mem_select_support
            ((cwPartitionedTensor K q).positivePower 1) cw112RawCellKeep s).mp hs).1,
          fun c i ↦ by
            refine Fin.cases ?_ (fun k ↦ k.elim0) i
            exact ((PartitionedTensor.mem_select_support
              ((cwPartitionedTensor K q).positivePower 1) cw112RawCellKeep s).mp hs).2 c⟩,
        fun h ↦ (PartitionedTensor.mem_select_support
          ((cwPartitionedTensor K q).positivePower 1) cw112RawCellKeep s).mpr
          ⟨h.1, fun c ↦ h.2 c 0⟩⟩
  | n + 1, s => by
      rw [mem_positivePower_succ_support, mem_positivePower_succ_support,
        dwz63_mem_orbitCellPower_support_iff n, PartitionedTensor.mem_select_support]
      constructor
      · rintro ⟨⟨hleft, hkeepleft⟩, hright, hkeepright⟩
        refine ⟨⟨hleft, hright⟩, fun c i ↦ ?_⟩
        refine Fin.lastCases ?_ (fun k ↦ ?_) i
        · simpa [positiveWordEquiv_succ_apply] using hkeepright c
        · simpa [positiveWordEquiv_succ_apply] using hkeepleft c k
      · rintro ⟨⟨hleft, hright⟩, hkeep⟩
        refine ⟨⟨hleft, fun c k ↦ ?_⟩, hright, fun c ↦ ?_⟩
        · have := hkeep c k.castSucc
          simpa [positiveWordEquiv_succ_apply] using this
        · have := hkeep c (Fin.last (n + 1))
          simpa [positiveWordEquiv_succ_apply] using this

/-! ## The typed cut on the `112` side -/

/-- The per-segment `Z` profile of the orbit region, pushed forward along the dictionary. -/
noncomputable def cw112PushedOrbitProfile {M : ℕ} (t₀ : Fin M) (j : ℕ) :
    Fin M → CW112Block Leg.Z → ℕ :=
  fun t ↦ if t = t₀ then
    WordType.mappedType (cw112RawDict Leg.Z)
      (WordType.proportionalCounts (dwz63AlphaTilde 6) j) else 0

/-- **The `alphatilde`-typed cut of the `112` partition's `n`-th power.**  This is the object the
committed `T_{1,1,2}` chain's survivors live in. -/
noncomputable def cw112TypedCut {M : ℕ} (t₀ : Fin M) (n j : ℕ) :=
  ((cw112PartitionedTensor K q).positivePower n).select
    ((SegmentedSplitRestriction.ofLeg (A := CW112Block) Leg.Z
      (cw112PushedOrbitProfile t₀ j)).Keeps n (fun _ ↦ t₀))

noncomputable instance cw112TypedCutKeepDecidable {M : ℕ} (t₀ : Fin M) (n : ℕ) (j : ℕ)
    (c : Leg) (word : PositiveWord (CW112Block c) n) :
    Decidable
      ((SegmentedSplitRestriction.ofLeg (A := CW112Block) Leg.Z
        (cw112PushedOrbitProfile t₀ j)).Keeps n (fun _ ↦ t₀) c word) :=
  Classical.dec _

end AlgebraicComplexity.Examples
