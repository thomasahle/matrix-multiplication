/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112TypedRestrictionTransport
import AlgebraicComplexity.Tensor.PartitionedSelectPositivePower

set_option autoImplicit false

/-!
# The `(1,1,2)` orbit region restricts onto the typed cut of the `112` partition

Layer 4 (`AlgebraicComplexity/Examples/`).  The `[duan2023faster]` section 6.3 fine leaf's
`(1,1,2)` orbit region --- an `alphatilde`-typed cut of a power of the **raw** CW square --- is
carried exactly onto the corresponding typed cut of a power of `cw112PartitionedTensor`, the
object the committed `T_{1,1,2}` value chain is attached to.  The word-type transport this rests
on is `Examples/CoppersmithWinograd112TypedRestrictionTransport.lean`; the letter dictionary, its
blockwise maps and their propagation through positive powers come from
`Examples/CoppersmithWinograd112TypedRestriction.lean`, `Tensor/PartitionedBlockMapPower.lean` and
`Examples/CoppersmithWinograd112TypedRestrictionPower.lean`.

## The paper step

`[duan2023faster]`, proof of `lem:non-rot-values` (d),
`papers/sources/2210.10173/second_power_appendix.tex:26-45`, especially line `:37`: `\T` is the
zeroing-out of `T_{1,1,2}^{⊗m}` by the marginals of `α^{(1,1,2)}`, a subtensor of
`T_{1,1,2}^{⊗m}[α̃_Z^{(1,1,2)}]`.  The `Z`-marginal split is `eq:tilde_A`
(`second_power.tex:142-158`, statement `:145-156`), at level two the `b`-split of
`global_value.tex:341-348`; the value it optimises is `[coppersmith1990matrix]`, pp. 270--272.

## The direction of the restriction, and why it is the useful one

`Restricts A B` means `B` sits inside `A`, and `HasTauWeight.of_restricts` carries a weight from
`B` **up** to `A`.  The theorem below therefore has the *region* as the source and the *typed cut*
as the target, so a `tau`-weight proved for the `112` side descends to the leaf's orbit region ---
which is precisely what `dwz63_symSix_orbitRegionEntry_of_symThree` consumes.  (Cutting in the
other direction would be useless: a weight for the uncut power never reaches a cut of it.)

Primary sources: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via
Asymmetric Hashing*, `[duan2023faster]`, `second_power_appendix.tex:26-45` (line `:37`),
`second_power.tex:142-158`, `global_value.tex:341-348`; Don Coppersmith and Shmuel Winograd,
*Matrix Multiplication via Arithmetic Progressions*, `[coppersmith1990matrix]`, pp. 270--272.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The letter-level dictionary data, packaged for the power -/

section CellData

variable (K : Type u) [CommRing K] (q : ℕ)

/-- The dictionary is injective on the support of the raw cell. -/
theorem cw112RawCell_dict_injOn :
    ∀ s ∈ (cw112RawCell K q).support, ∀ t ∈ (cw112RawCell K q).support,
      (fun c ↦ cw112RawDict c (s c)) = (fun c ↦ cw112RawDict c (t c)) → s = t := by
  have hsupport : (cw112RawCell K q).support = cw112RawCellSupport := cw112RawCell_support K q
  rw [hsupport]
  exact cw112RawDict_injOn

/-- The `112` support is exactly the dictionary image of the raw cell's support. -/
theorem cw112RawCell_dict_support_image :
    (cw112PartitionedTensor K q).support =
      (cw112RawCell K q).support.image (fun s ↦ (fun c ↦ cw112RawDict c (s c))) := by
  have hsupport : (cw112RawCell K q).support = cw112RawCellSupport := cw112RawCell_support K q
  rw [hsupport, cw112PartitionedTensor_support]
  exact cw112BlockSupport_eq_image

/-- The same statement one exponent up: the support of a power of the `112` partition is the
letterwise dictionary image of the support of the corresponding power of the raw cell. -/
theorem cw112RawCell_positivePower_support_image (n : ℕ) :
    ((cw112PartitionedTensor K q).positivePower n).support =
      ((cw112RawCell K q).positivePower n).support.image
        (fun s ↦ (fun c ↦ positiveWordMap (cw112RawDict c) n (s c))) :=
  Tensor.positivePower_support_image (cw112RawCell K q) (cw112PartitionedTensor K q)
    cw112RawDict (cw112RawCell_dict_support_image K q) (cw112RawCell_dict_injOn K q) n

end CellData

/-! ## The two cut supports -/

section Cut

variable (K : Type u) [CommRing K] (q : ℕ)

/-- **The orbit region's support**: the letters lie in the `(1,1,2)` cell — which is what the
constant coarse target says — and the `Z` word carries the scaled `alphatilde` row exactly. -/
theorem dwz63_mem_orbitRegion_support_iff {M : ℕ} (t₀ : Fin M) (n j : ℕ)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)) :
    s ∈ (dwz63OrbitRegion K q 0 t₀ n j).support ↔
      s ∈ ((cw112RawCell K q).positivePower n).support ∧
        WordType.multiplicity (positiveWordEquiv (PositiveWord CWBlock 1) n (s Leg.Z)) =
          WordType.proportionalCounts (dwz63AlphaTilde 6) j := by
  have hdef : dwz63OrbitRegion K q 0 t₀ n j =
      ((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n M (fun _ ↦ t₀)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
          (fun t ↦ if t = t₀ then
            WordType.proportionalCounts (dwz63AlphaTilde 6) j else 0))
        (dwz63OrbitTarget 0 n) := rfl
  rw [hdef, PartitionedTensor.mem_segmentedLocalizedSplittingPower_support,
    dwz63_mem_orbitCellPower_support_iff]
  constructor
  · rintro ⟨hpow, hleg⟩
    refine ⟨⟨hpow,
      fun c i ↦ (dwz63_orbitTarget_iff_cellKeep n c (s c)).mp (hleg c).1 i⟩, ?_⟩
    exact (dwz63_keeps_constSeg_iff (A := fun _ : Leg ↦ PositiveWord CWBlock 1)
      t₀ _ n (s Leg.Z)).mp (hleg Leg.Z).2
  · rintro ⟨⟨hpow, hcell⟩, htype⟩
    refine ⟨hpow, fun c ↦ ⟨(dwz63_orbitTarget_iff_cellKeep n c (s c)).mpr (hcell c), ?_⟩⟩
    cases c
    · exact dwz63_keeps_constSeg_of_ne (by decide) _ _ _
    · exact dwz63_keeps_constSeg_of_ne (by decide) _ _ _
    · exact (dwz63_keeps_constSeg_iff (A := fun _ : Leg ↦ PositiveWord CWBlock 1)
        t₀ _ n (s Leg.Z)).mpr htype

/-- **The typed cut's support**: a supported word of `112` blocks whose `Z` word carries the
pushed-forward profile exactly. -/
theorem cw112_mem_typedCut_support_iff {M : ℕ} (t₀ : Fin M) (n j : ℕ)
    (t : BlockAddress (fun c ↦ PositiveWord (CW112Block c) n)) :
    t ∈ (cw112TypedCut K q t₀ n j).support ↔
      t ∈ ((cw112PartitionedTensor K q).positivePower n).support ∧
        WordType.multiplicity (positiveWordEquiv (CW112Block Leg.Z) n (t Leg.Z)) =
          WordType.mappedType (cw112RawDict Leg.Z)
            (WordType.proportionalCounts (dwz63AlphaTilde 6) j) := by
  have hdef : cw112TypedCut K q t₀ n j =
      ((cw112PartitionedTensor K q).positivePower n).select
        ((SegmentedSplitRestriction.ofLeg (A := CW112Block) Leg.Z
          (fun t ↦ if t = t₀ then
            WordType.mappedType (cw112RawDict Leg.Z)
              (WordType.proportionalCounts (dwz63AlphaTilde 6) j) else 0)).Keeps n
          (fun _ ↦ t₀)) := rfl
  rw [hdef, PartitionedTensor.mem_select_support]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro h
    exact (dwz63_keeps_constSeg_iff (A := CW112Block) t₀ _ n (t Leg.Z)).mp (h Leg.Z)
  · intro h c
    cases c
    · exact dwz63_keeps_constSeg_of_ne (by decide) _ _ _
    · exact dwz63_keeps_constSeg_of_ne (by decide) _ _ _
    · exact (dwz63_keeps_constSeg_iff (A := CW112Block) t₀ _ n (t Leg.Z)).mpr h

/-- **The two cuts correspond bijectively.**  This is the support hypothesis of
`Tensor.Restricts.partitionedBlockMap` at the word alphabets, and the place where the type
transport is used in both directions.

Proof sketch: both directions start from `cw112RawCell_positivePower_support_image`, which says
the `112` power's support is the letterwise dictionary image of the cell power's.  *Backward*
(a member of the typed cut is a dictionary image): the preimage `s` lies in the cell power, so all
its letters are cell letters; its `Z` type and the `alphatilde` row both vanish off the cell, and
`cw112RawDict_mappedType_injOn` --- the pushforward is injective on cell-supported profiles ---
turns the typed cut's pushed-forward condition back into the region's own condition.  *Forward*
(a dictionary image lies in the typed cut): membership in the `112` power is the image of
membership in the cell power, and the `Z` condition transports by the hypothesis-free
`cw112_multiplicity_positiveWordMap_Z`.  Injectivity of the pushforward is what makes the support
statement an equality rather than an inclusion. -/
theorem cw112TypedCut_support_eq_image {M : ℕ} (t₀ : Fin M) (n j : ℕ) :
    (cw112TypedCut K q t₀ n j).support =
      (dwz63OrbitRegion K q 0 t₀ n j).support.image
        (fun s ↦ (fun c ↦ positiveWordMap (cw112RawDict c) n (s c))) := by
  classical
  ext t
  rw [cw112_mem_typedCut_support_iff, Finset.mem_image]
  constructor
  · rintro ⟨hpow, htype⟩
    rw [cw112RawCell_positivePower_support_image, Finset.mem_image] at hpow
    obtain ⟨s, hs, rfl⟩ := hpow
    have hcell := (dwz63_mem_orbitCellPower_support_iff K q n s).mp hs
    refine ⟨s, (dwz63_mem_orbitRegion_support_iff K q t₀ n j s).mpr ⟨hs, ?_⟩, rfl⟩
    refine cw112RawDict_mappedType_injOn _ _
      (cw112_multiplicity_eq_zero_of_not_cell (s Leg.Z) (hcell.2 Leg.Z))
      (dwz63_proportionalCountsSix_eq_zero_of_not_cell j) ?_
    rw [← cw112_multiplicity_positiveWordMap_Z]
    exact htype
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hs, htype⟩ := (dwz63_mem_orbitRegion_support_iff K q t₀ n j s).mp hs
    refine ⟨?_, ?_⟩
    · rw [cw112RawCell_positivePower_support_image]
      exact Finset.mem_image_of_mem _ hs
    · rw [cw112_multiplicity_positiveWordMap_Z, htype]

/-! ## The restriction -/

/-- **The `(1,1,2)` orbit region of the fine leaf restricts onto the `alphatilde`-typed cut of the
`112` partition's `n`-th power.**

The region is the *source* and the typed cut the *target*, so a `tau`-weight for the `112` side
descends to the region — the direction `dwz63_symSix_orbitRegionEntry_of_symThree` needs.

Proof sketch: `Tensor.Restricts.partitionedBlockMap` at the word alphabets, with the dictionary
applied letterwise and the block maps the iterated tensor products of
`Tensor.positiveWordBlockMap`.  Injectivity on the support is the letter-level injectivity lifted
by `Tensor.positiveWordMap_injOn_support`; the support equality is
`cw112TypedCut_support_eq_image`; the constituent identity is the letter-level one lifted by
`Tensor.map_positiveWordBlockMap_constituent`, transported from the cell power to the region by
`PartitionedTensor.positivePower_select_constituent` (a cut keeps its parent's constituents). -/
theorem dwz63_orbitRegion_restricts_typedCut {M : ℕ} (t₀ : Fin M) (n j : ℕ) :
    Restricts (dwz63OrbitRegion K q 0 t₀ n j).realize (cw112TypedCut K q t₀ n j).realize := by
  refine Tensor.Restricts.partitionedBlockMap
    (dwz63OrbitRegion K q 0 t₀ n j) (cw112TypedCut K q t₀ n j)
    (fun c ↦ positiveWordMap (cw112RawDict c) n)
    (Tensor.positiveWordBlockMap cw112RawDict (cw112RawBlockMap K q) n) ?_ ?_ ?_
  · intro s hs t ht hst
    exact Tensor.positiveWordMap_injOn_support (cw112RawCell K q) cw112RawDict
      (cw112RawCell_dict_injOn K q) n s
      ((dwz63_mem_orbitRegion_support_iff K q t₀ n j s).mp hs).1 t
      ((dwz63_mem_orbitRegion_support_iff K q t₀ n j t).mp ht).1 hst
  · exact cw112TypedCut_support_eq_image K q t₀ n j
  · intro s hs t ht
    subst ht
    rw [Tensor.map_partitionedBlockMap_block]
    have hs' : s ∈ ((cw112RawCell K q).positivePower n).support :=
      ((dwz63_mem_orbitRegion_support_iff K q t₀ n j s).mp hs).1
    have hconstituent : ∀ u ∈ (cw112RawCell K q).support,
        map (fun c ↦ cw112RawBlockMap K q c (u c)) ((cw112RawCell K q).constituent u) =
          (cw112PartitionedTensor K q).constituent (fun c ↦ cw112RawDict c (u c)) := by
      intro u hu
      have hu' : u ∈ cw112RawCellSupport := by
        have hsupport : (cw112RawCell K q).support = cw112RawCellSupport :=
          cw112RawCell_support K q
        rwa [hsupport] at hu
      exact Tensor.map_partitionedBlockMap_constituent (cw112RawCell K q)
        (cw112PartitionedTensor K q) cw112RawDict (cw112RawBlockMap K q) u
        (map_cw112RawBlockMap_constituent K q u hu' _ rfl)
    have hsel : ((cw112RawCell K q).positivePower n).constituent s =
        (dwz63OrbitRegion K q 0 t₀ n j).constituent s :=
      congrFun (Tensor.PartitionedTensor.positivePower_select_constituent
        ((cwPartitionedTensor K q).positivePower 1) cw112RawCellKeep n) s
    rw [← hsel]
    exact congrArg
      (map (blockInclude (K := K)
        (V := PositivePowerBlockSpace K (CW112PartitionBlockSpace K q) n)
        (fun c ↦ positiveWordMap (cw112RawDict c) n (s c))))
      (Tensor.map_positiveWordBlockMap_constituent (cw112RawCell K q)
        (cw112PartitionedTensor K q) cw112RawDict (cw112RawBlockMap K q) hconstituent n s hs')

end Cut

end AlgebraicComplexity.Examples
