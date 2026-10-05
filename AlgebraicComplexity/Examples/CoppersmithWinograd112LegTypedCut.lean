/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112LegTypedTransport
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitRotatedRegion

set_option autoImplicit false

/-!
# The rotated orbit region restricts onto a typed cut of the `112` partition

Layer 4 (`AlgebraicComplexity/Examples/`).
`Examples/CoppersmithWinograd112TypedRestrictionCut.lean` carries the `(1,1,2)` orbit region of
`[duan2023faster]`'s fine leaf onto the `Z`-typed cut of a power of `cw112PartitionedTensor`.
`Examples/DuanWuZhouLevelTwoOrbitRotatedRegion.lean` turns the `(1,2,1)` and `(2,1,1)` rows into
the *same* `(1,1,2)` region with the `alphatilde` condition moved to the `X` resp. `Y` leg.  This
module carries that rotated region onto the corresponding typed cut, with the constrained leg as a
parameter.

## The paper step

`[duan2023faster]`, proof of `lem:non-rot-values` (d),
`papers/sources/2210.10173/second_power_appendix.tex:26-45`, especially line `:37`: `\T` is the
zeroing-out of `T_{1,1,2}^{⊗m}` by the marginals of `α^{(1,1,2)}`, a subtensor of
`T_{1,1,2}^{⊗m}[α̃^{(1,1,2)}]`.  For the two rotated rows the split is the symmetric
degree-one one of `global_value.tex:347`, the committed `dwz63AlphaTilde 7 = dwz63AlphaTilde 10`;
the value being optimised is `[coppersmith1990matrix]`, pp. 270--272.

## The direction of the restriction

`Restricts A B` means `B` sits inside `A`, and `HasTauWeight.of_restricts` carries a weight from
`B` **up** to `A`.  The region is therefore the source and the typed cut the target, so a
`tau`-weight proved for the `112` side descends to the leaf's rotated orbit region.

Primary sources: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via
Asymmetric Hashing*, `[duan2023faster]`, `second_power_appendix.tex:26-45` (line `:37`),
`second_power.tex:142-158`, `:235`, `global_value.tex:341-348` (`:347`); Don Coppersmith and
Shmuel Winograd, *Matrix Multiplication via Arithmetic Progressions*, `[coppersmith1990matrix]`,
pp. 270--272.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The symmetric degree-one row is supported inside the cell of a degree-one leg -/

/-- The two degree-one legs of the `(1,1,2)` coarse address. -/
theorem cwSquare112_side : cwSquare112 Leg.X = 1 ∧ cwSquare112 Leg.Y = 1 := ⟨rfl, rfl⟩

/-- **The symmetric degree-one split row vanishes off the cell of a degree-one leg.** -/
theorem dwz63_alphaTildeSeven_eq_zero_of_not_cell (c₀ : Leg) (hc₀ : cwSquare112 c₀ = 1)
    (a : PositiveWord CWBlock 1) (ha : ¬ cw112RawCellKeep c₀ a) :
    dwz63AlphaTilde 7 a = 0 := by
  by_contra h
  refine ha ?_
  show cwSquareDegreeMap c₀ a = cwSquare112 c₀
  rw [hc₀]
  exact dwz63_alphaTildeDegree_seven a h

/-- The scaled row vanishes off the cell as well. -/
theorem dwz63_proportionalCountsSeven_eq_zero_of_not_cell (c₀ : Leg)
    (hc₀ : cwSquare112 c₀ = 1) (j : ℕ) (a : PositiveWord CWBlock 1)
    (ha : ¬ cw112RawCellKeep c₀ a) :
    WordType.proportionalCounts (dwz63AlphaTilde 7) j a = 0 := by
  show dwz63AlphaTilde 7 a * j = 0
  rw [dwz63_alphaTildeSeven_eq_zero_of_not_cell c₀ hc₀ a ha, Nat.zero_mul]

/-! ## The typed cut on the `112` side, on an arbitrary leg -/

variable (K : Type u) [CommRing K] (q : ℕ)

/-- The per-segment profile of the rotated orbit region, pushed forward along the dictionary. -/
noncomputable def cw112LegPushedProfile (c₀ : Leg) {M : ℕ} (t₀ : Fin M) (j : ℕ) :
    Fin M → CW112Block c₀ → ℕ :=
  fun t ↦ if t = t₀ then
    WordType.mappedType (cw112RawDict c₀)
      (WordType.proportionalCounts (dwz63AlphaTilde 7) j) else 0

/-- **The `alphatilde`-typed cut of the `112` partition's `n`-th power, on the leg `c₀`.** -/
noncomputable def cw112LegTypedCut (c₀ : Leg) {M : ℕ} (t₀ : Fin M) (n j : ℕ) :=
  ((cw112PartitionedTensor K q).positivePower n).select
    ((SegmentedSplitRestriction.ofLeg (A := CW112Block) c₀
      (cw112LegPushedProfile c₀ t₀ j)).Keeps n (fun _ ↦ t₀))

noncomputable instance cw112LegTypedCutKeepDecidable (c₀ : Leg) {M : ℕ} (t₀ : Fin M)
    (n j : ℕ) (c : Leg) (word : PositiveWord (CW112Block c) n) :
    Decidable
      ((SegmentedSplitRestriction.ofLeg (A := CW112Block) c₀
        (cw112LegPushedProfile c₀ t₀ j)).Keeps n (fun _ ↦ t₀) c word) :=
  Classical.dec _

/-! ## The two cut supports -/

/-- **The rotated orbit region's support**: the letters lie in the `(1,1,2)` cell, and the word on
the constrained leg carries the scaled `alphatilde` row exactly. -/
theorem dwz63_mem_sideOrbitRegion_support_iff (c₀ : Leg) {M : ℕ} (t₀ : Fin M) (n j : ℕ)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)) :
    s ∈ (dwz63SideOrbitRegion K q c₀ t₀ n j).support ↔
      s ∈ ((cw112RawCell K q).positivePower n).support ∧
        WordType.multiplicity (positiveWordEquiv (PositiveWord CWBlock 1) n (s c₀)) =
          WordType.proportionalCounts (dwz63AlphaTilde 7) j := by
  have hdef : dwz63SideOrbitRegion K q c₀ t₀ n j =
      ((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n M (fun _ ↦ t₀)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) c₀
          (fun t ↦ if t = t₀ then
            WordType.proportionalCounts (dwz63AlphaTilde 7) j else 0))
        (dwz63OrbitTarget 0 n) := rfl
  rw [hdef, PartitionedTensor.mem_segmentedLocalizedSplittingPower_support,
    dwz63_mem_orbitCellPower_support_iff]
  constructor
  · rintro ⟨hpow, hleg⟩
    refine ⟨⟨hpow,
      fun c i ↦ (dwz63_orbitTarget_iff_cellKeep n c (s c)).mp (hleg c).1 i⟩, ?_⟩
    exact (dwz63_keepsAt_constSeg_iff (A := fun _ : Leg ↦ PositiveWord CWBlock 1)
      c₀ t₀ _ n (s c₀)).mp (hleg c₀).2
  · rintro ⟨⟨hpow, hcell⟩, htype⟩
    refine ⟨hpow, fun c ↦ ⟨(dwz63_orbitTarget_iff_cellKeep n c (s c)).mpr (hcell c), ?_⟩⟩
    by_cases hc : c₀ = c
    · subst hc
      exact (dwz63_keepsAt_constSeg_iff (A := fun _ : Leg ↦ PositiveWord CWBlock 1)
        c₀ t₀ _ n (s c₀)).mpr htype
    · exact dwz63_keepsAt_constSeg_of_ne hc _ _ _

/-- **The typed cut's support**: a supported word of `112` blocks whose word on the constrained
leg carries the pushed-forward profile exactly. -/
theorem cw112_mem_legTypedCut_support_iff (c₀ : Leg) {M : ℕ} (t₀ : Fin M) (n j : ℕ)
    (t : BlockAddress (fun c ↦ PositiveWord (CW112Block c) n)) :
    t ∈ (cw112LegTypedCut K q c₀ t₀ n j).support ↔
      t ∈ ((cw112PartitionedTensor K q).positivePower n).support ∧
        WordType.multiplicity (positiveWordEquiv (CW112Block c₀) n (t c₀)) =
          WordType.mappedType (cw112RawDict c₀)
            (WordType.proportionalCounts (dwz63AlphaTilde 7) j) := by
  have hdef : cw112LegTypedCut K q c₀ t₀ n j =
      ((cw112PartitionedTensor K q).positivePower n).select
        ((SegmentedSplitRestriction.ofLeg (A := CW112Block) c₀
          (fun t ↦ if t = t₀ then
            WordType.mappedType (cw112RawDict c₀)
              (WordType.proportionalCounts (dwz63AlphaTilde 7) j) else 0)).Keeps n
          (fun _ ↦ t₀)) := rfl
  rw [hdef, PartitionedTensor.mem_select_support]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro h
    exact (dwz63_keepsAt_constSeg_iff (A := CW112Block) c₀ t₀ _ n (t c₀)).mp (h c₀)
  · intro h c
    by_cases hc : c₀ = c
    · subst hc
      exact (dwz63_keepsAt_constSeg_iff (A := CW112Block) c₀ t₀ _ n (t c₀)).mpr h
    · exact dwz63_keepsAt_constSeg_of_ne hc _ _ _

/-- **The two cuts correspond bijectively.**

Proof sketch: both directions start from `cw112RawCell_positivePower_support_image`, which says
the `112` power's support is the letterwise dictionary image of the cell power's.  *Backward*
(a member of the typed cut is a dictionary image): the preimage `s` lies in the cell power, so all
its letters are cell letters; its type on the constrained leg and the `alphatilde` row both vanish
off the cell, and `cw112RawDict_mappedTypeAt_injOn` turns the typed cut's pushed-forward condition
back into the region's own condition.  *Forward*: membership in the `112` power is the image of
membership in the cell power, and the condition on the constrained leg transports by the
hypothesis-free `cw112_multiplicity_positiveWordMapAt`. -/
theorem cw112LegTypedCut_support_eq_image (c₀ : Leg) (hc₀ : cwSquare112 c₀ = 1)
    {M : ℕ} (t₀ : Fin M) (n j : ℕ) :
    (cw112LegTypedCut K q c₀ t₀ n j).support =
      (dwz63SideOrbitRegion K q c₀ t₀ n j).support.image
        (fun s ↦ (fun c ↦ positiveWordMap (cw112RawDict c) n (s c))) := by
  classical
  ext t
  rw [cw112_mem_legTypedCut_support_iff, Finset.mem_image]
  constructor
  · rintro ⟨hpow, htype⟩
    rw [cw112RawCell_positivePower_support_image, Finset.mem_image] at hpow
    obtain ⟨s, hs, rfl⟩ := hpow
    have hcell := (dwz63_mem_orbitCellPower_support_iff K q n s).mp hs
    refine ⟨s,
      (dwz63_mem_sideOrbitRegion_support_iff K q c₀ t₀ n j s).mpr ⟨hs, ?_⟩, rfl⟩
    refine cw112RawDict_mappedTypeAt_injOn c₀ _ _
      (cw112_multiplicityAt_eq_zero_of_not_cell c₀ (s c₀) (hcell.2 c₀))
      (dwz63_proportionalCountsSeven_eq_zero_of_not_cell c₀ hc₀ j) ?_
    rw [← cw112_multiplicity_positiveWordMapAt c₀]
    exact htype
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hs, htype⟩ := (dwz63_mem_sideOrbitRegion_support_iff K q c₀ t₀ n j s).mp hs
    refine ⟨?_, ?_⟩
    · rw [cw112RawCell_positivePower_support_image]
      exact Finset.mem_image_of_mem _ hs
    · rw [cw112_multiplicity_positiveWordMapAt, htype]

/-! ## The restriction -/

/-- **The rotated orbit region restricts onto the `alphatilde`-typed cut of the `112` partition's
`n`-th power, on the constrained leg.**

Proof sketch: `Tensor.Restricts.partitionedBlockMap` at the word alphabets, with the dictionary
applied letterwise and the block maps the iterated tensor products of
`Tensor.positiveWordBlockMap`.  Injectivity on the support is the letter-level injectivity lifted
by `Tensor.positiveWordMap_injOn_support`; the support equality is
`cw112LegTypedCut_support_eq_image`; the constituent identity is the letter-level one lifted by
`Tensor.map_positiveWordBlockMap_constituent`, transported from the cell power to the region by
`PartitionedTensor.positivePower_select_constituent`. -/
theorem dwz63_sideOrbitRegion_restricts_legTypedCut (c₀ : Leg) (hc₀ : cwSquare112 c₀ = 1)
    {M : ℕ} (t₀ : Fin M) (n j : ℕ) :
    Restricts (dwz63SideOrbitRegion K q c₀ t₀ n j).realize
      (cw112LegTypedCut K q c₀ t₀ n j).realize := by
  refine Tensor.Restricts.partitionedBlockMap
    (dwz63SideOrbitRegion K q c₀ t₀ n j) (cw112LegTypedCut K q c₀ t₀ n j)
    (fun c ↦ positiveWordMap (cw112RawDict c) n)
    (Tensor.positiveWordBlockMap cw112RawDict (cw112RawBlockMap K q) n) ?_ ?_ ?_
  · intro s hs t ht hst
    exact Tensor.positiveWordMap_injOn_support (cw112RawCell K q) cw112RawDict
      (cw112RawCell_dict_injOn K q) n s
      ((dwz63_mem_sideOrbitRegion_support_iff K q c₀ t₀ n j s).mp hs).1 t
      ((dwz63_mem_sideOrbitRegion_support_iff K q c₀ t₀ n j t).mp ht).1 hst
  · exact cw112LegTypedCut_support_eq_image K q c₀ hc₀ t₀ n j
  · intro s hs t ht
    subst ht
    rw [Tensor.map_partitionedBlockMap_block]
    have hs' : s ∈ ((cw112RawCell K q).positivePower n).support :=
      ((dwz63_mem_sideOrbitRegion_support_iff K q c₀ t₀ n j s).mp hs).1
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
        (dwz63SideOrbitRegion K q c₀ t₀ n j).constituent s :=
      congrFun (Tensor.PartitionedTensor.positivePower_select_constituent
        ((cwPartitionedTensor K q).positivePower 1) cw112RawCellKeep n) s
    rw [← hsel]
    exact congrArg
      (map (blockInclude (K := K)
        (V := PositivePowerBlockSpace K (CW112PartitionBlockSpace K q) n)
        (fun c ↦ positiveWordMap (cw112RawDict c) n (s c))))
      (Tensor.map_positiveWordBlockMap_constituent (cw112RawCell K q)
        (cw112PartitionedTensor K q) cw112RawDict (cw112RawBlockMap K q) hconstituent n s hs')

end AlgebraicComplexity.Examples
