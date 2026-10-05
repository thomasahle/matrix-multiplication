/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoRegionalCells

set_option autoImplicit false

/-!
# The section 6.3 leaf's `sym₆`-weight, assembled from its fifteen regions

Layer 4 (`AlgebraicComplexity/Examples/`).  Stage (D), closed on the value side: image 109's fifteen
region entries are fed to `segmentedRegionalSymSixWeights_of_letterwise` and
`hasTauWeight_symSix_segmentedLocalizedSplittingPower_regional`, and the result is a single
`HasTauWeight` fact about `sym₆` of the reference leaf --- the shape `hleafWeight` consumes --- at
the value `exp ((n + 1) * (dwz63LogVal - ε)) ^ 6`.

## Two strengthenings, and why they are here rather than in the accepted files

`dwz63_referenceLeaf_isomorphic_consecutive` (image 96) returns its sorting permutation
existentially **without** recording `dwz63Seg ∘ σ = SegmentRegionBlock.seg b rest`, and
`dwz63_exists_consecutiveBlocks` (image 96) hides the block order, so
`SegmentRegionSpec.totalValue` cannot be read off.  Both facts are needed here: the letterwise
invariant of the assembly holds only for the sorting permutation, and the leaf's value is the
ordered product of the fifteen regional values.  The primed forms below are the same proofs with
the extra conjunct; the accepted files are not re-issued.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K]

/-! ## The ordered product of the fifteen regional values -/

/-- The fifteen regional weights in the order the block list lays them out, right-nested exactly
as `SegmentRegionSpec.totalValue` builds them. -/
noncomputable def dwz63NestedValue (value : Fin 15 → ℝ) : ℝ :=
  value 0 * (value 1 * (value 2 * (value 3 * (value 4 * (value 5 * (value 6 *
    (value 7 * (value 8 * (value 9 * (value 10 * (value 11 * (value 12 *
      (value 13 * value 14)))))))))))))

/-- The block list's `totalValue` is that ordered product. -/
theorem dwz63_totalValue_consecutiveBlocks (n : ℕ)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ) (value : Fin 15 → ℝ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) :
    SegmentRegionSpec.totalValue
        (dwz63ConsecutiveBlock K n alphaTilde value wRef 0).toSegmentRegionSpec
        (SegmentRegionBlock.specs (dwz63ConsecutiveBlocks K n alphaTilde value wRef))
      = dwz63NestedValue value := rfl

/-- The ordered product is the `Finset` product. -/
theorem dwz63_nestedValue_eq_prod (value : Fin 15 → ℝ) :
    dwz63NestedValue value = ∏ t : Fin 15, value t := by
  simp [dwz63NestedValue, Fin.prod_univ_succ]

/-- At the regional values the ordered product is one exponential: the fifteen exponents add. -/
theorem dwz63_nestedValue_regionValue (s : ℕ) (ε : ℝ) :
    dwz63NestedValue (fun t ↦ dwz63RegionValue t s ε)
      = Real.exp (∑ t : Fin 15, dwz63RegionExponent t s ε) ^ 6 := by
  rw [dwz63_nestedValue_eq_prod]
  simp only [dwz63RegionValue_eq_exp]
  rw [Finset.prod_pow, ← Real.exp_sum]

/-! ## The two strengthened packagings -/

/-- **Image 96's block existential, carrying the ordered product as well.** -/
theorem dwz63_exists_consecutiveBlocks' (n : ℕ)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ) (value : Fin 15 → ℝ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hpos : ∀ t, 0 < WordType.multiplicity (dwz63Seg K n wRef) t) :
    ∃ (b : SegmentRegionBlock (fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z 15)
      (rest : List (SegmentRegionBlock (fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z 15)),
      SegmentRegionBlock.total b rest = n ∧
      SegmentRegionBlock.multiplicityProfile b rest =
        WordType.multiplicity (dwz63Seg K n wRef) ∧
      SegmentRegionSpec.parentType b.toSegmentRegionSpec (SegmentRegionBlock.specs rest) =
        alphaTilde ∧
      SegmentRegionSpec.totalValue b.toSegmentRegionSpec (SegmentRegionBlock.specs rest) =
        dwz63NestedValue value ∧
      ∀ u ∈ b :: rest,
        u.type = (fun t' ↦ if t' = u.label then alphaTilde u.label else 0) ∧
        u.value = value u.label ∧
        u.size + 1 = WordType.multiplicity (dwz63Seg K n wRef) u.label := by
  refine ⟨dwz63ConsecutiveBlock K n alphaTilde value wRef 0,
    dwz63ConsecutiveBlocks K n alphaTilde value wRef, ?_,
    dwz63_multiplicityProfile_consecutiveBlocks K n alphaTilde value wRef hpos,
    dwz63_parentType_consecutiveBlocks K n alphaTilde value wRef,
    dwz63_totalValue_consecutiveBlocks K n alphaTilde value wRef, ?_⟩
  · exact SegmentRegionBlock.total_eq_of_multiplicityProfile _ _ (dwz63Seg K n wRef)
      (dwz63_multiplicityProfile_consecutiveBlocks K n alphaTilde value wRef hpos)
  · intro u hu
    obtain ⟨t, rfl⟩ := dwz63_mem_consecutiveBlocks K n alphaTilde value wRef u hu
    exact ⟨rfl, rfl, Nat.succ_pred_eq_of_pos (hpos t)⟩

/-- **Image 96's sorting isomorphism, carrying the segmentation equation as well.**

The extra conjunct is what makes the letterwise invariant of the assembly available: it holds only
for the permutation that actually sorts the segmentation, not for an arbitrary one. -/
theorem dwz63_referenceLeaf_isomorphic_consecutive'
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (b : SegmentRegionBlock (fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z 15)
    (rest : List (SegmentRegionBlock (fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z 15))
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support)
      (SegmentRegionBlock.total b rest))
    (hmult : WordType.multiplicity (dwz63Seg K (SegmentRegionBlock.total b rest) wRef) =
      SegmentRegionBlock.multiplicityProfile b rest) :
    ∃ σ : Equiv.Perm (Fin (SegmentRegionBlock.total b rest + 1)),
      dwz63Seg K (SegmentRegionBlock.total b rest) wRef ∘ ⇑σ =
        SegmentRegionBlock.seg b rest ∧
      Isomorphic
        (((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap (SegmentRegionBlock.total b rest) 15
          (dwz63Seg K (SegmentRegionBlock.total b rest) wRef)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde)
          (positiveSupportWordBlockAddress
            ((cwSquarePartitionedTensor K dwz63Q).support)
            (SegmentRegionBlock.total b rest) wRef)).realize
        (((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap (SegmentRegionBlock.total b rest) 15
          (SegmentRegionBlock.seg b rest)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde)
          (positionRelabelBlockAddress (fun _ : Leg ↦ Fin 5)
            (SegmentRegionBlock.total b rest) σ
            (positiveSupportWordBlockAddress
              ((cwSquarePartitionedTensor K dwz63Q).support)
              (SegmentRegionBlock.total b rest) wRef))).realize := by
  obtain ⟨σ, hσ⟩ := SegmentRegionBlock.exists_perm_comp_eq_seg b rest
    (dwz63Seg K (SegmentRegionBlock.total b rest) wRef) hmult
  refine ⟨σ, hσ, ?_⟩
  have h := Tensor.Isomorphic.segmentedLocalizedSplittingPower_position
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap
    (SegmentRegionBlock.total b rest) 15
    (dwz63Seg K (SegmentRegionBlock.total b rest) wRef)
    (SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde)
    (positiveSupportWordBlockAddress
      ((cwSquarePartitionedTensor K dwz63Q).support)
      (SegmentRegionBlock.total b rest) wRef) σ
  rw [hσ] at h
  exact h


/-! ## The leaf's `sym₆`-weight -/

/-- **Stage (D), closed on the value side.**

The fifteen region entries of image 109, sorted onto consecutive blocks and multiplied, give a
`sym₆`-weight of the section 6.3 reference leaf at `exp ((n + 1) * (dwz63LogVal - ε)) ^ 6`
--- the
shape `hleafWeight` consumes.  The three orbit rows enter as the hypothesis `hcut`, in image 104's
`sym₃` form at the exact period the assembly needs.

`dwz63_regionProduct_lt_required` (image 109) records that this value is strictly below what
`omega_lt_2374631_of_plainBatchedStageAndLeaf`'s `hleafValue` binder demands, for every positive
`ε`; a margin variant of that endpoint is what closes the remaining gap. -/
theorem dwz63_hasTauWeight_symSix_referenceLeaf (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
      (∀ (o : Fin 3) (m : ℕ), m + 1 = 200000000 * (dwz63Alpha (dwz63OrbitRow o) * s) →
        HasTauWeight K (symThree K (dwz63OrbitRegion K dwz63Q o (dwz63OrbitRow o) m
          (dwz63Alpha (dwz63OrbitRow o) * s)).realize) dwz63Tau
          (Real.exp ((200000000 : ℝ) * ((dwz63Alpha (dwz63OrbitRow o) * s : ℕ) : ℝ)
            * (dwz63OrbitLogVal o - ε)) ^ 3)) →
      ∀ (n : ℕ) (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n),
        (∀ t : Fin 15, WordType.multiplicity (dwz63Seg K n wRef) t
          = 200000000 * (dwz63Alpha t * s)) →
        HasTauWeight K
          (symSix K
            ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
            cwSquareDegreeMap n 15 (dwz63Seg K n wRef)
            (SegmentedSplitRestriction.ofLeg
              (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
              (fun t ↦ WordType.proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s)))
            (positiveSupportWordBlockAddress
              ((cwSquarePartitionedTensor K dwz63Q).support) n wRef)).realize)) dwz63Tau
          (Real.exp (((n : ℝ) + 1) * (dwz63LogVal - ε)) ^ 6) := by
  obtain ⟨N, hN⟩ := dwz63_exists_symSix_regionEntry_cells K ε hε
  refine ⟨max N 1, fun s hs hcut n wRef hmu ↦ ?_⟩
  have hsN : N ≤ s := le_trans (le_max_left _ _) hs
  have hs1 : 0 < s := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hs)
  have hpos : ∀ t : Fin 15, 0 < WordType.multiplicity (dwz63Seg K n wRef) t := by
    intro t
    rw [hmu t]
    exact Nat.mul_pos (by norm_num) (Nat.mul_pos (dwz63Alpha_pos t) hs1)
  obtain ⟨b, rest, htotal, hmultProfile, hparent, hvalue, hblocks⟩ :=
    dwz63_exists_consecutiveBlocks' K n
      (fun t ↦ WordType.proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s))
      (fun t ↦ dwz63RegionValue t s ε) wRef hpos
  subst htotal
  obtain ⟨σ, hσ, hiso⟩ := dwz63_referenceLeaf_isomorphic_consecutive' K
    (fun t ↦ WordType.proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s)) b rest wRef
    hmultProfile.symm
  refine HasTauWeight.of_restricts (Tensor.Restricts.symSix_congr hiso.restricts) ?_
  have hb0 : (0 : ℝ) ≤ b.toSegmentRegionSpec.value := by
    obtain ⟨-, hval, -⟩ := hblocks b (List.mem_cons_self ..)
    show (0 : ℝ) ≤ b.value
    rw [hval]
    unfold dwz63RegionValue
    positivity
  have hrestnn : ∀ u ∈ SegmentRegionBlock.specs rest, (0 : ℝ) ≤ u.value := by
    intro u hu
    obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hu
    obtain ⟨-, hval, -⟩ := hblocks u' (List.mem_cons_of_mem b hu')
    show (0 : ℝ) ≤ u'.value
    rw [hval]
    unfold dwz63RegionValue
    positivity
  have hweights : ∀ u ∈ b :: rest, HasTauWeight K
      (symSix K ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap u.size 15 (fun _ ↦ u.label)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z u.type)
        (fun c ↦ positiveWordConst (dwz63Cell u.label c) u.size)).realize)) dwz63Tau u.value := by
    intro u hu
    obtain ⟨htype, hval, hsize⟩ := hblocks u hu
    rw [htype, hval]
    exact hN s hsN hcut u.label u.size (by rw [hsize, hmu])
  have hbundle := segmentedRegionalSymSixWeights_of_letterwise
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap Leg.Z dwz63Tau
    dwz63Cell b rest
    (positionRelabelBlockAddress (fun _ : Leg ↦ Fin 5)
      (SegmentRegionBlock.total b rest) σ
      (positiveSupportWordBlockAddress
        ((cwSquarePartitionedTensor K dwz63Q).support) (SegmentRegionBlock.total b rest) wRef))
    (fun c i ↦ dwz63_relabelledAddress_eq_dwz63Cell K (SegmentRegionBlock.total b rest) wRef σ
      (SegmentRegionBlock.seg b rest i) i (congrFun hσ i) c)
    hweights
  have hreg := hasTauWeight_symSix_segmentedLocalizedSplittingPower_regional
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap Leg.Z
    b.toSegmentRegionSpec (SegmentRegionBlock.specs rest) (SegmentRegionBlock.seg b rest)
    (positionRelabelBlockAddress (fun _ : Leg ↦ Fin 5)
      (SegmentRegionBlock.total b rest) σ
      (positiveSupportWordBlockAddress
        ((cwSquarePartitionedTensor K dwz63Q).support) (SegmentRegionBlock.total b rest) wRef))
    hb0 hrestnn hbundle
  rw [hparent, hvalue, dwz63_nestedValue_regionValue] at hreg
  have hn : SegmentRegionBlock.total b rest + 1 = 20000000000000000 * s := by
    have hsum := WordType.sum_multiplicity
      (dwz63Seg K (SegmentRegionBlock.total b rest) wRef)
    rw [← hsum]
    simp only [hmu, dwz63Alpha, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one]
    ring
  rw [dwz63_leafValue_eq (SegmentRegionBlock.total b rest) s ε hn] at hreg
  exact hreg

end AlgebraicComplexity.Examples
