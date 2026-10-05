/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedRegionalOneSegmentBridge
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoConsecutiveSegments
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellRegional

set_option autoImplicit false

/-!
# The section 6.3 leaf's `sym₆`-weight from its fifteen cells

Layer 4 (`AlgebraicComplexity/Examples/`).  This is stage (D)'s composition step: the fifteen
per-cell weights compose into one `HasTauWeight` fact about `sym₆` of the reference leaf, which is
exactly the `hleafWeight` binder of `omega_lt_2374631_of_plainBatchedStageAndLeaf`
(`Examples/DuanWuZhouLevelTwoPlainBatchedEndpoint.lean`).  The composition is unconditional; the
fifteen weights it consumes are not, so the conclusion here is conditional on `hw`.

## What is a hypothesis and why

`dwz63_hasTauWeight_symSix_referenceLeaf_of_regional` takes the fifteen weights as the single
recursive bundle `SegmentedRegionalSymSixWeights`.  Three of the fifteen cells --- the orbit cells
`(1,1,2)`, `(1,2,1)`, `(2,1,1)` --- have **no** weight at all in the committed tree: the committed
`beta` chain weighs the *uncut* `112` tensor and does not descend through the regional restriction,
so those three entries remain conditional on the typed-cut `112`/`beta` obligation that image 104
(`Examples/DuanWuZhouLevelTwoFineCellOrbit.lean`) exposes as its `hcut` binder.  `(2,2,0)` is
proved exactly in `Examples/DuanWuZhouLevelTwoFineCellTwoTwoZero.lean`, and the fine-counting lane
restates the remaining rows at the joined period.  Carrying the bundle as a hypothesis means the
composition is finished now and admits each cell the moment it lands, with no statement here
changing shape.

The bundle is asked at *every* position permutation `σ`, because the permutation that sorts the
segmentation into consecutive blocks is produced inside the proof
(`dwz63_referenceLeaf_isomorphic_consecutive`) and the regional coarse targets are relative to it.
That is not a strengthening in practice: the per-cell weights hold at every coarse target of the
right shape, and `SegmentedRegionalSymSixWeights` chooses the regional targets existentially.

## What the cells supply

`dwz63_exists_symSix_regionEntry_logVal` is the join with the per-cell lane: image 95's generic
per-cell theorem `dwz63_exists_fineCellWeight_logVal` proves a weight for the **one-segment** leaf,
and a region of the fifteen-segment leaf **is** that leaf
(`segmentedLocalizedSplittingPower_constSeg_eq_oneSegment`, an equation), while `V^{(6)}` costs a
sixth power (`HasTauWeight.symSix_pow_six`).  So every cell proved through that route becomes a
region entry with no further work; the nine committed instances are nine instantiations of the
theorem below.

Primary source: `[duan2023faster]` --- Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.3 (the level-two global-value
example), `papers/sources/2210.10173/global_value.tex:332-348`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## A weighed cell is a region entry -/

/-- **A cell weighed by the fine route is a region's `sym₆` entry.**

The one-segment leaf of `dwz63_exists_fineCellWeight_logVal` is the region of the `M`-segment leaf
labelled `t₀` whose prescribed type is `proportionalCounts a j` on its own segment and the zero
type elsewhere --- an equation, so nothing is lost --- and `V^{(6)}` raises the value to the sixth.
Each of the nine committed cells is an instantiation of this. -/
theorem dwz63_exists_symSix_regionEntry_logVal (zero : Leg) (hzero : zero ≠ Leg.Z) (k : Fin 5)
    (hq : 0 < q)
    (a : PositiveWord CWBlock 1 → ℕ) (mass : ℕ)
    (hmasseq : WordType.profileMass a = mass) (hmass0 : 0 < mass)
    (ha : ∀ p : PositiveWord CWBlock 1, a p ≠ 0 → cwSquareBlockDegree p = k)
    (logVal : ℝ)
    (hrate : dwz63Tau * ((WordType.profileMass a : ℝ) * WordType.profileEntropyNats a
        + ((∑ p : PositiveWord CWBlock 1, a p * cwWordMiddleCount 1 p : ℕ) : ℝ) *
          Real.log q) = (WordType.profileMass a : ℝ) * logVal)
    (ε : ℝ) (hε : 0 < ε) {M : ℕ} (t₀ : Fin M) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = mass * j →
      HasTauWeight K
        (symSix K ((((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n M (fun _ ↦ t₀)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun t ↦ if t = t₀ then WordType.proportionalCounts a j else 0))
          (dwz63ZeroCellTarget zero k n)).realize)) dwz63Tau
        (Real.exp ((mass : ℝ) * (j : ℝ) * (logVal - ε)) ^ 6) := by
  obtain ⟨N, hN⟩ := dwz63_exists_fineCellWeight_logVal K q zero hzero k hq a mass hmasseq hmass0
    ha logVal hrate ε hε
  refine ⟨N, fun j hj n hn ↦ ?_⟩
  exact hasTauWeight_symSix_region_of_oneSegment ((cwPartitionedTensor K q).positivePower 1)
    cwSquareDegreeMap n M Leg.Z t₀ (WordType.proportionalCounts a j)
    (dwz63ZeroCellTarget zero k n) (hN j hj n hn) (Real.exp_pos _).le

/-! ## The leaf's `sym₆`-weight -/

/-- **The section 6.3 reference leaf's `sym₆`-weight, from its fifteen regions.**

Stage (D)'s conditional regional composition: the sorting permutation of
`dwz63_referenceLeaf_isomorphic_consecutive` puts the fifteen segments in consecutive blocks, and
`hasTauWeight_symSix_segmentedLocalizedSplittingPower_regional` divides the leaf along them and
multiplies the fifteen weights.  The conclusion is the shape
`omega_lt_2374631_of_plainBatchedStageAndLeaf`'s `hleafWeight` binder consumes, at the weight
`SegmentRegionSpec.totalValue`, which is the product of the fifteen cell weights.  It is
conditional, not closed: `hw` is precisely the still-open fifteen-weight bundle, three of whose
entries (the orbit rows) depend on the typed-cut `112`/`beta` obligation of image 104.

Proof sketch: `dwz63_referenceLeaf_isomorphic_consecutive` produces, from the multiplicity
hypothesis `hmult`, a position permutation `σ` together with an isomorphism between the leaf at
the reference segmentation and the leaf whose segments are consecutive blocks;
`Restricts.symSix_congr` carries that isomorphism's restriction through `sym₆`, so
`HasTauWeight.of_restricts` reduces the goal to the consecutive-block leaf.  There
`hasTauWeight_symSix_segmentedLocalizedSplittingPower_regional`, applied to the bundle `hw σ` at
that same `σ` --- which is why the bundle is asked at *every* permutation --- divides the leaf
region by region and returns the product weight at `SegmentRegionSpec.totalValue`.  Rewriting by
`hparent` replaces the recursion's parent type by `alphaTilde`, which is the profile the statement
is phrased with. -/
theorem dwz63_hasTauWeight_symSix_referenceLeaf_of_regional
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (b : SegmentRegionBlock (fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z 15)
    (rest : List (SegmentRegionBlock (fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z 15))
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support)
      (SegmentRegionBlock.total b rest))
    (hmult : WordType.multiplicity
        (dwz63Seg K (SegmentRegionBlock.total b rest) wRef) =
      SegmentRegionBlock.multiplicityProfile b rest)
    (hparent : SegmentRegionSpec.parentType b.toSegmentRegionSpec
      (SegmentRegionBlock.specs rest) = alphaTilde)
    (hb : 0 ≤ b.value) (hrestnn : ∀ u ∈ SegmentRegionBlock.specs rest, 0 ≤ u.value)
    (hw : ∀ σ : Equiv.Perm (Fin (SegmentRegionBlock.total b rest + 1)),
      SegmentedRegionalSymSixWeights ((cwPartitionedTensor K dwz63Q).positivePower 1)
        cwSquareDegreeMap Leg.Z dwz63Tau b.toSegmentRegionSpec (SegmentRegionBlock.specs rest)
        (SegmentRegionBlock.seg b rest)
        (positionRelabelBlockAddress (fun _ : Leg ↦ Fin 5)
          (SegmentRegionBlock.total b rest) σ
          (positiveSupportWordBlockAddress
            ((cwSquarePartitionedTensor K dwz63Q).support)
            (SegmentRegionBlock.total b rest) wRef))) :
    HasTauWeight K
      (symSix K ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap (SegmentRegionBlock.total b rest) 15
        (dwz63Seg K (SegmentRegionBlock.total b rest) wRef)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde)
        (positiveSupportWordBlockAddress
          ((cwSquarePartitionedTensor K dwz63Q).support)
          (SegmentRegionBlock.total b rest) wRef)).realize)) dwz63Tau
      (SegmentRegionSpec.totalValue b.toSegmentRegionSpec (SegmentRegionBlock.specs rest)) := by
  obtain ⟨σ, hiso⟩ :=
    dwz63_referenceLeaf_isomorphic_consecutive K alphaTilde b rest wRef hmult
  refine HasTauWeight.of_restricts (Tensor.Restricts.symSix_congr hiso.restricts) ?_
  have hreg := hasTauWeight_symSix_segmentedLocalizedSplittingPower_regional
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap Leg.Z
    b.toSegmentRegionSpec (SegmentRegionBlock.specs rest)
    (SegmentRegionBlock.seg b rest)
    (positionRelabelBlockAddress (fun _ : Leg ↦ Fin 5)
      (SegmentRegionBlock.total b rest) σ
      (positiveSupportWordBlockAddress
        ((cwSquarePartitionedTensor K dwz63Q).support)
        (SegmentRegionBlock.total b rest) wRef))
    hb hrestnn (hw σ)
  rw [hparent] at hreg
  exact hreg

end AlgebraicComplexity.Examples
