/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerGrowth
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightNestedComposition

set_option autoImplicit false

/-!
# Canonical total-weight inner extraction sequence

This module joins the exact canonical Behrend family for **one rational typed leaf** and its
asymptotic count bound to the nested total-weight sequence interface.  The selected-address
subtype itself is used as the inner index; there is no representative-leaf replacement.

This leafwise constructor deliberately does not claim the heterogeneous aggregate rate used by a
full recursive certificate.  Externally multiplying instances of this theorem yields the sum of
the leafwise minima.  A certificate whose objective is the minimum of the three *aggregate*
directional totals must instead hash the assembled product family before taking that minimum.

The only outer-stage hypotheses are semantic alignment statements: its localized exponent and
fine marginal type must be the ones used by the inner growth datum, and all retained coarse words
must have the same exact coarse type as the canonical representative.  Numerical entropy or
certificate constants do not occur here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w

/-- Every exact dimension product of a rational typed leaf is positive. -/
theorem rationalTypedLeaf_dimensionProduct_pos
    {I : Type*} [Fintype I] [Nonempty I]
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf I C) (c : Leg) :
    0 < leaf.dimensionProduct c := by
  unfold RationalTypedLeaf.dimensionProduct
  exact Finset.prod_pos fun i _hi ↦ pow_pos (leaf.dimension_pos i c) _

/-- Construct one leafwise canonical inner sequence from the localized conditional-growth datum.

`hn` and `hfine` identify the outer constituent's semantic parameters with the exact inner
profile. `hcoarseWordType` is the ordinary fixed-coarse-type invariant produced by quotient
extraction; it is precisely what transports the one canonical degeneration to every survivor.

The inner base may be any `W` strictly below the target/field quotient after the temporary
`δ > 1` reserve used to absorb the subexponential prime loss.  This quotient contains a maximum
over the three competitor legs for this one leaf; do not multiply this constructor over
heterogeneous leaves when the intended objective takes the directional minimum only after
aggregation. -/
theorem exists_cwTotalWeightCanonicalInnerSequenceData
    {K : Type u} [CommRing K] {q : ℕ}
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source} {stride : ℕ} {outerBase : ℝ}
    (outer : CWTotalWeightLocalizedOuterSequenceData.{u, v, w}
      K q 1 T stride outerBase)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q 1 support c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (growth : CWTotalWeightInnerGrowthData K q leaf.profile.count
      ambientBase ambientLoss)
    (hn : ∀ r, outer.n r = growth.exponent r)
    (hfine : ∀ r, outer.fineType r =
      cwTotalWeightFineMarginalType K q 1
        (WordType.proportionalCounts leaf.profile.count r))
    (hcoarseWordType : ∀ r i,
      WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K q 1) (outer.n r)
            (outer.coarseWord r i)) =
        WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K q 1) (outer.n r)
            (positiveWordCast (hn r).symm (growth.coarseWord r))))
    {δ W : ℝ} (hδ : 1 < δ) (hW : 0 < W)
    (hWrate : W < cwTotalWeightInnerTargetBase K q 1 leaf.profile.count /
      (δ * cwTotalWeightInnerCompetitorBase K q 1 leaf.profile.count ambientBase)) :
    Nonempty
      (CWTotalWeightLocalizedOuterSequenceData.CanonicalInnerSequenceData.{u, v, w, 0}
        outer W
          ((leaf.dimensionProduct .X * leaf.dimensionProduct .Y *
            leaf.dimensionProduct .Z : ℕ) : ℝ)) := by
  letI : Nonempty (cwChunkPartitionedTensor K q 1).support :=
    ⟨cwChunkSupportWitness K q 1⟩
  obtain ⟨innerLoss, hinnerLoss, hinnerLossPos, hinnerGrowth⟩ :=
    growth.exists_subexponentialLoss_pow_le_behrendCopies
      leaf hdimension hδ hW hWrate
  let reference : ∀ r,
      PositiveWord (CWTotalWeightCoarseSupport K q 1) (outer.n r) :=
    fun r ↦ positiveWordCast (hn r).symm (growth.coarseWord r)
  let coarseType : ℕ → CWTotalWeightCoarseSupport K q 1 → ℕ :=
    fun r ↦ WordType.multiplicity
      (positiveWordEquiv (CWTotalWeightCoarseSupport K q 1) (outer.n r)
        (reference r))
  let innerCount : ℕ → ℕ := fun r ↦
    cwTotalWeightInnerBehrendCopies K q leaf hdimension
      (growth.exponent r) r (growth.coarseWord r)
  let J : ℕ → Type 0 := fun r ↦
    {a // a ∈ CWTotalWeightInnerBehrendIndex K q leaf hdimension
      (growth.exponent r) r (growth.coarseWord r)}
  let xSize : ℕ → ℕ := fun r ↦ leaf.dimensionProduct .X ^ r
  let ySize : ℕ → ℕ := fun r ↦ leaf.dimensionProduct .Y ^ r
  let zSize : ℕ → ℕ := fun r ↦ leaf.dimensionProduct .Z ^ r
  refine ⟨{
    innerBase_pos := hW
    volumeBase_pos := ?_
    innerLoss := innerLoss
    innerCount := innerCount
    xSize := xSize
    ySize := ySize
    zSize := zSize
    reference := reference
    coarseType := coarseType
    reference_mem := ?_
    coarseWord_mem := ?_
    J := J
    fintypeJ := fun _r ↦ inferInstance
    card_J := ?_
    canonical_degenerates := ?_
    innerLoss_subexponential := hinnerLoss
    innerLoss_pos := fun r _hr ↦ hinnerLossPos r
    innerCount_pos := ?_
    xSize_pos := ?_
    ySize_pos := ?_
    zSize_pos := ?_
    inner_copy_growth := ?_
    volume_growth := ?_
  }⟩
  · exact_mod_cast mul_pos
      (mul_pos (rationalTypedLeaf_dimensionProduct_pos leaf .X)
        (rationalTypedLeaf_dimensionProduct_pos leaf .Y))
      (rationalTypedLeaf_dimensionProduct_pos leaf .Z)
  · intro r
    rw [mem_positiveTypeClass]
  · intro r i
    rw [mem_positiveTypeClass]
    exact hcoarseWordType r i
  · intro r
    simpa only [J, innerCount] using
      card_cwTotalWeightInnerBehrendIndex K q leaf hdimension
        (growth.exponent r) r (growth.coarseWord r)
  · intro r hr
    simp only [hfine r]
    have htransport :=
      cwTotalWeightLocalizedFineTypes_isomorphic_of_length_cast
        K q 1 (hn r).symm (growth.coarseWord r)
        (cwTotalWeightFineMarginalType K q 1
          (WordType.proportionalCounts leaf.profile.count r))
    have hcanonical :=
      cwTotalWeightInnerBehrend_degenerates
        K q leaf hdimension (growth.exponent r) r (growth.coarseWord r)
    exact (PolynomialDegenerates.of_restricts htransport.restricts).trans
      (by simpa [J, xSize, ySize, zSize] using hcanonical)
  · intro r hr
    exact growth.behrendCopies_pos leaf hdimension r hr
  · intro r _hr
    exact pow_pos (rationalTypedLeaf_dimensionProduct_pos leaf .X) r
  · intro r _hr
    exact pow_pos (rationalTypedLeaf_dimensionProduct_pos leaf .Y) r
  · intro r _hr
    exact pow_pos (rationalTypedLeaf_dimensionProduct_pos leaf .Z) r
  · intro r hr
    exact hinnerGrowth r hr
  · intro r _hr
    simp only [xSize, ySize, zSize, Nat.cast_mul, Nat.cast_pow, mul_pow]
    exact le_rfl

end AlgebraicComplexity.Examples
