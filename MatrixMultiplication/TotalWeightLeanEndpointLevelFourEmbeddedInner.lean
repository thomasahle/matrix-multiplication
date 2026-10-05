/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightEmbeddedInnerSequenceDepth
import MatrixMultiplication.TotalWeightAcceptanceFloors

set_option autoImplicit false

/-!
# Sparse depth-four inner extraction feeding the C′ acceptance endpoint

This is the certificate-facing endpoint for a rational typed leaf carried by its actual positive
alphabet rather than the full depth-four chunk support.  It exposes precisely the remaining data:
the outer sequence, the sparse leaf embedding, the ambient-growth certificate for its zero-extended
profile, the fixed coarse-type transport, and the two directed rate inequalities.

The theorem constructs the complete inner sequence using the marked hashing theorem and then calls
the homogeneous acceptance argument at an arbitrary fixed positive stride.  It does not assume a
degeneration of the assembled inner family.  In particular an exact dyadic certificate may use a
large common-denominator stride; no approximation to an artificial mass-nineteen profile is
required.
-/

namespace MatrixMultiplication.TotalWeightLeanEndpoint

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.TotalWeightAcceptanceFloors

universe u w x z

private theorem strict_of_feasibility_with_slack
    {omegaValue budget retained matrix target : ℝ}
    (hmatrix : 0 < matrix)
    (hslack : budget < retained + target * matrix)
    (feasibility : ∀ Ω, budget ≤ retained + Ω * matrix → omegaValue ≤ Ω) :
    omegaValue < target := by
  let Ω := (budget - retained) / matrix
  have hΩ : Ω < target := by
    apply (div_lt_iff₀ hmatrix).2
    linarith
  have hfeasible : budget ≤ retained + Ω * matrix := by
    have hmatrixNe : matrix ≠ 0 := hmatrix.ne'
    dsimp [Ω]
    rw [div_mul_cancel₀ (budget - retained) hmatrixNe]
    linarith
  exact (feasibility Ω hfeasible).trans_lt hΩ

/-- The C′ acceptance arithmetic is homogeneous in every fixed stride.  The earlier literal
stride-38 theorem is one specialization; exact certificate denominators may instead be absorbed
into a larger stride without changing either exponent. -/
theorem omega_lt_236999_of_subexponentialVolumeSequence_acceptance_anyStride
    (K : Type u) [Field K] {stride : ℕ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retainedFloor))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volumeFloor))) :
    omega K < acceptanceTarget := by
  have hextract : CurrentProofObligations.CurrentLaserExtraction K retainedFloor volumeFloor :=
    CurrentProofObligations.CurrentLaserExtraction.of_subexponentialVolumeSequence K hextractions
  refine strict_of_feasibility_with_slack volumeFloor_pos
    sourceRankBudget_lt_acceptance_endpoint ?_
  intro Ω hbudget
  exact CurrentProofObligations.omega_le_of_currentLaserExtraction K volumeFloor_pos
    hextract hbudget

/-- A sparse embedded depth-four leaf meeting the C′ inner-rate and volume floors, combined with
the C′ outer sequence at any exact common-denominator stride, proves `omega < 2.36999`. -/
theorem omega_lt_236999_of_levelFourEmbeddedCanonicalInner
    (K : Type u) [Field K]
    {stride : ℕ}
    (outer : CWTotalWeightLocalizedOuterSequenceData.{u, u, w}
      K 5 4 (Tensor.power (coppersmithWinograd K 5) 8) stride
        ((2 : ℝ) ^ ((stride : ℝ) * outerRetainedFloor)))
    {I : Type z} [Fintype I] [Nonempty I]
    {C : Leg → Type x} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K 5 4).support)
    (hdimension : ∀ i c,
      leaf.dimension i c = cwChunkConstituentDimension K 5 4 (letter i) c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (growth : CWTotalWeightInnerGrowthDataAtDepth K 5 4
      (cwEmbeddedChunkProfile leaf letter) ambientBase ambientLoss)
    (hn : ∀ r, outer.n r = growth.exponent r)
    (hfine : ∀ r, outer.fineType r =
      cwTotalWeightFineMarginalType K 5 4
        (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) r))
    (hcoarseWordType : ∀ r i,
      WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K 5 4) (outer.n r)
            (outer.coarseWord r i)) =
        WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K 5 4) (outer.n r)
            (positiveWordCast (hn r).symm (growth.coarseWord r))))
    {δ : ℝ} (hδ : 1 < δ)
    (hWrate :
      (2 : ℝ) ^ ((stride : ℝ) * innerRetainedFloor) <
        cwTotalWeightInnerTargetBase K 5 4 (cwEmbeddedChunkProfile leaf letter) /
          (δ * cwTotalWeightInnerCompetitorBase K 5 4
            (cwEmbeddedChunkProfile leaf letter) ambientBase))
    (hvolume : (2 : ℝ) ^ (3 * (stride : ℝ) * volumeFloor) ≤
      ((leaf.dimensionProduct .X * leaf.dimensionProduct .Y *
        leaf.dimensionProduct .Z : ℕ) : ℝ)) :
    omega K < acceptanceTarget := by
  obtain ⟨inner⟩ :=
    exists_cwTotalWeightEmbeddedCanonicalInnerSequenceData_ofDepth
      outer leaf letter hdimension growth hn hfine hcoarseWordType hδ
      (Real.rpow_pos_of_pos (by norm_num) _) hWrate
  have hsequence := inner.toSubexponentialLaserVolumeSequence_addRetained
  have hcopy :
      (2 : ℝ) ^ ((stride : ℝ) * retainedFloor) ≤
        (2 : ℝ) ^ ((stride : ℝ) *
          (outerRetainedFloor + innerRetainedFloor)) := by
    rw [retainedFloor_eq_outer_add_inner]
  exact omega_lt_236999_of_subexponentialVolumeSequence_acceptance_anyStride K
    (hsequence.mono (by positivity) hcopy (by positivity) hvolume)

end MatrixMultiplication.TotalWeightLeanEndpoint
