import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerSequenceDepth
import MatrixMultiplication.TotalWeightAcceptanceFloors
import MatrixMultiplication.TotalWeightLeanEndpoint

set_option autoImplicit false

/-!
# Level-four canonical inner extraction feeding the total-weight endpoint

`MatrixMultiplication.TotalWeightLeanEndpoint.omega_lt_236999_of_nestedAcceptanceData` consumes a
depth-four outer sequence together with a `CanonicalInnerSequenceData` over it.  Until now the only
constructor for the inner datum, `exists_cwTotalWeightCanonicalInnerSequenceData`, was pinned to
recursion depth one, so the second argument had no producer at the depth the endpoint demands.

`AlgebraicComplexity.Examples.exists_cwTotalWeightCanonicalInnerSequenceData_ofDepth` removes that
pin.  This module records the resulting one-step endpoint adapter at the certificate's exact
parameters `q = 5`, `depth = 4`, `stride = TotalWeightAcceptanceFloors.strideValue` (`= 38`),
`T = CW_5^{⊗8}`.  The stride is taken from the `C′` acceptance-floor module rather than spelled as
a literal, so the single place fixing it stays
`MatrixMultiplication/TotalWeightAcceptanceFloors.strideValue`.

Three things are worth reading off the statement.

* No numerical entropy or compatibility constant occurs.  The quantitative inputs are exactly the
  inner growth datum's ambient-cardinality bound, the rate inequality `hWrate`, and the volume
  inequality `hvolume`.
* `hvolume` is the only adapter between the endpoint's base-two volume convention
  `2 ^ (3 * stride * volumeFloor)` and the exact leafwise dimension product produced by the inner
  extraction; `CanonicalInnerSequenceData.ofVolumeBase_le` discharges it.
* Nothing here supplies the outer datum.  Constructing a depth-four
  `CWTotalWeightLocalizedOuterSequenceData` at stride `strideValue` remains the open certificate
  obligation.
-/

namespace MatrixMultiplication.TotalWeightLeanEndpoint

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.TotalWeightVolumeEndpoint

universe u w

/-- The depth-four canonical inner extraction discharges the second argument of
`omega_lt_236999_of_nestedAcceptanceData`.

Given the level-four outer total-weight sequence at stride `strideValue`, one rational typed leaf of
the depth-four chunk partition with the canonical dimensions, and a localized conditional-growth
datum for it whose rate clears the inner acceptance floor, the requested exponent bound follows. -/
theorem omega_lt_236999_of_levelFourCanonicalInner
    (K : Type u) [Field K]
    (outer : CWTotalWeightLocalizedOuterSequenceData.{u, u, w}
      K 5 4 (Tensor.power (coppersmithWinograd K 5) 8)
        TotalWeightAcceptanceFloors.strideValue
        ((2 : ℝ) ^ (((TotalWeightAcceptanceFloors.strideValue : ℕ) : ℝ) *
          acceptanceOuterRetainedFloor)))
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K 5 4).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K 5 4 support c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (growth : CWTotalWeightInnerGrowthDataAtDepth K 5 4 leaf.profile.count
      ambientBase ambientLoss)
    (hn : ∀ r, outer.n r = growth.exponent r)
    (hfine : ∀ r, outer.fineType r =
      cwTotalWeightFineMarginalType K 5 4
        (WordType.proportionalCounts leaf.profile.count r))
    (hcoarseWordType : ∀ r i,
      WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K 5 4) (outer.n r)
            (outer.coarseWord r i)) =
        WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K 5 4) (outer.n r)
            (positiveWordCast (hn r).symm (growth.coarseWord r))))
    {δ : ℝ} (hδ : 1 < δ)
    (hWrate : (2 : ℝ) ^ (((TotalWeightAcceptanceFloors.strideValue : ℕ) : ℝ) *
        acceptanceInnerRetainedFloor) <
      cwTotalWeightInnerTargetBase K 5 4 leaf.profile.count /
        (δ * cwTotalWeightInnerCompetitorBase K 5 4 leaf.profile.count ambientBase))
    (hvolume : (2 : ℝ) ^ (3 * ((TotalWeightAcceptanceFloors.strideValue : ℕ) : ℝ) * volumeFloor) ≤
      ((leaf.dimensionProduct .X * leaf.dimensionProduct .Y *
        leaf.dimensionProduct .Z : ℕ) : ℝ)) :
    omega K < acceptanceTarget := by
  obtain ⟨inner⟩ :=
    exists_cwTotalWeightCanonicalInnerSequenceData_levelFour outer leaf hdimension growth
      hn hfine hcoarseWordType hδ
      (Real.rpow_pos_of_pos (by norm_num) _) hWrate
  exact omega_lt_236999_of_nestedAcceptanceData K outer
    (inner.ofVolumeBase_le (Real.rpow_pos_of_pos (by norm_num) _) hvolume)

end MatrixMultiplication.TotalWeightLeanEndpoint
