import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerGrowthDepthFour
import MatrixMultiplication.TotalWeightLeanEndpointLevelFourInner

set_option autoImplicit false

/-!
# The level-four endpoint with its inner growth datum and volume floor supplied

`MatrixMultiplication.TotalWeightLeanEndpoint.omega_lt_236999_of_levelFourCanonicalInner` takes
seven inputs beyond the outer sequence: a rational typed leaf of the depth-four chunk partition,
the identification `hdimension` of its dimension table with the canonical chunk dimensions, a
`CWTotalWeightInnerGrowthDataAtDepth` over it, the three index-alignment equations
`hn`/`hfine`/`hcoarseWordType`, the rate inequality `hWrate`, and the volume inequality `hvolume`.

`AlgebraicComplexity/Examples/CoppersmithWinogradTotalWeightInnerGrowthDepthFour.lean` supplies the
growth datum with its `ambient_upper` field *proved*, and proves the volume inequality for any leaf
that puts multiplicity at least `19` on the all-`cw011` chunk letter.  This module plugs both in.

Two theorems are recorded.

* `omega_lt_236999_of_levelFourOuter_innerLeaf` is the leaf-generic one: it consumes any
  canonical-dimension depth-four leaf together with the maximum-entropy certificate for its
  normalized profile, and leaves open only the outer sequence, the three alignment equations, and
  the rate inequality `hWrate`.  This is the shape the assembly should use.
* `omega_lt_236999_of_levelFourOuter_constantInnerLeaf` specializes it to the unconditional
  constant-`19` leaf, whose maximum-entropy certificate is proved outright.

## The alignment blocker, restated

The depth-four outer datum has `n r = 19 * r - 1`, so `hn` forces
`profileMass leaf.profile.count = 19`.  `PositiveIntegralProfile.count_pos` forces
`profileMass ≥ 6 ^ 16` for any leaf over the full depth-four chunk support.  Consequently the
*constant* specialization below can never have its `hn` discharged, and the leaf-generic theorem is
usable only once a sparse/embedded leaf alphabet is available
(`EmbeddedRationalTypedLeaf*`, `CoppersmithWinogradTotalWeightEmbeddedInner*`).  Nothing in this
module hides that: `hn` is an explicit hypothesis of both statements.
-/

namespace MatrixMultiplication.TotalWeightLeanEndpoint

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.TotalWeightVolumeEndpoint

universe u

/-- The endpoint's volume floor is at most `3755689/625000`, the threshold of
`AlgebraicComplexity.Examples.two_rpow_le_five_pow_304`. -/
theorem volumeFloor_le_threshold : volumeFloor ≤ 3755689 / 625000 := by
  norm_num [volumeFloor,
    MatrixMultiplication.Generated.TotalQuotientVolumeScalar.volumeFloor]

/-- Any canonical-dimension depth-four leaf with multiplicity at least `19` on the all-`cw011`
chunk letter clears the endpoint's volume floor, in the endpoint's own `((38 : ℕ) : ℝ)`
spelling. -/
theorem levelFour_volumeFloor_endpoint
    (K : Type u) [CommRing K]
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf (cwChunkPartitionedTensor K 5 4).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K 5 4 support c)
    (hcount : 19 ≤ leaf.profile.count (cwChunkOneTypeWitness K 5 4)) :
    (2 : ℝ) ^ (3 * ((38 : ℕ) : ℝ) * volumeFloor) ≤
      ((leaf.dimensionProduct .X * leaf.dimensionProduct .Y *
        leaf.dimensionProduct .Z : ℕ) : ℝ) := by
  have hcast : ((38 : ℕ) : ℝ) = (38 : ℝ) := by norm_num
  rw [hcast]
  exact cwChunkLevelFour_volumeFloor_of_oneTypeCount K leaf hdimension hcount
    volumeFloor_le_threshold

/-- **The level-four endpoint with the inner growth datum and the volume floor supplied.**

Compared with `omega_lt_236999_of_levelFourCanonicalInner` this theorem no longer takes a growth
datum or a volume inequality: the datum is
`cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe`, whose `ambient_upper` field is proved from the
maximum-entropy hypothesis by the method-of-types layer, and the volume inequality follows from the
one-type multiplicity hypothesis. -/
theorem omega_lt_236999_of_levelFourOuter_innerLeaf
    (K : Type u) [Field K]
    (outer : CWTotalWeightLocalizedOuterSequenceData.{u, u, u}
      K 5 4 (Tensor.power (coppersmithWinograd K 5) 8) 38
        ((2 : ℝ) ^ (((38 : ℕ) : ℝ) * acceptanceOuterRetainedFloor)))
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf (cwChunkPartitionedTensor K 5 4).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K 5 4 support c)
    (hcount : 19 ≤ leaf.profile.count (cwChunkOneTypeWitness K 5 4))
    (hmass : 0 < WordType.profileMass leaf.profile.count)
    (hmaximum : WordType.IsMaximumEntropyInMappedFiber (cwChunkCoordinate K 5 4)
      (WordType.normalizedProfileProbability leaf.profile.count hmass))
    (hn : ∀ r, outer.n r =
      (cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe K 5 4 leaf.profile.count
        hmass hmaximum).exponent r)
    (hfine : ∀ r, outer.fineType r =
      cwTotalWeightFineMarginalType K 5 4
        (WordType.proportionalCounts leaf.profile.count r))
    (hcoarseWordType : ∀ r i,
      WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K 5 4) (outer.n r)
            (outer.coarseWord r i)) =
        WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K 5 4) (outer.n r)
            (positiveWordCast (hn r).symm
              ((cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe K 5 4 leaf.profile.count
                hmass hmaximum).coarseWord r))))
    {δ : ℝ} (hδ : 1 < δ)
    (hWrate : (2 : ℝ) ^ (((38 : ℕ) : ℝ) * acceptanceInnerRetainedFloor) <
      cwTotalWeightInnerTargetBase K 5 4 leaf.profile.count /
        (δ * cwTotalWeightInnerCompetitorBase K 5 4 leaf.profile.count
          (cwChunkAmbientEntropyBase leaf.profile.count))) :
    omega K < acceptanceTarget :=
  omega_lt_236999_of_levelFourCanonicalInner K outer leaf hdimension
    (cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe K 5 4 leaf.profile.count hmass hmaximum)
    hn hfine hcoarseWordType hδ hWrate
    (levelFour_volumeFloor_endpoint K leaf hdimension hcount)

/-- The constant-`19` specialization.  Its maximum-entropy hypothesis is proved outright
(`WordType.isMaximumEntropyInMappedFiber_const`); its `hn` is the one that the alignment blocker
makes unsatisfiable, and is left explicit. -/
theorem omega_lt_236999_of_levelFourOuter_constantInnerLeaf
    (K : Type u) [Field K]
    (outer : CWTotalWeightLocalizedOuterSequenceData.{u, u, u}
      K 5 4 (Tensor.power (coppersmithWinograd K 5) 8) 38
        ((2 : ℝ) ^ (((38 : ℕ) : ℝ) * acceptanceOuterRetainedFloor)))
    (hn : ∀ r, outer.n r = (cwChunkConstantInnerGrowthDataLevelFour K).exponent r)
    (hfine : ∀ r, outer.fineType r =
      cwTotalWeightFineMarginalType K 5 4
        (WordType.proportionalCounts (cwChunkConstantLeafLevelFour K).profile.count r))
    (hcoarseWordType : ∀ r i,
      WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K 5 4) (outer.n r)
            (outer.coarseWord r i)) =
        WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K 5 4) (outer.n r)
            (positiveWordCast (hn r).symm
              ((cwChunkConstantInnerGrowthDataLevelFour K).coarseWord r))))
    {δ : ℝ} (hδ : 1 < δ)
    (hWrate : (2 : ℝ) ^ (((38 : ℕ) : ℝ) * acceptanceInnerRetainedFloor) <
      cwTotalWeightInnerTargetBase K 5 4 (cwChunkConstantLeafLevelFour K).profile.count /
        (δ * cwTotalWeightInnerCompetitorBase K 5 4
          (cwChunkConstantLeafLevelFour K).profile.count
          (WordType.proportionalEntropyBase
            (cwChunkConstantLeafLevelFour K).profile.count))) :
    omega K < acceptanceTarget :=
  omega_lt_236999_of_levelFourCanonicalInner K outer (cwChunkConstantLeafLevelFour K)
    (fun _ _ ↦ rfl) (cwChunkConstantInnerGrowthDataLevelFour K)
    hn hfine hcoarseWordType hδ hWrate
    (levelFour_volumeFloor_endpoint K (cwChunkConstantLeafLevelFour K)
      (fun _ _ ↦ rfl) (le_refl 19))

end MatrixMultiplication.TotalWeightLeanEndpoint
