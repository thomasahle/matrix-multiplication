/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerExtraction
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightPresentFixedCellWholeStage

set_option autoImplicit false

/-!
# The present fixed-cell whole stage at a concrete marked rational typed leaf

`cwTotalWeightPresentMarkedFixedTargetCellType_wholeStage` derives the assembled product
restriction of the present fixed-cell route, but it still asks its caller for the canonical inner
restriction `hcanonical`, together with an abstract index type `J` and its cardinality.

Those are not genuine mathematics: the committed inner extraction
`cwTotalWeightLocalizedFineTypes_restricts_markedLeafDirectSum` already produces exactly that
restriction for a rational typed leaf.  This module performs the composition once, so that no
downstream client carries `hcanonical` as a hypothesis.

## What is instantiated rather than assumed

* `fineType` becomes `cwTotalWeightFineMarginalType K q depth (WordType.proportionalCounts
  leaf.profile.count k)`.
* `J` becomes the inner hash encoding's `markedLegwiseIsolatedPowerAddresses` on the localized
  ambient and marked fiber words.  It is a `Finset` coercion, so its `Fintype` instance is the
  canonical one and `hcardJ` is `rfl`; the resulting count is the *exact* finite cardinality, not
  a bound.
* `xSize`, `ySize`, `zSize` become `leaf.dimensionProduct .X/.Y/.Z ^ k`.

The one step that is not definitional is the address spelling.  The inner extraction is stated at
`positiveSupportWordBlockAddress … coarseWord`, while the stage carries a raw `reference`, so the
recovered supported word is transported along
`positiveSupportWordBlockAddress_cwTotalWeightCoarseWordOfAddress` — the same rewrite the
whole-stage file performs internally.  The support premise that transport needs is **not** a new
hypothesis: it is mechanical from `hreferenceMem`, whose membership projects through
`PartitionHashEncoding.presentMarkedXYIsolatedPowerAddresses` and
`PartitionedTensor.withSupport_support` to `reference ∈ actualSupport`, and then through the
inherited `hactualSupport`.  It is derived locally in the body, so this module adds **no** named
hypothesis to the whole stage's own.

## What is deliberately not done here

No lower bound on the surviving `zSupport.card` is proved or assumed, no upstream restriction into
the supported coarse source is supplied, and no identification of that source with a finer
exact-interface-term target is made.  Those are the disjoint remaining seams.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w x y

noncomputable section

/-- The reference address of a present marked fixed-cell stage lies in the coarse positive-power
support.

This is mechanical from premises the whole stage already carries, so it is *not* a hypothesis of
the wrapper below.  `hreferenceMem` lands in
`H.presentMarkedXYIsolatedPowerAddresses … ((Q.positivePower n).withSupport actualSupport)`, whose
definition is that support intersected with the abstract marked family; projecting the first
component and applying the inherited `hactualSupport` gives exactly the premise
`cwTotalWeightCoarseWordOfAddress` needs. -/
theorem cwTotalWeightPresentMarked_reference_mem_coarseSupport
    {R : Type u} [Field R] [NeZero (2 : R)]
    (K : Type v) [CommRing K] (q depth n : ℕ)
    (actualSupport : Finset
      (BlockAddress (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hactualSupport : actualSupport ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    {support : Finset (BlockAddress (fun _c : Leg ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (reference : BlockAddress
      (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n))
    (hreferenceMem : reference ∈
      H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed
        ((((cwChunkPartitionedTensor K q depth).coarsen
          (cwTotalWeightChunkCoarsening depth)).positivePower n).withSupport actualSupport)) :
    reference ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support := by
  have hmem :
      reference ∈ actualSupport ∩
        H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed := by
    simpa only [
      PartitionHashEncoding.presentMarkedXYIsolatedPowerAddresses,
      PartitionedTensor.withSupport_support
    ] using hreferenceMem
  exact hactualSupport (Finset.mem_inter.mp hmem).1

/-- **The present fixed-cell whole stage with its canonical inner restriction discharged.**

Every argument of `cwTotalWeightPresentMarkedFixedTargetCellType_wholeStage` that described the
inner extraction abstractly is instantiated from the committed rational typed-leaf theorem.  The
resulting stage has exactly `zSupport.card * Fintype.card J` equal rectangular matrix
multiplications of side lengths `leaf.dimensionProduct .X/.Y/.Z ^ k`, where `J` is the inner
marked isolated address family. -/
def cwTotalWeightPresentMarkedFixedTargetCellType_wholeStage_ofMarkedLeaf
    {R : Type u} [Field R] [NeZero (2 : R)]
    (K : Type v) [CommRing K] (q depth n : ℕ)
    {Part : Type w} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    {support : Finset (BlockAddress (fun _c : Leg ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (actualSupport : Finset
      (BlockAddress (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hactualSupport : actualSupport ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (hmodeled : actualSupport ⊆
      H.modeledAddresses n (H.legalTargets n ambientWords))
    (reference : BlockAddress
      (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n))
    (hreferenceMem : reference ∈
      H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed
        ((((cwChunkPartitionedTensor K q depth).coarsen
          (cwTotalWeightChunkCoarsening depth)).positivePower n).withSupport actualSupport))
    (hreference : CWTotalWeightReferenceProfiles
      depth n partAt rawTargets reference)
    {Rinner : Type y} [Field Rinner] [NeZero (2 : Rinner)]
    {C : Leg → Type x} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ s c,
      leaf.dimension s c = cwChunkConstituentDimension K q depth s c)
    (Hinner : PartitionHashEncoding (R := Rinner)
      (cwChunkPartitionedTensor K q depth).support)
    (k : ℕ)
    (Binner : Finset Rinner) (hBinner : ThreeAPFree (Binner : Set Rinner))
    (seedInner : ProgressionHash.Seed Rinner (Fin (n + 1))) :=
  cwTotalWeightPresentMarkedFixedTargetCellType_wholeStage
    (R := R) K q depth n partAt rawTargets H ambientWords markedWords hwords B hB seed
    actualSupport hactualSupport hmodeled reference hreferenceMem hreference
    (fineType := cwTotalWeightFineMarginalType K q depth
      (WordType.proportionalCounts leaf.profile.count k))
    (J := Hinner.markedLegwiseIsolatedPowerAddresses n
      (cwTotalWeightLocalizedAmbientWords K q depth n
        (WordType.proportionalCounts leaf.profile.count k)
        (cwTotalWeightCoarseWordOfAddress K q depth n reference
          (cwTotalWeightPresentMarked_reference_mem_coarseSupport K q depth n
            actualSupport hactualSupport H ambientWords markedWords B seed reference
            hreferenceMem)))
      (cwTotalWeightMarkedFiberWords K q depth n
        (WordType.proportionalCounts leaf.profile.count k)
        (cwTotalWeightCoarseWordOfAddress K q depth n reference
          (cwTotalWeightPresentMarked_reference_mem_coarseSupport K q depth n
            actualSupport hactualSupport H ambientWords markedWords B seed reference
            hreferenceMem)))
      Binner seedInner)
    (innerCopies := Fintype.card
      (Hinner.markedLegwiseIsolatedPowerAddresses n
        (cwTotalWeightLocalizedAmbientWords K q depth n
          (WordType.proportionalCounts leaf.profile.count k)
          (cwTotalWeightCoarseWordOfAddress K q depth n reference
          (cwTotalWeightPresentMarked_reference_mem_coarseSupport K q depth n
            actualSupport hactualSupport H ambientWords markedWords B seed reference
            hreferenceMem)))
        (cwTotalWeightMarkedFiberWords K q depth n
          (WordType.proportionalCounts leaf.profile.count k)
          (cwTotalWeightCoarseWordOfAddress K q depth n reference
          (cwTotalWeightPresentMarked_reference_mem_coarseSupport K q depth n
            actualSupport hactualSupport H ambientWords markedWords B seed reference
            hreferenceMem)))
        Binner seedInner))
    (xSize := leaf.dimensionProduct .X ^ k)
    (ySize := leaf.dimensionProduct .Y ^ k)
    (zSize := leaf.dimensionProduct .Z ^ k)
    (hcardJ := rfl)
    (hcanonical := by
      simpa only [positiveSupportWordBlockAddress_cwTotalWeightCoarseWordOfAddress
          K q depth n reference
            (cwTotalWeightPresentMarked_reference_mem_coarseSupport K q depth n
              actualSupport hactualSupport H ambientWords markedWords B seed reference
              hreferenceMem)] using
        cwTotalWeightLocalizedFineTypes_restricts_markedLeafDirectSum
          K q depth leaf hdimension Hinner n k
          (cwTotalWeightCoarseWordOfAddress K q depth n reference
          (cwTotalWeightPresentMarked_reference_mem_coarseSupport K q depth n
            actualSupport hactualSupport H ambientWords markedWords B seed reference
            hreferenceMem))
          Binner hBinner seedInner)

end

end AlgebraicComplexity.Examples
