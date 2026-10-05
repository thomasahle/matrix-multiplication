/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerGrowthDepth

set_option autoImplicit false

/-!
# Depth-generic canonical total-weight inner extraction sequence

`exists_cwTotalWeightCanonicalInnerSequenceData` builds a `CanonicalInnerSequenceData` from a
localized outer sequence, but its statement pins the recursion depth to `1`.  The nested endpoint
chain needs depth `4`.  This module removes that pin.

## Where the depth-one pin actually lives

Everything the depth-one constructor consumes below the hashing field is already stated for a
general `depth`:

* `cwTotalWeightLocalizedFineTypes`, `cwTotalWeightMarkedFiberWords`,
  `cwTotalWeightLocalizedAmbientWords`, `cwTotalWeightFineMarginalType`,
  `cwTotalWeightConditionalLegType`, `cwTotalWeightCoarseProfile`,
  `cwTotalWeightInnerTargetBase`, `cwTotalWeightInnerCompetitorBase`,
  `cwTotalWeightInnerCompetitorInputLoss`;
* the finite extraction theorems `exists_seed_many_cwTotalWeightLocalizedMarkedLeafDirectSum`
  and `cwTotalWeightNestedLaserVolumeStage_of_fixedCoarseType`;
* the counting bridge `cwTotalWeight_sourceWordLegFiber_card_le_entropyQuotient`;
* the sequence interfaces `CWTotalWeightLocalizedOuterSequenceData` and
  `CanonicalInnerSequenceData`.

The single mathematically real depth-one ingredient is the *partition hash encoding*
`cwLevelTwoChunkPartitionHashEncoding`: it reads an ordered pair of CW blocks as a two-digit
base-three numeral in `{0,…,8}` and uses the resulting constant coordinate sum `8`.  That is a
level-two accident of the digit count, not of the argument.  A depth-`d` native chunk is a word of
`2^d` CW blocks, and reading that word as a `2^d`-digit base-three numeral is again injective with
again a constant coordinate sum, because every supported CW address has coordinate digit sum two
*at every position*.  The generalization is therefore parametric, and it is carried out one module
upstream, in `Examples/CoppersmithWinogradChunkHashEncoding.lean`, where the level-two encoding it
replaces already lived.

The chunk/word-alignment identity `cwChunkPartitionedTensor K q depth =
(cwPartitionedTensor K q).positivePower (2^depth - 1)` and its power isomorphism play no role in
the inner constructor at all: the inner leaf sees the coarse structure only through
`outer.n`, `outer.fineType` and `outer.coarseWord`, and the alignment obligation
`Restricts (Tensor.power T (stride * r)) …` is discharged once, inside the *outer* datum.  Hence
no `8 * 38 * r` versus `16 * m` arithmetic occurs here, and stride `38` is simply carried.

## Facts restated depth-generically in this module

The following declarations are the depth-generic counterparts of declarations that exist only at
`depth = 1`; each is proved by the same argument as its depth-one sibling.

The depth-generic *encoding* is no longer among them.  It was consolidated into its natural
upstream home `Examples/CoppersmithWinogradChunkHashEncoding.lean`, which now carries
`natBaseCode` and its lemmas, `cwChunkAlphabetSize`, `splitWordCode`, `cwChunkNatCode`,
`cwChunkNatTarget`, `cwChunkFieldValue`, `cwChunkSupport_nonempty` and
`cwChunkPartitionHashEncoding` — together with the two regression pins `cwChunkNatTarget_one`,
`cwChunkNatCode_one` and the depth-one `cwLevelTwo…` family, whose proofs are one-line corollaries
of the generic ones.  Every name is unchanged and reaches this module through the import chain.

Two of the four groups below were split out under the repository's 900-line module rule, without
any name, statement or import-path change: the depth-generic prime field now lives in
`Examples/CoppersmithWinogradTotalWeightInnerPrimeHashingDepth.lean` and the depth-generic growth
packaging in `Examples/CoppersmithWinogradTotalWeightInnerGrowthDepth.lean`; this module imports
the latter, which imports the former, so a client that imports this module sees exactly the set of
declarations it saw before.

* the prime hashing field: `cwTotalWeightInnerLegFiberMaximumAtDepth`,
  `cwTotalWeightInnerCompetitorRequirementAtDepth`, `cwTotalWeightInnerHashModulusAtDepth`,
  `CWTotalWeightInnerHashFieldAtDepth`, `cwTotalWeightInnerPartitionHashEncodingAtDepth`,
  `cwTotalWeightInnerPrimeField_quarterBudgetAtDepth`,
  `exists_seed_many_cwTotalWeightInnerPrimeMarkedLeafDirectSumAtDepth`, together with the four
  finite bounding lemmas of `CoppersmithWinogradTotalWeightInnerPrimeHashing`;
* the growth packaging: `cwTotalWeightInnerCompetitorRequirement_cast_le_atDepth`,
  `cwTotalWeightInnerHashModulus_cast_le_atDepth`, `CWTotalWeightInnerGrowthDataAtDepth` and its
  namespace, `cwTotalWeightInnerBehrendBucketsAtDepth`, `cwTotalWeightInnerBehrendSeedAtDepth`,
  `cwTotalWeightInnerBehrendCopiesAtDepth`, `CWTotalWeightInnerBehrendIndexAtDepth`,
  `cwTotalWeightInnerBehrend_hashCountAtDepth`,
  `cwTotalWeightInnerBehrend_degeneratesAtDepth`, and the three asymptotic theorems of
  `CWTotalWeightInnerGrowthData`;
* the constructor `exists_cwTotalWeightCanonicalInnerSequenceData_ofDepth` and its level-four
  specialization `exists_cwTotalWeightCanonicalInnerSequenceData_levelFour`.

Two further declarations are genuinely new rather than restatements:
`CanonicalInnerSequenceData.ofVolumeBase_le`, the only adapter between the endpoint's base-two
volume convention and the exact leafwise dimension product; and
`exists_subexponentialLaserVolumeSequence_levelFourInner`, which checks end to end that the
produced datum flattens through `toSubexponentialLaserVolumeSequence_addRetained`.

The one *numerical* change is the characteristic floor.  The depth-one field needs characteristic
at least `9 = 3 ^ 2`; the depth-`d` field needs at least `cwChunkAlphabetSize d = 3 ^ 2 ^ d`, which
is `3 ^ 16 = 43046721` at depth four.  This is a constant, so `PrimeFieldSizing.loss` absorbs it
and no exponential rate changes: `cwTotalWeightInnerCompetitorBase` and
`cwTotalWeightInnerTargetBase` are literally the depth-generic ones already in use.
-/

namespace AlgebraicComplexity.Examples

open scoped BigOperators
open AlgebraicComplexity Tensor

universe u v w x

/-! ## The depth-generic constructor -/

/-- Depth-generic form of `exists_cwTotalWeightCanonicalInnerSequenceData`.

The proof is the depth-one one verbatim: every step is parametric in `depth`, once the base-three
chunk hash encoding above replaces the level-two one.  In particular the coarse-word transport
`cwTotalWeightLocalizedFineTypes_isomorphic_of_length_cast`, the fixed-coarse-type invariant, and
the fine marginal type all already carry `depth`. -/
theorem exists_cwTotalWeightCanonicalInnerSequenceData_ofDepth
    {K : Type u} [CommRing K] {q depth : ℕ}
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source} {stride : ℕ} {outerBase : ℝ}
    (outer : CWTotalWeightLocalizedOuterSequenceData.{u, v, w}
      K q depth T stride outerBase)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q depth support c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (growth : CWTotalWeightInnerGrowthDataAtDepth K q depth leaf.profile.count
      ambientBase ambientLoss)
    (hn : ∀ r, outer.n r = growth.exponent r)
    (hfine : ∀ r, outer.fineType r =
      cwTotalWeightFineMarginalType K q depth
        (WordType.proportionalCounts leaf.profile.count r))
    (hcoarseWordType : ∀ r i,
      WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) (outer.n r)
            (outer.coarseWord r i)) =
        WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) (outer.n r)
            (positiveWordCast (hn r).symm (growth.coarseWord r))))
    {δ W : ℝ} (hδ : 1 < δ) (hW : 0 < W)
    (hWrate : W < cwTotalWeightInnerTargetBase K q depth leaf.profile.count /
      (δ * cwTotalWeightInnerCompetitorBase K q depth leaf.profile.count ambientBase)) :
    Nonempty
      (CWTotalWeightLocalizedOuterSequenceData.CanonicalInnerSequenceData.{u, v, w, 0}
        outer W
          ((leaf.dimensionProduct .X * leaf.dimensionProduct .Y *
            leaf.dimensionProduct .Z : ℕ) : ℝ)) := by
  letI : Nonempty (cwChunkPartitionedTensor K q depth).support :=
    ⟨cwChunkSupportWitness K q depth⟩
  obtain ⟨innerLoss, hinnerLoss, hinnerLossPos, hinnerGrowth⟩ :=
    growth.exists_subexponentialLoss_pow_le_behrendCopies
      leaf hdimension hδ hW hWrate
  let reference : ∀ r,
      PositiveWord (CWTotalWeightCoarseSupport K q depth) (outer.n r) :=
    fun r ↦ positiveWordCast (hn r).symm (growth.coarseWord r)
  let coarseType : ℕ → CWTotalWeightCoarseSupport K q depth → ℕ :=
    fun r ↦ WordType.multiplicity
      (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) (outer.n r)
        (reference r))
  let innerCount : ℕ → ℕ := fun r ↦
    cwTotalWeightInnerBehrendCopiesAtDepth K q depth leaf hdimension
      (growth.exponent r) r (growth.coarseWord r)
  let J : ℕ → Type 0 := fun r ↦
    {a // a ∈ CWTotalWeightInnerBehrendIndexAtDepth K q depth leaf hdimension
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
      card_cwTotalWeightInnerBehrendIndexAtDepth K q depth leaf hdimension
        (growth.exponent r) r (growth.coarseWord r)
  · intro r hr
    simp only [hfine r]
    have htransport :=
      cwTotalWeightLocalizedFineTypes_isomorphic_of_length_cast
        K q depth (hn r).symm (growth.coarseWord r)
        (cwTotalWeightFineMarginalType K q depth
          (WordType.proportionalCounts leaf.profile.count r))
    have hcanonical :=
      cwTotalWeightInnerBehrend_degeneratesAtDepth
        K q depth leaf hdimension (growth.exponent r) r (growth.coarseWord r)
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

/-- Level-four specialization with the exact parameters of the nested endpoint chain: `q = 5`,
`depth = 4`, stride `38`.

Instantiating `T := Tensor.power (coppersmithWinograd K 5) 8` gives literally the
`CanonicalInnerSequenceData` consumed by
`CanonicalInnerSequenceData.toSubexponentialLaserVolumeSequence_addRetained` and hence by
`MatrixMultiplication.TotalWeightLeanEndpoint.omega_lt_236999_of_nestedSequenceData`. -/
theorem exists_cwTotalWeightCanonicalInnerSequenceData_levelFour
    {K : Type u} [CommRing K]
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source} {outerBase : ℝ}
    (outer : CWTotalWeightLocalizedOuterSequenceData.{u, v, w}
      K 5 4 T 38 outerBase)
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
    {δ W : ℝ} (hδ : 1 < δ) (hW : 0 < W)
    (hWrate : W < cwTotalWeightInnerTargetBase K 5 4 leaf.profile.count /
      (δ * cwTotalWeightInnerCompetitorBase K 5 4 leaf.profile.count ambientBase)) :
    Nonempty
      (CWTotalWeightLocalizedOuterSequenceData.CanonicalInnerSequenceData.{u, v, w, 0}
        outer W
          ((leaf.dimensionProduct .X * leaf.dimensionProduct .Y *
            leaf.dimensionProduct .Z : ℕ) : ℝ)) :=
  exists_cwTotalWeightCanonicalInnerSequenceData_ofDepth outer leaf hdimension growth
    hn hfine hcoarseWordType hδ hW hWrate

/-! ## Feeding the level-four endpoint chain -/

namespace CWTotalWeightLocalizedOuterSequenceData

namespace CanonicalInnerSequenceData

/-- Weaken the recorded rectangular-volume base of a canonical inner sequence.

The endpoint chain states its volume input in the base-two form `2 ^ (3 * stride * volume)`, while
the canonical inner constructor produces the exact leafwise dimension product.  This is the only
adapter needed between the two, and it loses nothing: `volume_growth` is a lower bound. -/
noncomputable def ofVolumeBase_le
    {K : Type u} [CommRing K] {q depth : ℕ}
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source} {stride : ℕ}
    {outerBase innerBase volumeBase volumeBase' : ℝ}
    {outer : CWTotalWeightLocalizedOuterSequenceData.{u, v, w}
      K q depth T stride outerBase}
    (data : CanonicalInnerSequenceData.{u, v, w, x} outer innerBase volumeBase)
    (hpos : 0 < volumeBase') (hle : volumeBase' ≤ volumeBase) :
    CanonicalInnerSequenceData.{u, v, w, x} outer innerBase volumeBase' :=
  { data with
    volumeBase_pos := hpos
    volume_growth := fun r hr ↦
      le_trans (pow_le_pow_left₀ hpos.le hle r) (data.volume_growth r hr) }

end CanonicalInnerSequenceData

end CWTotalWeightLocalizedOuterSequenceData

/-- End-to-end check that the depth-four inner datum is exactly what the nested endpoint consumes:
with the base-two retained-exponent shape on both sides and stride `38`, the canonical inner
extraction flattens through
`CanonicalInnerSequenceData.toSubexponentialLaserVolumeSequence_addRetained` and the two retained
exponents add.

This is the statement `MatrixMultiplication.TotalWeightLeanEndpoint.omega_lt_236999_of_nestedSequenceData`
consumes, with `T := Tensor.power (coppersmithWinograd K 5) 8`; see
`exists_subexponentialLaserVolumeSequence_levelFourInner_cw5`. -/
theorem exists_subexponentialLaserVolumeSequence_levelFourInner
    {K : Type u} [CommRing K]
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source} {outerRetained innerRetained : ℝ}
    (outer : CWTotalWeightLocalizedOuterSequenceData.{u, v, w}
      K 5 4 T 38 ((2 : ℝ) ^ (((38 : ℕ) : ℝ) * outerRetained)))
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
    (hWrate : (2 : ℝ) ^ (((38 : ℕ) : ℝ) * innerRetained) <
      cwTotalWeightInnerTargetBase K 5 4 leaf.profile.count /
        (δ * cwTotalWeightInnerCompetitorBase K 5 4 leaf.profile.count ambientBase)) :
    Nonempty
      (SubexponentialLaserVolumeSequence K T 38
        ((2 : ℝ) ^ (((38 : ℕ) : ℝ) * (outerRetained + innerRetained)))
        ((leaf.dimensionProduct .X * leaf.dimensionProduct .Y *
          leaf.dimensionProduct .Z : ℕ) : ℝ)) := by
  obtain ⟨inner⟩ :=
    exists_cwTotalWeightCanonicalInnerSequenceData_levelFour outer leaf hdimension growth
      hn hfine hcoarseWordType hδ
      (Real.rpow_pos_of_pos (by norm_num) _) hWrate
  exact ⟨inner.toSubexponentialLaserVolumeSequence_addRetained⟩

/-- The same statement with the endpoint's literal source tensor
`Tensor.power (coppersmithWinograd K 5) 8`. -/
theorem exists_subexponentialLaserVolumeSequence_levelFourInner_cw5
    {K : Type u} [CommRing K] {outerRetained innerRetained : ℝ}
    (outer : CWTotalWeightLocalizedOuterSequenceData.{u, u, w}
      K 5 4 (Tensor.power (coppersmithWinograd K 5) 8) 38
        ((2 : ℝ) ^ (((38 : ℕ) : ℝ) * outerRetained)))
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
    (hWrate : (2 : ℝ) ^ (((38 : ℕ) : ℝ) * innerRetained) <
      cwTotalWeightInnerTargetBase K 5 4 leaf.profile.count /
        (δ * cwTotalWeightInnerCompetitorBase K 5 4 leaf.profile.count ambientBase)) :
    Nonempty
      (SubexponentialLaserVolumeSequence K
        (Tensor.power (coppersmithWinograd K 5) 8) 38
        ((2 : ℝ) ^ (((38 : ℕ) : ℝ) * (outerRetained + innerRetained)))
        ((leaf.dimensionProduct .X * leaf.dimensionProduct .Y *
          leaf.dimensionProduct .Z : ℕ) : ℝ)) :=
  exists_subexponentialLaserVolumeSequence_levelFourInner outer leaf hdimension growth
    hn hfine hcoarseWordType hδ hWrate

end AlgebraicComplexity.Examples
