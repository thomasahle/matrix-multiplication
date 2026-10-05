/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroDimension
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientation
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationCoherentRestriction
import AlgebraicComplexity.MatrixMultiplication.PermutedSharedOneSliceFiber

/-!
# Exact zero-coordinate fusion of a CW interface term, in all three orientations

The committed `cwSelectedExactInterfaceTerm_zeroZ_restricts_fusedOneSlice` fuses the whole selected
support of an exact zero-`Z` interface term into one matrix-multiplication tensor
`⟨1, |S| q^e, 1⟩`, with no representative selection and no loss factor.  This module proves the
same statement with the zero coordinate on `X` and on `Y`, in the rotated frame.

## What the assembly consists of

The pieces were all landed separately, and this module only composes them:

* the **rotated coherent chain** of `CoppersmithWinogradZeroOrientationCoherentRestriction`, which
  ends at every supported zero-`zero` outer word of chunks;
* the **support law** `cwSelectedExactInterfaceTerm_zero_support_isSharedFiber` (items 1--2), which
  says the selected support is a shared fibre on the zero leg with injective labels on the two live
  legs;
* the **rotated-frame fusion**
  `CTensor.PermutedSharedOneSliceFiberData.restricts_permute_oneSliceMatrixMultiplication`, which
  is the committed `SharedOneSliceFiberData` fusion read through
  `PartitionedTensor.permute` and the items-1--2 support transport.

No coherence is re-proved and no new tensor law is used: the only genuinely new content is the
leg-indexed exponent bookkeeping of the first section.

## The exponent, read at the right leg

On a zero-`zero` fibre the surviving matrix dimension is `q ^ k` with `k` the middle-digit count of
the encoded chunk word at `firstLiveLeg zero`.  `cwZeroInterfaceQExponentOn c term` is the committed
`cwZeroInterfaceQExponent` with its leg made an argument, and the committed one is the instance
`c = .X = firstLiveLeg .Z`.  Carrying the leg in the statement is the discipline of the whole
zero-orientation tranche: a client cannot pair a zero-`X` interface with a zero-`Y` exponent.

## Honest gap

This module moves no certificate inequality and proves nothing asymptotic.  In particular the
cardinality `|S|` of the selected support is *not* estimated here — that is the quantitative
successor tranche (codex-2.36x's `0cf5dca` and its method-of-types corollary), and the merged-leaf
adapter that consumes both is `MergedLeafClassFactor`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

/-! ## The exact interface exponent, at an arbitrary leg -/

/-- The exact exponent of `q` contributed by a zero-coordinate recursive interface term, read at
leg `c`.  The committed `cwZeroInterfaceQExponent` is the instance `c = .X`. -/
def cwZeroInterfaceQExponentOn (c : Leg) {depth : ℕ}
    (term : ExactInterfaceTermParameters depth) : ℕ :=
  ∑ word, (term.split c).counts word * splitWordMiddleCount word

@[simp] theorem cwZeroInterfaceQExponentOn_X {depth : ℕ}
    (term : ExactInterfaceTermParameters depth) :
    cwZeroInterfaceQExponentOn .X term = cwZeroInterfaceQExponent term := rfl

private theorem positivePowerProfile_counts_aux {depth : ℕ}
    (index : LevelConstituentIndex depth) (multiplicity n : ℕ)
    (split : ∀ c, CompleteSplitProfile depth (index.count c) multiplicity)
    (hmultiplicity : multiplicity = n + 1) (c : Leg) :
    ((ExactInterfaceTermParameters.mk multiplicity index split).positivePowerProfile
      hmultiplicity c).counts = (split c).counts := by
  subst hmultiplicity
  rfl

private theorem positivePowerProfile_counts
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (c : Leg) :
    (term.positivePowerProfile hmultiplicity c).counts = (term.split c).counts :=
  positivePowerProfile_counts_aux term.index term.multiplicity n term.split hmultiplicity c

variable (K : Type u) [CommRing K] (q : ℕ)

/-- The encoded chunk sequence of the recovered supported outer word realizes the exact stored
profile on leg `c`.  This is the committed `_x_isConsistent` with its leg made an argument; the
selection law it reads is already leg-quantified. -/
theorem cwSelectedExactInterfaceSupportedWord_isConsistent
    (c : Leg) {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (address : (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    (term.positivePowerProfile hmultiplicity c).IsConsistent
      (fun position ↦ cwChunkSplitWord depth
        ((positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n
          (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address)
            position).1 c)) := by
  have hselected := address.2
  change address.1 ∈
    ((cwChunkPartitionedTensor K q depth).selectEncodedCompleteSplitProfiles
      (fun _c ↦ cwChunkSplitWord depth) term.index
      (fun c ↦ term.positivePowerProfile hmultiplicity c)).support at hselected
  have hconsistent :=
    ((cwChunkPartitionedTensor K q depth).mem_selectEncodedCompleteSplitProfiles_support
      (fun _c ↦ cwChunkSplitWord depth) term.index
      (fun c ↦ term.positivePowerProfile hmultiplicity c) address.1).mp hselected |>.2 c
  have haddress := positiveSupportWordBlockAddress_cwSelectedExactInterfaceSupportedWord
    K q term hmultiplicity address
  have hwords := congrArg
    (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n)
    (congrFun haddress c)
  unfold CompleteSplitProfile.IsConsistent at hconsistent ⊢
  have hsequence :
      (fun position ↦ cwChunkSplitWord depth
        ((positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n
          (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address)
            position).1 c)) =
        (cwChunkSplitWord depth ∘ positiveWordEquiv
          (PositiveWord CWBlock (2 ^ depth - 1)) n (address.1 c)) := by
    funext position
    rw [Function.comp_apply]
    congr 1
    have hposition := congrFun hwords position
    calc
      (positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n
          (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address) position).1 c =
          positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
            (positiveSupportWordBlockAddress
              (cwChunkPartitionedTensor K q depth).support n
              (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address) c)
              position :=
        (congrFun (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
          (cwChunkPartitionedTensor K q depth).support n
          (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address) c)
          position).symm
      _ = positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
          (address.1 c) position := hposition
  rw [hsequence]
  exact hconsistent

/-- Exact complete-split consistency fixes the total middle-digit count of every selected outer
constituent on leg `c`.  The committed statement is the instance `c = .X`. -/
theorem cwSelectedExactInterfaceSupportedWord_sum_middleCount_on
    (c : Leg) {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (address : (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    ∑ position, splitWordMiddleCount
        (cwChunkSplitWord depth
          ((positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n
            (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address)
              position).1 c)) =
      cwZeroInterfaceQExponentOn c term := by
  have h := (term.positivePowerProfile hmultiplicity c).sum_middleCount_of_isConsistent
    _ (cwSelectedExactInterfaceSupportedWord_isConsistent K q c term hmultiplicity address)
  simpa only [positivePowerProfile_counts, cwZeroInterfaceQExponentOn] using h

/-! ## The rotated interface constituent -/

/-- **Every constituent of an exact zero-`zero` interface, rotated into the canonical shared-`Z`
frame, carries the canonical shared map** — not merely a proposition-level restriction to a
one-slice matrix tensor.  This is the last level of the rotated coherent chain. -/
noncomputable def cwSelectedExactInterfaceConstituentRotatedCoherentRestriction
    (zero : Leg) {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hzero : term.index.count zero = 0)
    (address : (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation zero)
          ((cwSelectedExactInterfaceTerm K q term hmultiplicity).constituent address.1))
        (q ^ cwZeroInterfaceQExponentOn (firstLiveLeg zero) term) //
      HEq (C.legMap .Z) (cwZeroInterfaceRotatedCanonicalZMap K q zero depth n) } := by
  let outerWord := cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address
  have haddress := positiveSupportWordBlockAddress_cwSelectedExactInterfaceSupportedWord
    K q term hmultiplicity address
  have hshared :=
    (cwSelectedExactInterfaceTerm_zero_support_isSharedFiber
      K q term hmultiplicity zero hzero).1 address.1 address.2
  have hzeroWords :
      positiveSupportWordBlockAddress (cwChunkPartitionedTensor K q depth).support n
          outerWord zero = positiveWordConst (cwZeroChunkWord depth) n := by
    rw [haddress]
    exact hshared
  let data := cwZeroChunkOuterWordRotatedCoherentRestriction K q zero depth n outerWord hzeroWords
  have hdimension :
      positiveWordProduct
          (fun support : (cwChunkPartitionedTensor K q depth).support ↦
            q ^ splitWordMiddleCount
              (cwChunkSplitWord depth (support.1 (firstLiveLeg zero)))) n outerWord =
        q ^ cwZeroInterfaceQExponentOn (firstLiveLeg zero) term := by
    rw [positiveWordProduct_eq_fin_prod, Finset.prod_pow_eq_pow_sum,
      cwSelectedExactInterfaceSupportedWord_sum_middleCount_on
        K q (firstLiveLeg zero) term hmultiplicity address]
  let dataDimension :
      { C : OneSliceRestriction
          (Tensor.permute (K := K) (zeroOrientation zero)
            ((cwChunkPartitionedTensor K q depth).positiveSupportWordTensor n outerWord))
          (q ^ cwZeroInterfaceQExponentOn (firstLiveLeg zero) term) //
        HEq (C.legMap .Z) (cwZeroInterfaceRotatedCanonicalZMap K q zero depth n) } := by
    rw [← hdimension]
    exact data
  have hconst :=
    (cwChunkPartitionedTensor K q depth).positivePower_constituent_positiveSupportWordBlockAddress
      n outerWord
  let dataConstituent :
      { C : OneSliceRestriction
          (Tensor.permute (K := K) (zeroOrientation zero)
            (((cwChunkPartitionedTensor K q depth).positivePower n).constituent
              (positiveSupportWordBlockAddress
                (cwChunkPartitionedTensor K q depth).support n outerWord)))
          (q ^ cwZeroInterfaceQExponentOn (firstLiveLeg zero) term) //
        HEq (C.legMap .Z) (cwZeroInterfaceRotatedCanonicalZMap K q zero depth n) } := by
    rw [hconst]
    exact dataDimension
  change
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation zero)
          (((cwChunkPartitionedTensor K q depth).positivePower n).constituent address.1))
        (q ^ cwZeroInterfaceQExponentOn (firstLiveLeg zero) term) //
      HEq (C.legMap .Z) (cwZeroInterfaceRotatedCanonicalZMap K q zero depth n) }
  rw [← haddress]
  exact dataConstituent

/-! ## The shared-fibre datum, and the fusion -/

/-- The complete exact zero-`zero` support, equipped with coherent rotated constituent maps for the
generic rotated shared-fibre fusion. -/
noncomputable def cwSelectedExactInterfaceTerm_zero_permutedSharedOneSliceData
    (zero : Leg) {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hzero : term.index.count zero = 0) :
    CTensor.PermutedSharedOneSliceFiberData
      (cwSelectedExactInterfaceTerm K q term hmultiplicity)
      (zeroOrientation zero)
      (cwZeroInterfaceLegWord depth n)
      (q ^ cwZeroInterfaceQExponentOn (firstLiveLeg zero) term) where
  certificate := fun address ↦
    (cwSelectedExactInterfaceConstituentRotatedCoherentRestriction
      K q zero term hmultiplicity hzero address).1
  zMap := cwZeroInterfaceRotatedCanonicalZMap K q zero depth n
  z_coherent := fun address ↦
    (cwSelectedExactInterfaceConstituentRotatedCoherentRestriction
      K q zero term hmultiplicity hzero address).2

/-- **Exact zero-coordinate fusion, in every orientation.**  The entire selected interface of a term
whose `zero` coordinate vanishes, rotated into the canonical frame, restricts to
`⟨1, |support| q^e, 1⟩` — with no representative selection, no loss factor and no cardinality
estimate.  The shared map is constructed explicitly by the rotated coherent chain.

At `zero = .Z` this is the committed
`cwSelectedExactInterfaceTerm_zeroZ_restricts_fusedOneSlice` with an inert `Tensor.permute 1`. -/
theorem cwSelectedExactInterfaceTerm_zero_restricts_fusedOneSlice
    (zero : Leg) {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hzero : term.index.count zero = 0) :
    Restricts
      (Tensor.permute (zeroOrientation zero)
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize)
      (matrixMultiplication (K := K) 1
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card *
          q ^ cwZeroInterfaceQExponentOn (firstLiveLeg zero) term) 1) := by
  have hsupport := cwSelectedExactInterfaceTerm_zero_support_isSharedFiber
    K q term hmultiplicity zero hzero
  refine (cwSelectedExactInterfaceTerm_zero_permutedSharedOneSliceData
    K q zero term hmultiplicity hzero).restricts_permute_oneSliceMatrixMultiplication
      ?_ ?_ ?_
  -- `zeroOrientation zero` is a match on the zero leg, so `(zeroOrientation zero).symm .X` and
  -- `firstLiveLeg zero` are equal but not definitionally so; and the label `address c` is a
  -- dependent application, whose type moves with `c`, so `simp` cannot rewrite under it.  Splitting
  -- the three legs makes each identification a reduction.
  · cases zero <;> exact hsupport.2.1
  · cases zero <;> exact hsupport.2.2
  · cases zero <;> exact hsupport.1

/-- The zero-`X` instance: the rotated interface restricts to `⟨1, |S| q^e, 1⟩` with the exponent
read from the `Y` profile. -/
theorem cwSelectedExactInterfaceTerm_zeroX_restricts_fusedOneSlice
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hx : term.index.count .X = 0) :
    Restricts
      (Tensor.permute Tensor.cycle.symm
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize)
      (matrixMultiplication (K := K) 1
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card *
          q ^ cwZeroInterfaceQExponentOn .Y term) 1) :=
  cwSelectedExactInterfaceTerm_zero_restricts_fusedOneSlice K q .X term hmultiplicity hx

/-- The zero-`Y` instance: the rotated interface restricts to `⟨1, |S| q^e, 1⟩` with the exponent
read from the `Z` profile. -/
theorem cwSelectedExactInterfaceTerm_zeroY_restricts_fusedOneSlice
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hy : term.index.count .Y = 0) :
    Restricts
      (Tensor.permute Tensor.cycle
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize)
      (matrixMultiplication (K := K) 1
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card *
          q ^ cwZeroInterfaceQExponentOn .Z term) 1) :=
  cwSelectedExactInterfaceTerm_zero_restricts_fusedOneSlice K q .Y term hmultiplicity hy

/-- The zero-`Z` instance, at the identity rotation, with the committed exponent.  The committed
`cwSelectedExactInterfaceTerm_zeroZ_restricts_fusedOneSlice` is this statement without the inert
`Tensor.permute 1`; it is untouched, and this one certifies that the orientation-indexed fusion
really does subsume it. -/
theorem cwSelectedExactInterfaceTerm_zeroZ_restricts_rotatedFusedOneSlice
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0) :
    Restricts
      (Tensor.permute (1 : Orientation)
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize)
      (matrixMultiplication (K := K) 1
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card *
          q ^ cwZeroInterfaceQExponent term) 1) :=
  cwSelectedExactInterfaceTerm_zero_restricts_fusedOneSlice K q .Z term hmultiplicity hz

end AlgebraicComplexity.Examples
