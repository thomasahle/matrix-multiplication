/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationOneSlice
import AlgebraicComplexity.MatrixMultiplication.PermutedCoherentOneSliceWord

/-!
# Exact zero-coordinate fusion of a Coppersmith--Winograd interface, in every orientation

`CoppersmithWinogradZeroCoherentRestriction` fuses the whole selected support of an exact zero-`Z`
interface term into a single one-slice matrix-multiplication tensor `⟨1, |S| q^e, 1⟩`, with no
representative selection and no loss factor.  A laser certificate meets zero blocks in all three
orientations, so the same fusion is needed with the zero on `X` and on `Y`.

This module supplies it, once, indexed by the zero leg.

## What is transported and what is re-run

* The **base certificates** are the six choice-free zero-`X` / zero-`Y` certificates of
  `CoppersmithWinogradZeroOrientationOneSliceBase`, which are transports of the committed zero-`Z`
  ones along the base cyclic symmetry.  Their shared map is the committed
  `cwZeroBaseCanonicalZMap`, unchanged: `CWPartitionBlockSpace` does not depend on the leg, and
  `OneSliceRestriction.precompose_legMap` computes the transported map, so the coherence is not
  re-proved in coordinates in either orientation.
* The **word, chunk and interface iterations** are re-run in the rotated frame, but through the
  *generic* coherent recursion `OneSliceRestriction.permutedCoherentWord`, not by repeating the
  dependent bookkeeping.  The committed zero-`Z` chain runs the same recursion twice by hand; the
  generic form covers both levels in all three orientations.
* The **dimension bookkeeping** is the committed leg-indexed one from
  `CoppersmithWinogradZeroOrientationOneSlice`.

## The exponent, read at the right leg

On a zero-`zero` fibre the surviving matrix dimension is `q ^ k` with `k` the middle-digit count of
the encoded word at `firstLiveLeg zero`.  So the interface exponent is
`cwZeroInterfaceQExponentOn (firstLiveLeg zero) term`, which at `zero = .Z` is the committed
`cwZeroInterfaceQExponent term` verbatim (`firstLiveLeg .Z = .X`).  Carrying the leg in the name is
the same discipline as the rest of the zero-orientation tranche: a client cannot pair a zero-`X`
interface with a zero-`Y` exponent.

## The conclusion stays in the permuted frame

Every restriction below is a restriction of `Tensor.permute (zeroOrientation zero) …`, with the
rotation named in the statement, exactly as the ratified items-1--2 design decision requires.
Rotating back is an isomorphism and belongs with the leaf packaging, beside
`ZeroCoordinateMerge.mergeX / mergeY / mergeZ`.

The interface level — the selected exact interface term, its shared-fibre datum and the three
orientation fusion theorems — is the companion module
`CoppersmithWinogradZeroOrientationFusion`.  The two are separate because the whole cone is
import-heavy: the committed `CoppersmithWinogradSquareSymmetry` that the rotated base needs costs
2,224 MB of olean load on its own, so each elaboration here is kept to one layer.

Nothing here is asymptotic: every statement is a finite exact equality or an exact restriction, and
no type-class cardinality estimate is used or assumed.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

variable (K : Type u) [CommRing K] (q : ℕ)

/-- Canonical map on the zero block of one base CW constituent, in any frame.

This is definitionally the committed `cwZeroBaseCanonicalZMap` of
`CoppersmithWinogradZeroCoherentRestriction` — both are `cw200OneSliceMap K q .Z`, and
`cwZeroBaseOneSliceMap_Z_coherent` is `rfl`, so the zero-`X` and zero-`Y` families share the
zero-`Z` family's map and not merely an isomorphic one.  It is restated here rather than imported
because the committed home of that abbreviation drags the whole zero-`Z` interface chain into this
module's import closure, at a measured 1.7 GB of olean load; the audit client records the
identification.

`CWPartitionBlockSpace` does not depend on the tensor leg, so this one map types correctly on the
shared block in all three orientations. -/
def cwZeroBaseRotatedCanonicalZMap :
    CWPartitionBlockSpace K q .Z .zero →ₗ[K] MMSpace K 1 1 1 .Z :=
  cw200OneSliceMap K q .Z

/-- The maps of an identity-rotation transport are the transported certificate's own maps.  Unlike
the two genuine rotations, `Tensor.permute 1` is only propositionally the identity, so this one step
is a rewrite rather than a reduction. -/
private theorem cwRotatedBaseOfRefl_legMap (x y z : CWBlock) {d : ℕ}
    (C : OneSliceRestriction (cwConstituentOfBlocks K q x y z) d) (c : Leg) :
    (cwRotatedBaseOfRefl K q x y z C).legMap c = C.legMap c := by
  have houter := OneSliceRestriction.congrTensor_legMap
    (C.congrTensor (cwPartitionConstituent_ofLegs K q x y z).symm)
    (Tensor.permute_one (K := K)
      (cwPartitionConstituent K q (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z))).symm c
  have hinner := OneSliceRestriction.congrTensor_legMap C
    (cwPartitionConstituent_ofLegs K q x y z).symm c
  exact houter.trans hinner

/-! ## The rotated base, with its shared map retained -/

/-- **Every supported base CW constituent with a zero at leg `zero`, read in the frame that rotates
`zero` onto `.Z`, has an explicit one-slice restriction that uses the committed canonical map on the
shared block.**

The certificate itself is one of the six choice-free transports of
`CoppersmithWinogradZeroOrientationOneSliceBase`; what is added here is the retained coherence,
which is what the shared-fibre fusion consumes.  At `zero = .Z` this is the committed
`cwZeroBaseCoherentRestriction` with an inert `Tensor.permute 1` in front. -/
noncomputable def cwZeroBaseRotatedCoherentRestriction
    (zero : Leg) (support : cwBlockSupport) (hzero : support.1 zero = .zero) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation zero) (cwSupportedConstituent K q support))
        (cwBaseConstituentDimension q support (secondLiveLeg zero)) //
      HEq (C.legMap .Z) (cwZeroBaseRotatedCanonicalZMap K q) } := by
  classical
  refine Classical.choice ?_
  rcases support with ⟨address, haddress⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  cases zero
  · rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [cw200, cwBlockAddress] at hzero
    · exact ⟨⟨cw020ZeroXOneSliceRestriction K q, HEq.rfl⟩⟩
    · exact ⟨⟨cw002ZeroXOneSliceRestriction K q, HEq.rfl⟩⟩
    · exact ⟨⟨cw011ZeroXOneSliceRestriction K q, HEq.rfl⟩⟩
    · simp [cw101, cwBlockAddress] at hzero
    · simp [cw110, cwBlockAddress] at hzero
  · rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨cw200ZeroYOneSliceRestriction K q, HEq.rfl⟩⟩
    · simp [cw020, cwBlockAddress] at hzero
    · exact ⟨⟨cw002ZeroYOneSliceRestriction K q, HEq.rfl⟩⟩
    · simp [cw011, cwBlockAddress] at hzero
    · exact ⟨⟨cw101ZeroYOneSliceRestriction K q, HEq.rfl⟩⟩
    · simp [cw110, cwBlockAddress] at hzero
  · rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨cwRotatedBaseOfRefl K q .last .zero .zero (cw200OneSliceRestriction K q),
        heq_of_eq (cwRotatedBaseOfRefl_legMap K q .last .zero .zero
          (cw200OneSliceRestriction K q) .Z)⟩⟩
    · exact ⟨⟨cwRotatedBaseOfRefl K q .zero .last .zero (cw020OneSliceRestriction K q),
        heq_of_eq (cwRotatedBaseOfRefl_legMap K q .zero .last .zero
          (cw020OneSliceRestriction K q) .Z)⟩⟩
    · simp [cw002, cwBlockAddress] at hzero
    · simp [cw011, cwBlockAddress] at hzero
    · simp [cw101, cwBlockAddress] at hzero
    · exact ⟨⟨cwRotatedBaseOfRefl K q .middle .middle .zero (cw110OneSliceRestriction K q),
        heq_of_eq (cwRotatedBaseOfRefl_legMap K q .middle .middle .zero
          (cw110OneSliceRestriction K q) .Z)⟩⟩

/-! ## The rotated base word -/

/-- Canonical shared map of a rotated supported zero-`zero` base word. -/
noncomputable def cwZeroBaseRotatedWordCanonicalZMap (zero : Leg) (r : ℕ) :
    PositivePowerBlockSpace K (CWPartitionBlockSpace K q) r
        ((zeroOrientation zero).symm .Z) (positiveWordConst .zero r) →ₗ[K] MMSpace K 1 1 1 .Z :=
  OneSliceRestriction.constWordZMap (A := fun _ : Leg ↦ CWBlock)
    (V := CWPartitionBlockSpace K q) ((zeroOrientation zero).symm .Z)
    (zLabel := CWBlock.zero) (cwZeroBaseRotatedCanonicalZMap K q) r

/-- Coherent rotated certificate for an arbitrary supported positive word on the zero-`zero` base
fibre.  This is the generic recursion, instantiated once. -/
noncomputable def cwZeroBaseRotatedWordCoherentRestriction
    (zero : Leg) (r : ℕ) (word : PositiveWord cwBlockSupport r)
    (hzero : positiveSupportWordBlockAddress cwBlockSupport r word zero =
      positiveWordConst .zero r) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation zero)
          ((cwPartitionedTensor K q).positiveSupportWordTensor r word))
        (positiveWordProduct
          (fun support ↦ cwBaseConstituentDimension q support (secondLiveLeg zero)) r word) //
      HEq (C.legMap .Z) (cwZeroBaseRotatedWordCanonicalZMap K q zero r) } :=
  OneSliceRestriction.permutedCoherentWord (cwPartitionedTensor K q)
    (fun support ↦ cwBaseConstituentDimension q support (secondLiveLeg zero))
    (zeroOrientation zero) (zLabel := CWBlock.zero) (cwZeroBaseRotatedCanonicalZMap K q)
    (fun support hsupport ↦
      cwZeroBaseRotatedCoherentRestriction K q zero support
        (by rw [zeroOrientation_symm_Z] at hsupport; exact hsupport))
    r word (by rw [zeroOrientation_symm_Z]; exact hzero)

/-! ## The rotated chunk -/

/-- Canonical shared map of a rotated zero-`zero` recursive chunk. -/
noncomputable def cwZeroChunkRotatedCanonicalZMap (zero : Leg) (depth : ℕ) :
    PositivePowerBlockSpace K (CWPartitionBlockSpace K q) (2 ^ depth - 1)
        ((zeroOrientation zero).symm .Z) (cwZeroChunkWord depth) →ₗ[K] MMSpace K 1 1 1 .Z :=
  cwZeroBaseRotatedWordCanonicalZMap K q zero (2 ^ depth - 1)

/-- **Coherent rotated certificate for every supported zero-`zero` recursive chunk.**  The
certificate is the one item 3 landed; the shared map it uses is now retained. -/
noncomputable def cwZeroChunkRotatedCoherentRestriction
    (zero : Leg) (depth : ℕ)
    (support : (cwChunkPartitionedTensor K q depth).support)
    (hzero : support.1 zero = cwZeroChunkWord depth) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation zero)
          ((cwChunkPartitionedTensor K q depth).constituent support.1))
        (q ^ splitWordMiddleCount
          (cwChunkSplitWord depth (support.1 (firstLiveLeg zero)))) //
      HEq (C.legMap .Z) (cwZeroChunkRotatedCanonicalZMap K q zero depth) } := by
  let word : PositiveWord cwBlockSupport (2 ^ depth - 1) := by
    simpa only [cwPartitionedTensor] using
      (cwChunkSupportedWordOfAddress K q depth support)
  have haddress := positiveSupportWordBlockAddress_cwChunkSupportedWordOfAddress
    K q depth support
  have haddress' :
      positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word = support.1 := by
    simpa only [word, cwPartitionedTensor] using haddress
  have hzeroWord :
      positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word zero =
        positiveWordConst .zero (2 ^ depth - 1) := by
    rw [haddress', hzero]
    rfl
  let data := cwZeroBaseRotatedWordCoherentRestriction K q zero (2 ^ depth - 1) word hzeroWord
  have hdimensionWord :
      positiveWordProduct
          (fun base ↦ cwBaseConstituentDimension q base (secondLiveLeg zero))
          (2 ^ depth - 1) word =
        q ^ splitWordMiddleCount
          (cwChunkSplitWord depth
            (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word
              (firstLiveLeg zero))) := by
    rw [positiveWordProduct_cwBaseDimension_secondLiveLeg_eq_pow_middleCount_of_eq_const
      q zero _ word hzeroWord]
    congr 1
    rw [← splitWordMiddleCount_cwChunkSplitWord_positiveSupportWordBlockAddress_leg
      (firstLiveLeg zero) depth word]
  let dataDimension :
      { C : OneSliceRestriction
          (Tensor.permute (K := K) (zeroOrientation zero)
            ((cwPartitionedTensor K q).positiveSupportWordTensor (2 ^ depth - 1) word))
          (q ^ splitWordMiddleCount
            (cwChunkSplitWord depth
              (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word
                (firstLiveLeg zero)))) //
        HEq (C.legMap .Z) (cwZeroChunkRotatedCanonicalZMap K q zero depth) } := by
    rw [← hdimensionWord]
    exact data
  have hconst :=
    (cwPartitionedTensor K q).positivePower_constituent_positiveSupportWordBlockAddress
      (2 ^ depth - 1) word
  change
    ((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).constituent
        (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word) =
      (cwPartitionedTensor K q).positiveSupportWordTensor (2 ^ depth - 1) word at hconst
  let dataConstituent :
      { C : OneSliceRestriction
          (Tensor.permute (K := K) (zeroOrientation zero)
            (((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).constituent
              (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word)))
          (q ^ splitWordMiddleCount
            (cwChunkSplitWord depth
              (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word
                (firstLiveLeg zero)))) //
        HEq (C.legMap .Z) (cwZeroChunkRotatedCanonicalZMap K q zero depth) } := by
    rw [hconst]
    exact dataDimension
  change
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation zero)
          (((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).constituent support.1))
        (q ^ splitWordMiddleCount
          (cwChunkSplitWord depth (support.1 (firstLiveLeg zero)))) //
      HEq (C.legMap .Z) (cwZeroChunkRotatedCanonicalZMap K q zero depth) }
  rw [← haddress']
  exact dataConstituent

/-! ## The rotated outer word -/

/-- Canonical shared map of a rotated supported zero-`zero` outer word of chunks. -/
noncomputable def cwZeroInterfaceRotatedCanonicalZMap (zero : Leg) (depth n : ℕ) :
    PositivePowerBlockSpace K
        (PositivePowerBlockSpace K (CWPartitionBlockSpace K q) (2 ^ depth - 1)) n
        ((zeroOrientation zero).symm .Z) (cwZeroInterfaceLegWord depth n) →ₗ[K]
      MMSpace K 1 1 1 .Z :=
  OneSliceRestriction.constWordZMap
    (A := fun _ : Leg ↦ PositiveWord CWBlock (2 ^ depth - 1))
    (V := PositivePowerBlockSpace K (CWPartitionBlockSpace K q) (2 ^ depth - 1))
    ((zeroOrientation zero).symm .Z)
    (zLabel := cwZeroChunkWord depth) (cwZeroChunkRotatedCanonicalZMap K q zero depth) n

/-- Coherent rotated certificate for every supported outer word in the zero-`zero` recursive
fibre.  The generic recursion again, one level up. -/
noncomputable def cwZeroChunkOuterWordRotatedCoherentRestriction
    (zero : Leg) (depth n : ℕ)
    (word : PositiveWord (cwChunkPartitionedTensor K q depth).support n)
    (hzero : positiveSupportWordBlockAddress
      (cwChunkPartitionedTensor K q depth).support n word zero =
        positiveWordConst (cwZeroChunkWord depth) n) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation zero)
          ((cwChunkPartitionedTensor K q depth).positiveSupportWordTensor n word))
        (positiveWordProduct
          (fun support ↦ q ^ splitWordMiddleCount
            (cwChunkSplitWord depth (support.1 (firstLiveLeg zero)))) n word) //
      HEq (C.legMap .Z) (cwZeroInterfaceRotatedCanonicalZMap K q zero depth n) } :=
  OneSliceRestriction.permutedCoherentWord (cwChunkPartitionedTensor K q depth)
    (fun support ↦ q ^ splitWordMiddleCount
      (cwChunkSplitWord depth (support.1 (firstLiveLeg zero))))
    (zeroOrientation zero) (zLabel := cwZeroChunkWord depth)
    (cwZeroChunkRotatedCanonicalZMap K q zero depth)
    (fun support hsupport ↦
      cwZeroChunkRotatedCoherentRestriction K q zero depth support
        (by rw [zeroOrientation_symm_Z] at hsupport; exact hsupport))
    n word (by rw [zeroOrientation_symm_Z]; exact hzero)

end AlgebraicComplexity.Examples
