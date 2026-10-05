/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationOneSliceBase
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroWord
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroWordDimension
import AlgebraicComplexity.MatrixMultiplication.OneSliceRestrictionTransport
import AlgebraicComplexity.Tensor.PartitionedPowerSupportDecodeCore

/-!
# Explicit one-slice maps for zero-`X` and zero-`Y` Coppersmith--Winograd chunks

`CoppersmithWinogradZeroOneSlice` iterates the committed zero-`Z` base certificates along a
supported zero-`Z` word and obtains an explicit one-slice restriction for every zero-`Z` recursive
chunk.  This module does the same in the two remaining orientations, in the rotated frame fixed by
`MoreAsymmetryCompatibility.zeroOrientation`.

## What is genuinely new here, and what is transported

* The **base certificates** are transports of the committed zero-`Z` ones
  (`CoppersmithWinogradZeroOrientationOneSliceBase`); nothing is re-proved in coordinates.
* The **word and chunk iterations** are re-run, not transported: they use the generic rotated
  recursion `OneSliceRestriction.ofPermutedPositivePowerConstituentData`, which is the unrotated
  recursion verbatim modulo `Tensor.permute_external`.
* The **dimension bookkeeping** *is* new, and it is the only arithmetic in the module.  On a
  zero-`zero` fibre the surviving matrix dimension sits at `secondLiveLeg zero` and equals `q`
  exactly when the block at `firstLiveLeg zero` is middle.  The committed statements are the
  instance `zero = .Z`, where those two legs are `.Y` and `.X`; the leg-indexed forms below carry
  the zero leg as an argument, so a client cannot pair a zero-`X` word with a zero-`Y` exponent.

## The exponent

For a zero-`zero` chunk the middle dimension is `q ^ splitWordMiddleCount (cwChunkSplitWord depth
(address (firstLiveLeg zero)))` — the same statistic the committed theorem reads off the `X` word,
now read off whichever leg the rotation puts there.  At `zero = .Z` this is literally the committed
exponent.

No asymptotic argument, no representative selection and no entropy estimate occurs here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

/-! ## Leg-indexed dimensions on a zero fibre -/

/-- On a zero-`zero` supported address the zero leg itself carries a unit matrix dimension. -/
theorem cwBaseConstituentDimension_zeroLeg_eq_one_of_eq_zero
    (q : ℕ) (zero : Leg) (support : cwBlockSupport) (hzero : support.1 zero = .zero) :
    cwBaseConstituentDimension q support zero = 1 := by
  rcases support with ⟨address, haddress⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases zero <;>
    simp_all [cwBaseConstituentDimension, cwBlockMatrixDimensions,
      cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress]

/-- On a zero-`zero` supported address the first live leg also carries a unit matrix dimension:
all of the constituent's rectangularity is concentrated on the second live leg. -/
theorem cwBaseConstituentDimension_firstLiveLeg_eq_one_of_eq_zero
    (q : ℕ) (zero : Leg) (support : cwBlockSupport) (hzero : support.1 zero = .zero) :
    cwBaseConstituentDimension q support (firstLiveLeg zero) = 1 := by
  rcases support with ⟨address, haddress⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases zero <;>
    simp_all [cwBaseConstituentDimension, cwBlockMatrixDimensions, firstLiveLeg,
      cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress]

/-- On a zero-`zero` supported address the second live leg carries `q` exactly at a middle block
on the first live leg, and `1` otherwise. -/
theorem cwBaseConstituentDimension_secondLiveLeg_eq_pow_middleIndicator_of_eq_zero
    (q : ℕ) (zero : Leg) (support : cwBlockSupport) (hzero : support.1 zero = .zero) :
    cwBaseConstituentDimension q support (secondLiveLeg zero) =
      q ^ (if cwBlockDigit (support.1 (firstLiveLeg zero)) = (1 : SplitDigit) then 1 else 0) := by
  rcases support with ⟨address, haddress⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases zero <;>
    simp_all [cwBaseConstituentDimension, cwBlockMatrixDimensions, firstLiveLeg, secondLiveLeg,
      cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress]

/-! ## Leg-indexed word statistics -/

/-- Number of middle blocks on leg `c` in a supported word of base CW addresses.  The committed
`cwSupportedWordXMiddleCount` is the instance `c = .X`. -/
def cwSupportedWordMiddleCount (c : Leg) (r : ℕ)
    (word : PositiveWord cwBlockSupport r) : ℕ :=
  ∑ position,
    if cwBlockDigit ((positiveWordEquiv cwBlockSupport r word position).1 c) =
        (1 : SplitDigit) then 1 else 0

@[simp] theorem cwSupportedWordMiddleCount_X (r : ℕ) (word : PositiveWord cwBlockSupport r) :
    cwSupportedWordMiddleCount .X r word = cwSupportedWordXMiddleCount r word :=
  rfl

/-- A constant-zero transposed word on leg `c` means every supported letter is zero on `c`.  This
is the committed `positiveSupportWord_letter_z_eq_zero_of_address_z_eq_const` with its leg made an
argument; the underlying recursion lemma was already leg-generic. -/
theorem positiveSupportWord_letter_eq_zero_of_address_eq_const
    (c : Leg) {r : ℕ} (word : PositiveWord cwBlockSupport r)
    (hzero : positiveSupportWordBlockAddress cwBlockSupport r word c =
      positiveWordConst .zero r) (position : Fin (r + 1)) :
    (positiveWordEquiv cwBlockSupport r word position).1 c = .zero := by
  have hzWords := congrArg (positiveWordEquiv CWBlock r) hzero
  have hzPosition := congrFun hzWords position
  calc
    (positiveWordEquiv cwBlockSupport r word position).1 c =
        positiveWordEquiv CWBlock r
          (positiveSupportWordBlockAddress cwBlockSupport r word c) position :=
      (congrFun
        (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
          cwBlockSupport r word c) position).symm
    _ = positiveWordEquiv CWBlock r (positiveWordConst .zero r) position := hzPosition
    _ = .zero := by simp only [positiveWordEquiv_const]

/-- The second-live-leg product dimension of a supported zero-`zero` base word is the power of `q`
counted by its middle positions on the first live leg. -/
theorem positiveWordProduct_cwBaseDimension_secondLiveLeg_eq_pow_middleCount_of_eq_const
    (q : ℕ) (zero : Leg) (r : ℕ) (word : PositiveWord cwBlockSupport r)
    (hzero : positiveSupportWordBlockAddress cwBlockSupport r word zero =
      positiveWordConst .zero r) :
    positiveWordProduct
        (fun support ↦ cwBaseConstituentDimension q support (secondLiveLeg zero)) r word =
      q ^ cwSupportedWordMiddleCount (firstLiveLeg zero) r word := by
  rw [positiveWordProduct_eq_fin_prod]
  calc
    (∏ position,
        cwBaseConstituentDimension q
          (positiveWordEquiv cwBlockSupport r word position) (secondLiveLeg zero)) =
        ∏ position,
          q ^ (if cwBlockDigit
              ((positiveWordEquiv cwBlockSupport r word position).1 (firstLiveLeg zero)) =
                (1 : SplitDigit) then 1 else 0) := by
      apply Finset.prod_congr rfl
      intro position _
      exact cwBaseConstituentDimension_secondLiveLeg_eq_pow_middleIndicator_of_eq_zero q zero _
        (positiveSupportWord_letter_eq_zero_of_address_eq_const zero word hzero position)
    _ = q ^ cwSupportedWordMiddleCount (firstLiveLeg zero) r word := by
      rw [Finset.prod_pow_eq_pow_sum]
      rfl

/-- For a supported base-address word, the encoded chunk on leg `c` has exactly the recursively
counted number of middle blocks on that leg.  The committed statement is the instance `c = .X`. -/
theorem splitWordMiddleCount_cwChunkSplitWord_positiveSupportWordBlockAddress_leg
    (c : Leg) (depth : ℕ) (word : PositiveWord cwBlockSupport (2 ^ depth - 1)) :
    splitWordMiddleCount
        (cwChunkSplitWord depth
          (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word c)) =
      cwSupportedWordMiddleCount c (2 ^ depth - 1) word := by
  rw [splitWordMiddleCount_cwChunkSplitWord]
  unfold cwSupportedWordMiddleCount
  apply Finset.sum_congr rfl
  intro position _
  rw [congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
      cwBlockSupport (2 ^ depth - 1) word c) position]

/-! ## The rotated word and chunk certificates -/

section Certificates

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- Word-aligned rotated certificates for every letter of a supported zero-`zero` word. -/
noncomputable def cwZeroBaseRotatedWordData
    (zero : Leg) (r : ℕ) (word : PositiveWord cwBlockSupport r)
    (hzero : positiveSupportWordBlockAddress cwBlockSupport r word zero =
      positiveWordConst .zero r) :
    OneSliceRestriction.PermutedPositiveSupportWordData
      (cwPartitionedTensor K q)
      (fun support ↦ cwBaseConstituentDimension q support (secondLiveLeg zero))
      (zeroOrientation zero) r word := by
  induction r with
  | zero =>
      exact cwZeroBaseRotatedOneSliceRestriction K q zero word hzero
  | succ r ih =>
      exact ⟨ih word.1 (congrArg Prod.fst hzero),
        cwZeroBaseRotatedOneSliceRestriction K q zero word.2 (congrArg Prod.snd hzero)⟩

/-- A whole supported zero-`zero` base word, rotated into the canonical shared-`Z` frame, has an
explicit one-slice restriction. -/
noncomputable def cwZeroBaseRotatedWordOneSliceRestriction
    (zero : Leg) (r : ℕ) (word : PositiveWord cwBlockSupport r)
    (hzero : positiveSupportWordBlockAddress cwBlockSupport r word zero =
      positiveWordConst .zero r) :
    OneSliceRestriction
      (Tensor.permute (K := K) (zeroOrientation zero)
        ((cwPartitionedTensor K q).positiveSupportWordTensor r word))
      (positiveWordProduct
        (fun support ↦ cwBaseConstituentDimension q support (secondLiveLeg zero)) r word) :=
  OneSliceRestriction.ofPermutedPositiveSupportWordData
    (cwPartitionedTensor K q)
    (fun support ↦ cwBaseConstituentDimension q support (secondLiveLeg zero))
    (zeroOrientation zero) r word
    (cwZeroBaseRotatedWordData K q zero r word hzero)

/-- **Every zero-`zero` recursive chunk, rotated into the canonical shared-`Z` frame, has an
explicit restriction to `⟨1, q^k, 1⟩`, with `k` read from its encoded split word on the first live
leg.**

At `zero = .Z` this is the committed `cwZeroChunkOneSliceRestriction` verbatim; the zero-`X` and
zero-`Y` instances are the ones item 3 owed. -/
noncomputable def cwZeroChunkRotatedOneSliceRestriction
    (zero : Leg) (depth : ℕ)
    (support : (cwChunkPartitionedTensor K q depth).support)
    (hzero : support.1 zero = cwZeroChunkWord depth) :
    OneSliceRestriction
      (Tensor.permute (K := K) (zeroOrientation zero)
        ((cwChunkPartitionedTensor K q depth).constituent support.1))
      (q ^ splitWordMiddleCount
        (cwChunkSplitWord depth (support.1 (firstLiveLeg zero)))) := by
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
  let data := cwZeroBaseRotatedWordData K q zero (2 ^ depth - 1) word hzeroWord
  let C := OneSliceRestriction.ofPermutedPositivePowerConstituentData
    (cwPartitionedTensor K q)
    (fun base ↦ cwBaseConstituentDimension q base (secondLiveLeg zero))
    (zeroOrientation zero) (2 ^ depth - 1) word data
  have hdimension :
      positiveWordProduct
          (fun base ↦ cwBaseConstituentDimension q base (secondLiveLeg zero))
          (2 ^ depth - 1) word =
        q ^ splitWordMiddleCount
          (cwChunkSplitWord depth (support.1 (firstLiveLeg zero))) := by
    rw [positiveWordProduct_cwBaseDimension_secondLiveLeg_eq_pow_middleCount_of_eq_const
      q zero _ word hzeroWord]
    congr 1
    rw [← splitWordMiddleCount_cwChunkSplitWord_positiveSupportWordBlockAddress_leg
      (firstLiveLeg zero) depth word, haddress']
  have C' := C.castDimension hdimension
  change OneSliceRestriction
    (Tensor.permute (K := K) (zeroOrientation zero)
      (((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).constituent support.1)) _
  exact haddress' ▸ C'

/-- The zero-`X` instance: a chunk whose `X` word is the all-zero chunk word, rotated by
`zeroOrientation .X = cycle.symm`, restricts to `⟨1, q^k, 1⟩` with `k` read from its `Y` word. -/
noncomputable def cwZeroXChunkRotatedOneSliceRestriction
    (depth : ℕ) (support : (cwChunkPartitionedTensor K q depth).support)
    (hzero : support.1 .X = cwZeroChunkWord depth) :
    OneSliceRestriction
      (Tensor.permute (K := K) cycle.symm
        ((cwChunkPartitionedTensor K q depth).constituent support.1))
      (q ^ splitWordMiddleCount (cwChunkSplitWord depth (support.1 .Y))) :=
  cwZeroChunkRotatedOneSliceRestriction K q .X depth support hzero

/-- The zero-`Y` instance: a chunk whose `Y` word is the all-zero chunk word, rotated by
`zeroOrientation .Y = cycle`, restricts to `⟨1, q^k, 1⟩` with `k` read from its `Z` word. -/
noncomputable def cwZeroYChunkRotatedOneSliceRestriction
    (depth : ℕ) (support : (cwChunkPartitionedTensor K q depth).support)
    (hzero : support.1 .Y = cwZeroChunkWord depth) :
    OneSliceRestriction
      (Tensor.permute (K := K) cycle
        ((cwChunkPartitionedTensor K q depth).constituent support.1))
      (q ^ splitWordMiddleCount (cwChunkSplitWord depth (support.1 .Z))) :=
  cwZeroChunkRotatedOneSliceRestriction K q .Y depth support hzero

/-- The zero-`Z` instance, for comparison: the identity rotation recovers the committed exponent
`q ^ splitWordMiddleCount (cwChunkSplitWord depth (support.1 .X))`. -/
noncomputable def cwZeroZChunkRotatedOneSliceRestriction
    (depth : ℕ) (support : (cwChunkPartitionedTensor K q depth).support)
    (hzero : support.1 .Z = cwZeroChunkWord depth) :
    OneSliceRestriction
      (Tensor.permute (K := K) (1 : Orientation)
        ((cwChunkPartitionedTensor K q depth).constituent support.1))
      (q ^ splitWordMiddleCount (cwChunkSplitWord depth (support.1 .X))) :=
  cwZeroChunkRotatedOneSliceRestriction K q .Z depth support hzero

end Certificates

end AlgebraicComplexity.Examples
