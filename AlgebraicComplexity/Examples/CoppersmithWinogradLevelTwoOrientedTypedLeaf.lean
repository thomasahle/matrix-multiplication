/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112TypedLeaf
import AlgebraicComplexity.Examples.CoppersmithWinogradChunkTypedLeaf
import AlgebraicComplexity.MatrixMultiplication.EmbeddedRationalTypedLeafSegmentedAssembly
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafProduct
import AlgebraicComplexity.Tensor.LocalizedCoarsenedSelection
import AlgebraicComplexity.Tensor.PartitionedPermutation

/-!
# Oriented level-two CW leaves inside the uncoarsened tensor square

Every positive level-two constituent has shape `112`, `211`, or `121`.  The canonical rational
typed leaf is written in the `112` orientation, with its ternary compatibility coordinate on `Z`.
This module embeds that four-letter leaf into the uncoarsened square partition and transports it
to an arbitrary heavy coordinate.

The construction is tensor-semantic: every exact proportional leaf word becomes a local
`SegmentedLeafCertificate` for the honest uncoarsened square.  It is consequently suitable for
the heterogeneous aggregate-hashing interface used by recursive certificates.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The three positive orientations -/

/-- Orientation carrying the canonical `112` heavy coordinate `Z` to the requested coordinate.

The values `0`, `1`, and `2` correspond respectively to `211`, `121`, and `112`. -/
def cwLevelTwoOrientation (heavy : Fin 3) : Orientation :=
  if heavy = 0 then cycle else if heavy = 1 then cycle.symm else Equiv.refl _

@[simp] theorem cwLevelTwoOrientation_zero : cwLevelTwoOrientation 0 = cycle := by
  simp [cwLevelTwoOrientation]

@[simp] theorem cwLevelTwoOrientation_one : cwLevelTwoOrientation 1 = cycle.symm := by
  simp [cwLevelTwoOrientation]

@[simp] theorem cwLevelTwoOrientation_two : cwLevelTwoOrientation 2 = Equiv.refl _ := by
  simp [cwLevelTwoOrientation]

/-! ## The four raw square words in the canonical fiber -/

private abbrev cwLevelTwo002S : cwBlockSupport := ⟨cw002, by decide⟩
private abbrev cwLevelTwo011S : cwBlockSupport := ⟨cw011, by decide⟩
private abbrev cwLevelTwo101S : cwBlockSupport := ⟨cw101, by decide⟩
private abbrev cwLevelTwo110S : cwBlockSupport := ⟨cw110, by decide⟩

/-- The raw two-CW-letter word represented by one canonical `112` block address.

The order agrees with the four branches in `cwSquareConstituent_112`: diagonal first is
`110 ⊗ 002`, diagonal second is `002 ⊗ 110`, and the two grid branches are `101 ⊗ 011` and
`011 ⊗ 101`. -/
def cw112FineWord (source : cw112BlockSupport) : PositiveWord cwBlockSupport 1 :=
  match source.1 .Z with
  | .firstCorner => (cwLevelTwo110S, cwLevelTwo002S)
  | .secondCorner => (cwLevelTwo002S, cwLevelTwo110S)
  | .grid =>
      match source.1 .X with
      | .first => (cwLevelTwo101S, cwLevelTwo011S)
      | .second => (cwLevelTwo011S, cwLevelTwo101S)

@[simp] theorem cw112FineWord_diagonalFirst :
    cw112FineWord cw112DiagonalFirstS = (cwLevelTwo110S, cwLevelTwo002S) := by
  rfl

@[simp] theorem cw112FineWord_diagonalSecond :
    cw112FineWord cw112DiagonalSecondS = (cwLevelTwo002S, cwLevelTwo110S) := by
  rfl

@[simp] theorem cw112FineWord_crossFirst :
    cw112FineWord cw112CrossFirstS = (cwLevelTwo101S, cwLevelTwo011S) := by
  rfl

@[simp] theorem cw112FineWord_crossSecond :
    cw112FineWord cw112CrossSecondS = (cwLevelTwo011S, cwLevelTwo101S) := by
  rfl

theorem cw112FineWord_injective : Function.Injective cw112FineWord := by
  decide

/-! ## Coordinate transport and the ambient support embedding -/

/-- Leg permutation specialized to the constant three-leg CW block alphabet.

Using this nondependent equivalence avoids inserting casts through `PermutedBlockIndex`; the
generic dependent permutation remains the right API when the three block-label types differ. -/
def cwPermuteBlockAddress (e : Orientation) : CWBlockAddress ≃ CWBlockAddress where
  toFun source c := source (e.symm c)
  invFun source c := source (e c)
  left_inv source := by
    ext c
    exact congrArg source (e.symm_apply_apply c)
  right_inv source := by
    ext c
    exact congrArg source (e.apply_symm_apply c)

@[simp] theorem cwPermuteBlockAddress_apply
    (e : Orientation) (source : CWBlockAddress) (c : Leg) :
    cwPermuteBlockAddress e source c = source (e.symm c) :=
  rfl

/-- Permuting a supported base CW address by one of the three positive orientations preserves
the six-address support. -/
theorem cwPermuteBlockAddress_cwLevelTwoOrientation_mem
    (heavy : Fin 3) (source : CWBlockAddress) (hsource : source ∈ cwBlockSupport) :
    cwPermuteBlockAddress (cwLevelTwoOrientation heavy) source ∈ cwBlockSupport := by
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hsource
  rcases hsource with rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases heavy <;> decide

/-- Permute one supported base CW address by the positive level-two orientation. -/
def cwLevelTwoPermutedBlock (heavy : Fin 3) (source : cwBlockSupport) : cwBlockSupport :=
  ⟨cwPermuteBlockAddress (cwLevelTwoOrientation heavy) source.1,
    cwPermuteBlockAddress_cwLevelTwoOrientation_mem heavy source.1 source.2⟩

@[simp] theorem cwLevelTwoPermutedBlock_val (heavy : Fin 3) (source : cwBlockSupport) :
    (cwLevelTwoPermutedBlock heavy source).1 =
      cwPermuteBlockAddress (cwLevelTwoOrientation heavy) source.1 :=
  rfl

theorem cwLevelTwoPermutedBlock_injective (heavy : Fin 3) :
    Function.Injective (cwLevelTwoPermutedBlock heavy) := by
  intro left right h
  apply Subtype.ext
  apply (cwPermuteBlockAddress (cwLevelTwoOrientation heavy)).injective
  exact congrArg Subtype.val h

/-- The oriented raw square word belonging to one abstract `112` leaf letter. -/
def cwLevelTwoFineWord (heavy : Fin 3) (source : cw112BlockSupport) :
    PositiveWord cwBlockSupport 1 :=
  positiveWordMap (cwLevelTwoPermutedBlock heavy) 1 (cw112FineWord source)

theorem cwLevelTwoFineWord_injective (heavy : Fin 3) :
    Function.Injective (cwLevelTwoFineWord heavy) := by
  exact (positiveWordMap_injective (cwLevelTwoPermutedBlock_injective heavy) 1).comp
    cw112FineWord_injective

/-- The same raw word, with its alphabet exposed as the support field of the actual CW
partition.  The wrapper is propositionally content-free; it only crosses the opacity boundary of
`cwPartitionedTensor`. -/
noncomputable def cwLevelTwoPartitionFineWord
    (K : Type u) [CommRing K] (q : ℕ) (heavy : Fin 3) (source : cw112BlockSupport) :
    PositiveWord (cwPartitionedTensor K q).support 1 := by
  change PositiveWord cwBlockSupport 1
  exact cwLevelTwoFineWord heavy source

theorem cwLevelTwoPartitionFineWord_injective
    (K : Type u) [CommRing K] (q : ℕ) (heavy : Fin 3) :
    Function.Injective (cwLevelTwoPartitionFineWord K q heavy) := by
  change Function.Injective (cwLevelTwoFineWord heavy)
  exact cwLevelTwoFineWord_injective heavy

/-- One oriented four-letter level-two alphabet embedded in the full uncoarsened square support. -/
noncomputable def cwLevelTwoFineLetter
    (K : Type u) [CommRing K] (q : ℕ) (heavy : Fin 3) :
    cw112BlockSupport ↪ (cwChunkPartitionedTensor K q 1).support where
  toFun source := by
    refine ⟨positiveSupportWordBlockAddress (cwPartitionedTensor K q).support 1
      (cwLevelTwoPartitionFineWord K q heavy source), ?_⟩
    change positiveSupportWordBlockAddress (cwPartitionedTensor K q).support 1
      (cwLevelTwoPartitionFineWord K q heavy source) ∈
        ((cwPartitionedTensor K q).positivePower 1).support
    rw [(cwPartitionedTensor K q).positivePower_support_eq_image_positiveSupportWordBlockAddress]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  inj' := by
    intro left right h
    apply cwLevelTwoPartitionFineWord_injective K q heavy
    apply positiveSupportWordBlockAddress_injective (cwPartitionedTensor K q).support 1
    exact congrArg Subtype.val h

/-- Recovering the base-CW word from the embedded chunk letter returns the displayed oriented
two-letter word. -/
theorem cwChunkSupportedWordOfAddress_cwLevelTwoFineLetter
    (K : Type u) [CommRing K] (q : ℕ) (heavy : Fin 3)
    (source : cw112BlockSupport) :
    cwChunkSupportedWordOfAddress K q 1 (cwLevelTwoFineLetter K q heavy source) =
      cwLevelTwoPartitionFineWord K q heavy source := by
  apply positiveSupportWordBlockAddress_injective (cwPartitionedTensor K q).support 1
  change positiveSupportWordBlockAddress (cwPartitionedTensor K q).support 1
      (cwChunkSupportedWordOfAddress K q 1 (cwLevelTwoFineLetter K q heavy source)) =
    (cwLevelTwoFineLetter K q heavy source).1
  simpa using positiveSupportWordBlockAddress_cwChunkSupportedWordOfAddress
    K q 1 (cwLevelTwoFineLetter K q heavy source)

/-! ## Exact dimensions and local semantic certificate -/

/-- The canonical rational leaf with its three visible legs transported to the requested heavy
coordinate. -/
def cwLevelTwoRationalTypedLeaf
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (heavy : Fin 3) :=
  (cw112RationalTypedLeaf q L G hq hL hG).permute (cwLevelTwoOrientation heavy)

/-- Every uncoarsened square constituent has the canonical chunk-dimension restriction. -/
theorem cwLevelTwoFineConstituent_restricts_dimension
    (K : Type u) [CommRing K] (q : ℕ) :
    ∀ support : (cwChunkPartitionedTensor K q 1).support,
      Restricts ((cwChunkPartitionedTensor K q 1).constituent support.1)
        (matrixMultiplication (K := K)
          (cwChunkConstituentDimension K q 1 support .X)
          (cwChunkConstituentDimension K q 1 support .Y)
          (cwChunkConstituentDimension K q 1 support .Z)) := by
  intro support
  exact cwChunkSupportedConstituent_restricts_productDimensions K q 1 support

/-- The oriented rational leaf's stored dimensions agree exactly with the honest raw-square
constituent dimensions at its embedded support letters. -/
theorem cwLevelTwoRationalTypedLeaf_dimension
    (K : Type u) [CommRing K]
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (heavy : Fin 3) (source : cw112BlockSupport) (c : Leg) :
    (cwLevelTwoRationalTypedLeaf q L G hq hL hG heavy).dimension source c =
      cwChunkConstituentDimension K q 1 (cwLevelTwoFineLetter K q heavy source) c := by
  rw [cwChunkConstituentDimension,
    cwChunkSupportedWordOfAddress_cwLevelTwoFineLetter]
  change (cwLevelTwoRationalTypedLeaf q L G hq hL hG heavy).dimension source c =
    positiveWordProduct (fun support : cwBlockSupport ↦
      cwBaseConstituentDimension q support c) 1 (cwLevelTwoFineWord heavy source)
  rcases source with ⟨source, hsource⟩
  simp only [cw112BlockSupport, Finset.mem_insert, Finset.mem_singleton] at hsource
  rcases hsource with rfl | rfl | rfl | rfl <;>
    fin_cases heavy <;> cases c <;>
    simp [cwLevelTwoRationalTypedLeaf, cwLevelTwoFineWord, cw112FineWord,
      positiveWordMap, cwLevelTwoPermutedBlock, cwLevelTwoOrientation,
      cwPermuteBlockAddress, cw112RationalTypedLeaf,
      cw112LeafDimension, cw112DiagonalFirstAddress,
      cw112DiagonalSecondAddress, cw112CrossFirstAddress, cw112CrossSecondAddress,
      cw112BlockAddress, cwBaseConstituentDimension, cwBlockMatrixDimensions,
      cycle, positiveWordProduct]

/-- A proportional word of one oriented positive level-two type gives a local segment certificate
inside the honest uncoarsened CW square. -/
noncomputable def cwLevelTwoSegmentedCertificate
    (K : Type u) [CommRing K]
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (heavy : Fin 3) {r k : ℕ}
    (word : PositiveWord cw112BlockSupport r)
    (hword : word ∈ positiveTypeClass cw112BlockSupport r
      (WordType.proportionalCounts
        (cwLevelTwoRationalTypedLeaf q L G hq hL hG heavy).profile.count k)) :
    PolynomialDegenerates.SegmentedLeafCertificate
      (cwChunkPartitionedTensor K q 1) :=
  (cwLevelTwoRationalTypedLeaf q L G hq hL hG heavy).embeddedSegmentedCertificate
    (cwChunkPartitionedTensor K q 1)
    (cwLevelTwoFineLetter K q heavy)
    (cwChunkConstituentDimension K q 1)
    (cwLevelTwoFineConstituent_restricts_dimension K q)
    (cwLevelTwoRationalTypedLeaf_dimension K q L G hq hL hG heavy)
    word hword

end AlgebraicComplexity.Examples
