/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordType
import AlgebraicComplexity.MatrixMultiplication.EmbeddedRationalTypedLeafExtraction
import AlgebraicComplexity.MatrixMultiplication.MarkedPartitionedPowerHashing

set_option autoImplicit false

/-!
# Marked hashing for a sparse embedded rational typed leaf

This is the sparse-alphabet companion of `RationalTypedLeafHashing`.  The marked words have the
zero-extended type obtained by pushing the strictly positive leaf profile through an embedding
into the ambient partition support.  Every such word has an exact lift to the leaf alphabet;
the embedded constituent theorem then identifies every isolated survivor with the same
rectangular matrix-multiplication tensor.

The theorem retains the anti-laundering boundary of the ordinary hashing API: the direct-sum
restriction is derived from the concrete modeled ambient, marked family, and affine seed.  No
restriction of an already assembled survivor family is accepted as a premise.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x y z

namespace RationalTypedLeaf

variable {I : Type z} [Fintype I] [Nonempty I]
variable {K : Type u} [CommSemiring K]
variable {R : Type v} [Field R]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {C : Leg → Type y} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
variable {V : ∀ c, A c → Type (max u x)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

private theorem mappedType_proportionalCounts
    {S T : Type*} [Fintype S]
    (f : S → T) (profile : S → ℕ) (k : ℕ) :
    WordType.mappedType f (WordType.proportionalCounts profile k) =
      WordType.proportionalCounts (WordType.mappedType f profile) k := by
  classical
  funext target
  simp only [WordType.mappedType, WordType.proportionalCounts, Finset.sum_mul]

private theorem exists_positiveWord_typed_lift
    {S T : Type*} [Fintype S] [Fintype T]
    (f : S → T) (n : ℕ) (profile : S → ℕ) (target : PositiveWord T n)
    (hprofile : profile ∈ WordType.types S (n + 1))
    (htarget : target ∈ positiveTypeClass T n (WordType.mappedType f profile)) :
    ∃ source : PositiveWord S n,
      source ∈ positiveTypeClass S n profile ∧ positiveWordMap f n source = target := by
  classical
  have htarget' : positiveWordEquiv T n target ∈
      WordType.typeClass (n + 1) (WordType.mappedType f profile) := by
    rw [WordType.mem_typeClass]
    exact mem_positiveTypeClass.mp htarget
  have hsourceClass : 0 < (WordType.typeClass (n + 1) profile).card :=
    Finset.card_pos.mpr (WordType.typeClass_nonempty profile hprofile)
  have hfactor := WordType.card_targetType_mul_card_typedWordMapFiber
    f profile (positiveWordEquiv T n target) htarget'
  have hfiber : 0 < (WordType.typedWordMapFiber f profile
      (positiveWordEquiv T n target)).card := by
    have hproduct : 0 <
        (WordType.typeClass (n + 1) (WordType.mappedType f profile)).card *
          (WordType.typedWordMapFiber f profile
            (positiveWordEquiv T n target)).card := by
      rw [hfactor]
      exact hsourceClass
    exact Nat.pos_of_mul_pos_left hproduct
  obtain ⟨source, hsource⟩ := Finset.card_pos.mp hfiber
  have hsource' := WordType.mem_typedWordMapFiber.mp hsource
  let sourceWord : PositiveWord S n := (positiveWordEquiv S n).symm source
  refine ⟨sourceWord, ?_, ?_⟩
  · rw [mem_positiveTypeClass]
    simpa [sourceWord] using hsource'.1
  · apply (positiveWordEquiv T n).injective
    rw [positiveWordEquiv_map]
    simpa [sourceWord] using hsource'.2

omit [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)] in
/-- A localized ambient and a sparse embedded marked type restrict to an indexed direct sum of
equal rational typed leaves. -/
theorem localizedAmbient_restricts_embeddedMarkedLeafDirectSum
    {P : PartitionedTensor (K := K) (A := A) V}
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ P.support)
    (dimension : P.support → Leg → ℕ)
    (hbase : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (dimension s .X) (dimension s .Y) (dimension s .Z)))
    (hdimension : ∀ i c, leaf.dimension i c = dimension (letter i) c)
    (H : PartitionHashEncoding (R := R) P.support)
    (n k : ℕ)
    (ambientWords markedWords : Finset (PositiveWord P.support n))
    (hmarked : markedWords ⊆ ambientWords)
    (hmarkedType : ∀ word ∈ markedWords,
      WordType.multiplicity (positiveWordEquiv P.support n word) =
        WordType.proportionalCounts
          (WordType.mappedType letter leaf.profile.count) k)
    (Q : PartitionedTensor (K := K)
      (A := fun c ↦ PositiveWord (A c) n) (PositivePowerBlockSpace K V n))
    (hsupport : Q.support =
      H.modeledAddresses n (H.legalTargets n ambientWords))
    (hconstituentQ : ∀ address, Q.constituent address =
      (P.positivePower n).constituent address)
    [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Restricts Q.realize
      (Tensor.indexedDirectSum
        (fun _selected : H.markedLegwiseIsolatedPowerAddresses
          n ambientWords markedWords B seed ↦
          matrixMultiplication (K := K)
            (leaf.dimensionProduct .X ^ k)
            (leaf.dimensionProduct .Y ^ k)
            (leaf.dimensionProduct .Z ^ k))) := by
  classical
  let selected := H.markedLegwiseIsolatedPowerAddresses
    n ambientWords markedWords B seed
  have hseparate : Restricts Q.realize
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily (V := PositivePowerBlockSpace K V n) selected)
        (fun s : selected ↦ Q.constituent s.1)) := by
    exact Tensor.Restricts.modeledTargets_to_markedLegwiseIsolatedIndexedDirectSum
      H ambientWords markedWords hmarked B hB seed Q hsupport
  apply hseparate.trans
  apply Restricts.indexedDirectSum
  intro address
  obtain ⟨targetWord, htargetMarked, htargetAddress⟩ :=
    H.exists_markedSourceWord_of_mem_markedLegwiseIsolatedPowerAddresses
      n ambientWords markedWords B seed address.2
  have htargetType : targetWord ∈ positiveTypeClass P.support n
      (WordType.mappedType letter
        (WordType.proportionalCounts leaf.profile.count k)) := by
    rw [mappedType_proportionalCounts, mem_positiveTypeClass]
    exact hmarkedType targetWord htargetMarked
  have hsourceType :
      WordType.proportionalCounts leaf.profile.count k ∈
        WordType.types I (n + 1) := by
    rw [WordType.mem_types]
    have htargetMultiplicity := mem_positiveTypeClass.mp htargetType
    calc
      ∑ i, WordType.proportionalCounts leaf.profile.count k i =
          ∑ support, WordType.mappedType (letter : I → P.support)
            (WordType.proportionalCounts leaf.profile.count k) support :=
        (WordType.sum_mappedType (letter : I → P.support)
          (WordType.proportionalCounts leaf.profile.count k)).symm
      _ = ∑ support, WordType.multiplicity
          (positiveWordEquiv P.support n targetWord) support := by
        rw [htargetMultiplicity]
      _ = n + 1 := WordType.sum_multiplicity _
  obtain ⟨sourceWord, hsourceWord, hmap⟩ :=
    exists_positiveWord_typed_lift (letter : I → P.support) n
      (WordType.proportionalCounts leaf.profile.count k)
      targetWord hsourceType htargetType
  have hleaf := leaf.positivePower_constituent_matrixMultiplication_proportional_embedded
    P letter dimension hbase hdimension sourceWord hsourceWord
  change Restricts (Q.constituent address.1) _
  rw [hconstituentQ, ← htargetAddress, ← hmap]
  exact hleaf

omit [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)] in
/-- Good-seed form of `localizedAmbient_restricts_embeddedMarkedLeafDirectSum`, returning both
the exact division-free survivor count and the polynomial degeneration obtained from the same
seed. -/
theorem exists_seed_many_localizedEmbeddedMarkedLeafDirectSum
    {P : PartitionedTensor (K := K) (A := A) V}
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ P.support)
    (dimension : P.support → Leg → ℕ)
    (hbase : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (dimension s .X) (dimension s .Y) (dimension s .Z)))
    (hdimension : ∀ i c, leaf.dimension i c = dimension (letter i) c)
    (H : PartitionHashEncoding (R := R) P.support)
    (n k : ℕ)
    (ambientWords markedWords : Finset (PositiveWord P.support n))
    (hmarked : markedWords ⊆ ambientWords)
    (hmarkedType : ∀ word ∈ markedWords,
      WordType.multiplicity (positiveWordEquiv P.support n word) =
        WordType.proportionalCounts
          (WordType.mappedType letter leaf.profile.count) k)
    (Q : PartitionedTensor (K := K)
      (A := fun c ↦ PositiveWord (A c) n) (PositivePowerBlockSpace K V n))
    (hsupport : Q.support =
      H.modeledAddresses n (H.legalTargets n ambientWords))
    (hconstituentQ : ∀ address, Q.constituent address =
      (P.positivePower n).constituent address)
    [Fintype R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ H.legalTargets n markedWords,
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (H.legalTargets n ambientWords) triple).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (H.markedLegwiseIsolatedPowerAddresses
              n ambientWords markedWords B seed).card ∧
        PolynomialDegenerates Q.realize
          (Tensor.indexedDirectSum
            (fun _selected : H.markedLegwiseIsolatedPowerAddresses
              n ambientWords markedWords B seed ↦
              matrixMultiplication (K := K)
                (leaf.dimensionProduct .X ^ k)
                (leaf.dimensionProduct .Y ^ k)
                (leaf.dimensionProduct .Z ^ k))) := by
  obtain ⟨seed, hcount, _hsubset, _hinjective⟩ :=
    H.exists_seed_many_markedLegwiseIsolatedPowerAddresses
      n ambientWords markedWords hmarked B hB hquarter
  refine ⟨seed, hcount, ?_⟩
  exact PolynomialDegenerates.of_restricts
    (leaf.localizedAmbient_restricts_embeddedMarkedLeafDirectSum
      letter dimension hbase hdimension H n k
      ambientWords markedWords hmarked hmarkedType Q hsupport hconstituentQ B hB seed)

end RationalTypedLeaf

end AlgebraicComplexity
