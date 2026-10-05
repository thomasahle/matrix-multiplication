import AlgebraicComplexity.MatrixMultiplication.MarkedPartitionedPowerHashing
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafExtraction

/-!
# Marked hashing extraction for rational typed leaves

This file is the paper-independent finite extraction theorem for a rational typed leaf.  A client
supplies

* a tight field encoding of the partition support;
* an ambient word family obtainable by legwise zeroing;
* a marked subfamily of one exact proportional joint type; and
* the usual finite competitor bound.

Marked affine hashing isolates the chosen joint type against every ambient competitor.  Each
survivor is then converted, by the generic typed-leaf constituent theorem, to the same
rectangular matrix-multiplication tensor.  The result is a genuine indexed direct sum, not merely
a collection of individually available restrictions.

The ambient partition may be localized inside a quotient fiber.  Its support and constituents
are related to the original positive power by explicit hypotheses, which lets quotient clients
reuse this theorem without pretending that a single representative leaf preserves an inner copy
exponent.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x y

namespace RationalTypedLeaf

variable {K : Type u} [CommSemiring K]
variable {R : Type v} [Field R]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u x)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- A localized ambient partition and marked exact joint type hash to an indexed direct sum of
equal rational typed leaves.

`hconstituentQ` is intentionally semantic rather than definitional: it covers ordinary legwise
selection, localization inside a coarsening fiber, and any future zeroing wrapper whose retained
constituents agree with the original positive-power constituents. -/
theorem localizedAmbient_restricts_markedLeafDirectSum
    {P : PartitionedTensor (K := K) (A := A) V}
    [Nonempty P.support]
    {C : Leg → Type y} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf P.support C)
    (hbase : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z)))
    (H : PartitionHashEncoding (R := R) P.support)
    (n k : ℕ)
    (ambientWords markedWords : Finset (PositiveWord P.support n))
    (hmarked : markedWords ⊆ ambientWords)
    (hmarkedType : ∀ word ∈ markedWords,
      WordType.multiplicity (positiveWordEquiv P.support n word) =
        WordType.proportionalCounts leaf.profile.count k)
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
  obtain ⟨word, hwordMarked, hwordAddress⟩ :=
    H.exists_markedSourceWord_of_mem_markedLegwiseIsolatedPowerAddresses
      n ambientWords markedWords B seed address.2
  have hwordType : word ∈ positiveTypeClass P.support n
      (WordType.proportionalCounts leaf.profile.count k) := by
    rw [mem_positiveTypeClass]
    exact hmarkedType word hwordMarked
  have hleaf := leaf.positivePower_constituent_matrixMultiplication_proportional
    P hbase word hwordType
  change Restricts (Q.constituent address.1) _
  rw [hconstituentQ, ← hwordAddress]
  exact hleaf

/-- Finite good-seed form of `localizedAmbient_restricts_markedLeafDirectSum`.  The same seed
simultaneously satisfies the exact division-free survivor count and the tensor degeneration to
that survivor-indexed rectangular family. -/
theorem exists_seed_many_localizedMarkedLeafDirectSum
    {P : PartitionedTensor (K := K) (A := A) V}
    [Nonempty P.support]
    {C : Leg → Type y} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf P.support C)
    (hbase : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z)))
    (H : PartitionHashEncoding (R := R) P.support)
    (n k : ℕ)
    (ambientWords markedWords : Finset (PositiveWord P.support n))
    (hmarked : markedWords ⊆ ambientWords)
    (hmarkedType : ∀ word ∈ markedWords,
      WordType.multiplicity (positiveWordEquiv P.support n word) =
        WordType.proportionalCounts leaf.profile.count k)
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
    (leaf.localizedAmbient_restricts_markedLeafDirectSum hbase H n k
      ambientWords markedWords hmarked hmarkedType Q hsupport hconstituentQ B hB seed)

end RationalTypedLeaf

end AlgebraicComplexity
