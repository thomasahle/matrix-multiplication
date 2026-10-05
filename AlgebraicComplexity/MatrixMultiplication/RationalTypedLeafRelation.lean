import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafHashing
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafDegeneration
import AlgebraicComplexity.Tensor.IndexedDegeneration

/-!
# Relation-parametric constituent certificates for typed leaves

`RationalTypedLeaf` describes a profile and the matrix dimensions of its constituents.  It should
not prescribe whether those constituents are obtained by zeroing, exact restriction, or a
polynomial degeneration.  This module makes that separation explicit.

`TypedLeafExtractionCertificate` stores an arbitrary constituent-level relation `Rel`, together
with the polynomial-degeneration theorem needed by the finite extraction step.  Exact restriction
is merely one adapter (`of_restriction`); clients can instead supply a genuine polynomial
degeneration certificate without changing any typed-leaf or entropy code.  The distinction between
restriction and degeneration is represented in the type of the witness, rather than hidden behind
a relation name.

The certificate is polymorphic in the leaf itself.  In particular, a primitive leaf, a permuted
leaf, and the iterated cyclic product from `RationalTypedLeafProduct.lean` all use this same
relation interface.  The relation layer therefore composes with the typed-leaf product API; it is
not a parallel cyclic data model.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x y

namespace RationalTypedLeaf

variable {K : Type u} [CommSemiring K]
variable {R : Type w} [Field R]
variable {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u x)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {C : Leg → Type y} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]

/-- A semantic relation used to obtain the matrix tensor recorded by a typed leaf.

The relation is intentionally a proposition on each supported constituent rather than a field of
the leaf.  Its `degenerates` field is the semantic fact consumed by finite extraction. -/
structure TypedLeafExtractionCertificate
    {P : PartitionedTensor (K := K) (A := A) V}
    (leaf : RationalTypedLeaf P.support C)
    (Rel : P.support → Prop) where
  witness : ∀ s, Rel s
  degenerates : ∀ s, Rel s →
    PolynomialDegenerates (P.constituent s.1)
      (matrixMultiplication (K := K)
        (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z))

/-- Package exact constituent restrictions as a relation-parametric certificate. -/
theorem TypedLeafExtractionCertificate.of_restriction
    {P : PartitionedTensor (K := K) (A := A) V}
    (leaf : RationalTypedLeaf P.support C)
    (hbase : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z))) :
    TypedLeafExtractionCertificate leaf
      (fun s ↦ Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z))) where
  witness := hbase
  degenerates := fun s _h ↦ PolynomialDegenerates.of_restricts (hbase s)

/-- Package arbitrary constituent polynomial degenerations as a relation-parametric certificate.

The relation can encode a zeroing plan, a monomial degeneration, an interpolation certificate, or
any other paper-specific predicate.  The finite value theorem only sees the resulting semantic
`PolynomialDegenerates` witness. -/
theorem TypedLeafExtractionCertificate.of_polynomialDegenerates
    {P : PartitionedTensor (K := K) (A := A) V}
    (leaf : RationalTypedLeaf P.support C)
    (Rel : P.support → Prop)
    (hwitness : ∀ s, Rel s)
    (hbase : ∀ s : P.support, Rel s →
      PolynomialDegenerates (P.constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z))) :
    TypedLeafExtractionCertificate leaf Rel where
  witness := hwitness
  degenerates := hbase

/-- The relation-parametric finite extraction theorem.

Proof sketch: the affine-hashing argument first restricts to an indexed direct sum of the
surviving partition constituents.  Apply the certificate's constituent restrictions to each
surviving address, combine them with the positive-power typed-leaf theorem, and then promote the
resulting direct-sum restriction to a polynomial degeneration. -/
theorem localizedAmbient_degenerates_markedLeafDirectSum_of_certificate
    {P : PartitionedTensor (K := K) (A := A) V}
    [Nonempty P.support]
    {C : Leg → Type y} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf P.support C)
    (Rel : P.support → Prop)
    (certificate : TypedLeafExtractionCertificate
      (P := P) leaf Rel)
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
    PolynomialDegenerates Q.realize
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
  have hpromoted : PolynomialDegenerates Q.realize
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily (V := PositivePowerBlockSpace K V n) selected)
        (fun s : selected ↦ Q.constituent s.1)) :=
    PolynomialDegenerates.of_restricts hseparate
  have hcomponents : PolynomialDegenerates
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily (V := PositivePowerBlockSpace K V n) selected)
        (fun s : selected ↦ Q.constituent s.1))
      (Tensor.indexedDirectSum
        (fun _selected : selected ↦
          matrixMultiplication (K := K)
            (leaf.dimensionProduct .X ^ k)
            (leaf.dimensionProduct .Y ^ k)
            (leaf.dimensionProduct .Z ^ k))) := by
    apply PolynomialDegenerates.indexedDirectSum
    intro address
    obtain ⟨word, hwordMarked, hwordAddress⟩ :=
      H.exists_markedSourceWord_of_mem_markedLegwiseIsolatedPowerAddresses
        n ambientWords markedWords B seed address.2
    have hwordType : word ∈ positiveTypeClass P.support n
        (WordType.proportionalCounts leaf.profile.count k) := by
      rw [mem_positiveTypeClass]
      exact hmarkedType word hwordMarked
    have hleaf :=
      leaf.positivePower_constituent_matrixMultiplication_proportional_of_polynomialDegenerates
        P (fun s ↦ certificate.degenerates s (certificate.witness s)) word hwordType
    change PolynomialDegenerates (Q.constituent address.1) _
    rw [hconstituentQ, ← hwordAddress]
    exact hleaf
  exact hpromoted.trans hcomponents

/-- Exact restriction is the standard specialization of the relation-parametric theorem. -/
theorem localizedAmbient_degenerates_markedLeafDirectSum_of_restriction
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
    PolynomialDegenerates Q.realize
      (Tensor.indexedDirectSum
        (fun _selected : H.markedLegwiseIsolatedPowerAddresses
          n ambientWords markedWords B seed ↦
          matrixMultiplication (K := K)
            (leaf.dimensionProduct .X ^ k)
            (leaf.dimensionProduct .Y ^ k)
            (leaf.dimensionProduct .Z ^ k))) := by
  exact localizedAmbient_degenerates_markedLeafDirectSum_of_certificate
    leaf _ (TypedLeafExtractionCertificate.of_restriction leaf hbase)
    H n k ambientWords markedWords hmarked hmarkedType Q hsupport hconstituentQ B hB seed

end RationalTypedLeaf

end AlgebraicComplexity
