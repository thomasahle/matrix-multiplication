/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.EmbeddedRationalTypedLeafExtraction
import AlgebraicComplexity.MatrixMultiplication.SegmentedLeafAssembly

set_option autoImplicit false

/-!
# Sparse typed leaves as local segment certificates

An exact rational leaf normally occupies only a small positive subalphabet of a much larger
partition support.  `EmbeddedRationalTypedLeafExtraction` proves the corresponding constituent
restriction.  This module packages the same factorwise proof as a `SegmentedLeafCertificate`, so
heterogeneous aggregate hashing can concatenate such leaves without accepting an assembled
degeneration as a premise.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x y

namespace RationalTypedLeaf

variable {I : Type y} [Fintype I] [Nonempty I]
variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
variable {V : ∀ c, A c → Type (max u x)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- A proportional sparse typed word gives the expected matrix-multiplication restriction before
it is embedded as a constituent of a full positive power.

The source is exactly the supported-word tensor on the mapped sparse word.  Thus this theorem is
the local semantic unit required by segmented aggregate assembly; no zero-mass ambient letter is
added to the leaf profile. -/
theorem positiveSupportWordTensor_matrixMultiplication_proportional_embedded
    (P : PartitionedTensor (K := K) (A := A) V)
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ P.support)
    (dimension : P.support → Leg → ℕ)
    (hbase : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (dimension s .X) (dimension s .Y) (dimension s .Z)))
    (hdimension : ∀ i c, leaf.dimension i c = dimension (letter i) c)
    {r k : ℕ} (word : PositiveWord I r)
    (hword : word ∈ positiveTypeClass I r
      (WordType.proportionalCounts leaf.profile.count k)) :
    Restricts
      (P.positiveSupportWordTensor r (positiveWordMap letter r word))
      (matrixMultiplication (K := K)
        (leaf.dimensionProduct .X ^ k)
        (leaf.dimensionProduct .Y ^ k)
        (leaf.dimensionProduct .Z ^ k)) := by
  have hwordTensor := positiveSupportWordTensor_matrixMultiplication_embedded
    P letter dimension hbase r word
  have product_eq (c : Leg) :
      embeddedWordDimension (fun i ↦ dimension (letter i) c) r word =
        leaf.dimensionProduct c ^ k := by
    calc
      embeddedWordDimension (fun i ↦ dimension (letter i) c) r word =
          ∏ i, dimension (letter i) c ^
            WordType.proportionalCounts leaf.profile.count k i :=
        embeddedWordDimension_eq_prod_pow _ word hword
      _ = ∏ i, leaf.dimension i c ^
            WordType.proportionalCounts leaf.profile.count k i := by
        apply Finset.prod_congr rfl
        intro i _hi
        rw [hdimension i c]
      _ = leaf.dimensionProduct c ^ k :=
        leaf.prod_dimension_proportionalCounts c k
  rw [product_eq .X, product_eq .Y, product_eq .Z] at hwordTensor
  exact hwordTensor

/-- Package a proportional word on an embedded positive alphabet as one local segment.

The certificate's word is obtained by mapping the sparse letters into the ambient support, and
its degeneration is constructed by the preceding theorem. -/
noncomputable def embeddedSegmentedCertificate
    (P : PartitionedTensor (K := K) (A := A) V)
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ P.support)
    (dimension : P.support → Leg → ℕ)
    (hbase : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (dimension s .X) (dimension s .Y) (dimension s .Z)))
    (hdimension : ∀ i c, leaf.dimension i c = dimension (letter i) c)
    {r k : ℕ} (word : PositiveWord I r)
    (hword : word ∈ positiveTypeClass I r
      (WordType.proportionalCounts leaf.profile.count k)) :
    PolynomialDegenerates.SegmentedLeafCertificate P where
  depth := r
  word := positiveWordMap letter r word
  xSize := leaf.dimensionProduct .X ^ k
  ySize := leaf.dimensionProduct .Y ^ k
  zSize := leaf.dimensionProduct .Z ^ k
  degenerates := PolynomialDegenerates.of_restricts
    (positiveSupportWordTensor_matrixMultiplication_proportional_embedded
      P leaf letter dimension hbase hdimension word hword)

@[simp] theorem embeddedSegmentedCertificate_depth
    (P : PartitionedTensor (K := K) (A := A) V)
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ P.support)
    (dimension : P.support → Leg → ℕ)
    (hbase : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (dimension s .X) (dimension s .Y) (dimension s .Z)))
    (hdimension : ∀ i c, leaf.dimension i c = dimension (letter i) c)
    {r k : ℕ} (word : PositiveWord I r)
    (hword : word ∈ positiveTypeClass I r
      (WordType.proportionalCounts leaf.profile.count k)) :
    (embeddedSegmentedCertificate P leaf letter dimension hbase hdimension word hword).depth = r :=
  rfl

@[simp] theorem embeddedSegmentedCertificate_word
    (P : PartitionedTensor (K := K) (A := A) V)
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ P.support)
    (dimension : P.support → Leg → ℕ)
    (hbase : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (dimension s .X) (dimension s .Y) (dimension s .Z)))
    (hdimension : ∀ i c, leaf.dimension i c = dimension (letter i) c)
    {r k : ℕ} (word : PositiveWord I r)
    (hword : word ∈ positiveTypeClass I r
      (WordType.proportionalCounts leaf.profile.count k)) :
    (embeddedSegmentedCertificate P leaf letter dimension hbase hdimension word hword).word =
      positiveWordMap letter r word :=
  rfl

@[simp] theorem embeddedSegmentedCertificate_xSize
    (P : PartitionedTensor (K := K) (A := A) V)
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ P.support)
    (dimension : P.support → Leg → ℕ)
    (hbase : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (dimension s .X) (dimension s .Y) (dimension s .Z)))
    (hdimension : ∀ i c, leaf.dimension i c = dimension (letter i) c)
    {r k : ℕ} (word : PositiveWord I r)
    (hword : word ∈ positiveTypeClass I r
      (WordType.proportionalCounts leaf.profile.count k)) :
    (embeddedSegmentedCertificate P leaf letter dimension hbase hdimension word hword).xSize =
      leaf.dimensionProduct .X ^ k :=
  rfl

@[simp] theorem embeddedSegmentedCertificate_ySize
    (P : PartitionedTensor (K := K) (A := A) V)
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ P.support)
    (dimension : P.support → Leg → ℕ)
    (hbase : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (dimension s .X) (dimension s .Y) (dimension s .Z)))
    (hdimension : ∀ i c, leaf.dimension i c = dimension (letter i) c)
    {r k : ℕ} (word : PositiveWord I r)
    (hword : word ∈ positiveTypeClass I r
      (WordType.proportionalCounts leaf.profile.count k)) :
    (embeddedSegmentedCertificate P leaf letter dimension hbase hdimension word hword).ySize =
      leaf.dimensionProduct .Y ^ k :=
  rfl

@[simp] theorem embeddedSegmentedCertificate_zSize
    (P : PartitionedTensor (K := K) (A := A) V)
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ P.support)
    (dimension : P.support → Leg → ℕ)
    (hbase : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (dimension s .X) (dimension s .Y) (dimension s .Z)))
    (hdimension : ∀ i c, leaf.dimension i c = dimension (letter i) c)
    {r k : ℕ} (word : PositiveWord I r)
    (hword : word ∈ positiveTypeClass I r
      (WordType.proportionalCounts leaf.profile.count k)) :
    (embeddedSegmentedCertificate P leaf letter dimension hbase hdimension word hword).zSize =
      leaf.dimensionProduct .Z ^ k :=
  rfl

end RationalTypedLeaf

end AlgebraicComplexity
