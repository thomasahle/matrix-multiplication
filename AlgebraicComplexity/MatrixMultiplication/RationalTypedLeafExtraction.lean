/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.PartitionedTypeExtraction
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafCore

/-!
# Finite tensor extraction for rational typed leaves

This module keeps partitioned tensor powers out of the lightweight profile, entropy, and dimension
API.  It connects a rational typed leaf to a concrete constituent of a positive partitioned power:
an exact proportional word type restricts to the rectangular matrix-multiplication tensor whose
three dimensions are the corresponding powers of the primitive dimension products.
-/

namespace AlgebraicComplexity

open Tensor

universe v w x y

namespace RationalTypedLeaf

variable {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- The generic finite typed-word matrix-multiplication restriction, specialized to a
proportional rational profile.  No entropy or asymptotic argument enters this theorem. -/
theorem positivePower_constituent_matrixMultiplication_proportional
    {K : Type w} [CommSemiring K]
    {B : Leg → Type x} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
    {V : ∀ c, B c → Type (max w y)}
    [∀ c b, AddCommMonoid (V c b)] [∀ c b, Module K (V c b)]
    (P : PartitionedTensor (K := K) (A := B) V)
    [Nonempty P.support]
    (leaf : RationalTypedLeaf P.support A)
    (hconstituent : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z)))
    {r k : ℕ} (word : PositiveWord P.support r)
    (hword : word ∈ positiveTypeClass P.support r
      (WordType.proportionalCounts leaf.profile.count k)) :
    Restricts ((P.positivePower r).constituent
        (positiveSupportWordBlockAddress P.support r word))
      (matrixMultiplication (K := K)
        (leaf.dimensionProduct .X ^ k)
        (leaf.dimensionProduct .Y ^ k)
        (leaf.dimensionProduct .Z ^ k)) := by
  have h := Tensor.Restricts.positivePower_constituent_matrixMultiplication
    P (fun s ↦ leaf.dimension s .X) (fun s ↦ leaf.dimension s .Y)
      (fun s ↦ leaf.dimension s .Z) hconstituent r word
  rw [positiveWordProduct_eq_prod_pow _ hword,
    positiveWordProduct_eq_prod_pow _ hword,
    positiveWordProduct_eq_prod_pow _ hword] at h
  rw [prod_dimension_proportionalCounts leaf .X k,
    prod_dimension_proportionalCounts leaf .Y k,
    prod_dimension_proportionalCounts leaf .Z k] at h
  exact h

end RationalTypedLeaf

end AlgebraicComplexity
