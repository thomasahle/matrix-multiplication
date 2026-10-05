/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafExtraction

/-!
# Polynomial-degeneration adapter for rational typed leaves

`RationalTypedLeaf.lean` contains the basic profile, entropy, dimension, and exact-restriction
calculus.  This companion keeps the stronger polynomial-degeneration lifting theorem behind a
small adapter boundary.  A constituent relation may therefore be exact restriction, zeroing,
monomial degeneration, or an interpolation certificate; all of them produce the same proportional
matrix dimensions once their semantic degeneration witnesses are supplied.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x y

namespace RationalTypedLeaf

variable {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- Lift arbitrary polynomial degenerations of the base constituents through a supported word.

The external-product degeneration theorem handles one letter at a time, and the proportional
type identity turns the resulting dimension products into the leaf's exact `k`th powers.  This is
the degeneration-parametric sibling of
`positivePower_constituent_matrixMultiplication_proportional`.
-/
theorem positivePower_constituent_matrixMultiplication_proportional_of_polynomialDegenerates
    {K : Type u} [CommSemiring K]
    {B : Leg → Type w} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
    {V : ∀ c, B c → Type (max u x)}
    [∀ c b, AddCommMonoid (V c b)] [∀ c b, Module K (V c b)]
    (P : PartitionedTensor (K := K) (A := B) V)
    [Nonempty P.support]
    (leaf : RationalTypedLeaf P.support A)
    (hconstituent : ∀ s : P.support,
      PolynomialDegenerates (P.constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z)))
    {r k : ℕ} (word : PositiveWord P.support r)
    (hword : word ∈ positiveTypeClass P.support r
      (WordType.proportionalCounts leaf.profile.count k)) :
    PolynomialDegenerates ((P.positivePower r).constituent
        (positiveSupportWordBlockAddress P.support r word))
      (matrixMultiplication (K := K)
        (leaf.dimensionProduct .X ^ k)
        (leaf.dimensionProduct .Y ^ k)
        (leaf.dimensionProduct .Z ^ k)) := by
  have h := Tensor.PolynomialDegenerates.positivePower_constituent_matrixMultiplication
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
