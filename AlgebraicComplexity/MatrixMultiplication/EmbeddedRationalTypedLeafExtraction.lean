/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordType
import AlgebraicComplexity.MatrixMultiplication.ExternalProduct
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafCore
import AlgebraicComplexity.Tensor.PartitionedPower
import AlgebraicComplexity.Tensor.TypeExtraction

set_option autoImplicit false

/-!
# Rational typed leaves on a sparse embedded alphabet

`PositiveIntegralProfile` is intentionally strictly positive: zero-mass letters are removed from
its alphabet.  A partitioned tensor, however, can have a vastly larger support than the support of
one certificate type.  Requiring a `RationalTypedLeaf` on the entire partition support therefore
forces fictitious positive counts on structural zeroes.

This module supplies the missing adapter.  A rational typed leaf may live on any finite alphabet
`I`, together with an embedding `letter : I ↪ P.support`.  Its proportional word is mapped into
the ambient partition support, and the ordinary constituent-product theorem then gives exactly the
same rectangular matrix-multiplication tensor.  No positivity is asserted outside the image.
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

/-- Product of a numerical quantity along a word on the sparse leaf alphabet. -/
def embeddedWordDimension (value : I → ℕ) :
    (r : ℕ) → PositiveWord I r → ℕ
  | 0, i => value i
  | r + 1, word => embeddedWordDimension value r word.1 * value word.2

omit [Fintype I] [Nonempty I] in
@[simp] theorem embeddedWordDimension_zero
    (value : I → ℕ) (i : PositiveWord I 0) :
    embeddedWordDimension value 0 i = value i := rfl

omit [Fintype I] [Nonempty I] in
@[simp] theorem embeddedWordDimension_succ
    (value : I → ℕ) (r : ℕ) (word : PositiveWord I (r + 1)) :
    embeddedWordDimension value (r + 1) word =
      embeddedWordDimension value r word.1 * value word.2 := rfl

omit [Fintype I] [Nonempty I] in
/-- The recursive sparse-word product is the product over its function-word presentation. -/
theorem embeddedWordDimension_eq_fin_prod
    (value : I → ℕ) (r : ℕ) (word : PositiveWord I r) :
    embeddedWordDimension value r word =
      ∏ position, value (positiveWordEquiv I r word position) := by
  induction r with
  | zero =>
      rw [embeddedWordDimension_zero, Fin.prod_univ_one]
      exact congrArg value
        (congrFun (positiveWordEquiv_zero_apply I word) 0).symm
  | succ r ih =>
      rw [embeddedWordDimension_succ, ih word.1,
        positiveWordEquiv_succ_apply]
      let headWord : Fin (r + 1) → I := positiveWordEquiv I r word.1
      let last : I := word.2
      have hcomp :
          (fun position : Fin (r + 2) ↦
            value ((Fin.snoc headWord last : Fin (r + 2) → I) position)) =
          (Fin.snoc (fun position : Fin (r + 1) ↦ value (headWord position))
            (value last) : Fin (r + 2) → ℕ) := by
        funext position
        refine Fin.lastCases ?_ (fun earlier ↦ ?_) position <;> simp
      change
        (∏ position, value (headWord position)) * value last =
          ∏ position, value ((Fin.snoc headWord last : Fin (r + 2) → I) position)
      rw [hcomp, Fin.prod_snoc]

omit [Nonempty I] in
/-- A sparse-word dimension product depends only on its multiplicity type. -/
theorem embeddedWordDimension_eq_prod_pow
    (value : I → ℕ) {r : ℕ} {profile : I → ℕ}
    (word : PositiveWord I r)
    (hword : word ∈ positiveTypeClass I r profile) :
    embeddedWordDimension value r word = ∏ i, value i ^ profile i := by
  rw [embeddedWordDimension_eq_fin_prod,
    WordType.prod_word_eq_prod_pow, mem_positiveTypeClass.mp hword]

omit [Fintype I] [Nonempty I] in
/-- Exact constituent products may be iterated over a word on a sparse alphabet embedded in the
ambient partition support. -/
theorem positiveSupportWordTensor_matrixMultiplication_embedded
    (P : PartitionedTensor (K := K) (A := A) V)
    (letter : I ↪ P.support)
    (dimension : P.support → Leg → ℕ)
    (hbase : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (dimension s .X) (dimension s .Y) (dimension s .Z))) :
    ∀ (r : ℕ) (word : PositiveWord I r),
      Restricts
        (P.positiveSupportWordTensor r (positiveWordMap letter r word))
        (matrixMultiplication (K := K)
          (embeddedWordDimension (fun i ↦ dimension (letter i) .X) r word)
          (embeddedWordDimension (fun i ↦ dimension (letter i) .Y) r word)
          (embeddedWordDimension (fun i ↦ dimension (letter i) .Z) r word)) := by
  intro r
  induction r with
  | zero =>
      intro word
      exact hbase (letter word)
  | succ r ih =>
      intro word
      exact
        ((ih word.1).external (hbase (letter word.2))).trans
          (Tensor.Isomorphic.matrixMultiplication_externalProduct
            (K := K)
            (embeddedWordDimension (fun i ↦ dimension (letter i) .X) r word.1)
            (embeddedWordDimension (fun i ↦ dimension (letter i) .Y) r word.1)
            (embeddedWordDimension (fun i ↦ dimension (letter i) .Z) r word.1)
            (dimension (letter word.2) .X)
            (dimension (letter word.2) .Y)
            (dimension (letter word.2) .Z)).restricts

omit [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)] in
/-- A proportional typed-leaf word embedded in a larger partition support yields the expected
rectangular constituent.

The ambient dimension table and its constituent restrictions are required on the whole partition
support, while `hdimension` identifies them with the sparse leaf only on the embedded alphabet.
Thus no count, probability, or semantic certificate is invented for an unused ambient letter. -/
theorem positivePower_constituent_matrixMultiplication_proportional_embedded
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
      ((P.positivePower r).constituent
        (positiveSupportWordBlockAddress P.support r
          (positiveWordMap letter r word)))
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
  rw [P.positivePower_constituent_positiveSupportWordBlockAddress]
  rw [product_eq .X, product_eq .Y, product_eq .Z] at hwordTensor
  exact hwordTensor

end RationalTypedLeaf

end AlgebraicComplexity
