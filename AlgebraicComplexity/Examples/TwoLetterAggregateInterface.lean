/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TwoLetterAggregateInterface

/-!
# Semantic smoke test for unequal aggregate interfaces

Two distinct supported constituents are each duplicated in separate regional words.  Their
external product is nevertheless isomorphic to two copies of the balanced two-letter word.
This is the smallest genuinely unequal instance of the aggregate-interface theorem.
-/

namespace AlgebraicComplexity.Examples

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- The external product of the words `aa` and `bb` has the same interface tensor as two copies
of `ab`, even though `aa` and `bb` each have a different empirical marginal from `ab`. -/
theorem duplicatedEndpoints_isomorphic_balancedPair
    (P : PartitionedTensor (K := K) (A := A) V)
    (a b : P.support) (hab : a ≠ b) :
    Isomorphic
      (Tensor.external
        (P.positiveSupportWordTensor 1 (positiveWordConst a 1))
        (P.positiveSupportWordTensor 1 (positiveWordConst b 1)))
      (Tensor.external
        (P.positiveSupportWordTensor 1 (WordType.positiveWordPair a b))
        (P.positiveSupportWordTensor 1 (WordType.positiveWordPair a b))) := by
  let row : PositiveWord P.support 1 := positiveWordConst a 1
  let column : PositiveWord P.support 1 := positiveWordConst b 1
  let base : PositiveWord P.support 1 := WordType.positiveWordPair a b
  have hrow : WordType.positiveMultiplicity row =
      fun i ↦ if i = a then 2 else 0 := by
    simpa [row] using WordType.positiveMultiplicity_const a 1
  have hcolumn : WordType.positiveMultiplicity column =
      fun i ↦ if i = b then 2 else 0 := by
    simpa [column] using WordType.positiveMultiplicity_const b 1
  have hbase : WordType.positiveMultiplicity base =
      fun i ↦ (if i = a then 1 else 0) + (if i = b then 1 else 0) := by
    simpa [base] using WordType.positiveMultiplicity_pair a b
  have haggregate : WordType.HasAggregateInterface row column base := by
    intro i
    rw [hrow, hcolumn, hbase]
    by_cases hia : i = a
    · subst i
      simp [hab]
    · by_cases hib : i = b <;> simp [hia, hib, Ne.symm hab]
  have hunequal : WordType.positiveMultiplicity row ≠
      WordType.positiveMultiplicity base := by
    intro heq
    have ha := congrFun heq a
    rw [hrow, hbase] at ha
    simp [hab] at ha
  simpa only [row, column, base] using
    Tensor.Isomorphic.external_positiveSupportWordTensor_unequalAggregateInterface
      P 1 row column base ⟨haggregate, Or.inl hunequal⟩

end AlgebraicComplexity.Examples
