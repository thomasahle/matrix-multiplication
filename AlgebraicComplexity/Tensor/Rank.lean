/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.RankCore
import AlgebraicComplexity.Tensor.Product
import AlgebraicComplexity.Tensor.DirectSum

/-!
# Product and direct-sum calculus for tensor rank

The foundational predicate `RankLE`, ordinary tensor rank, and the additive laws are defined in
`Tensor/RankDefs.lean`; the legwise-map, permutation, restriction, and isomorphism laws are added
in `Tensor/RankCore.lean`.  Both are re-exported here.  This module adds the laws whose statements
genuinely require the factorwise external product or direct sum.

Keeping those operations out of the core lets exponent and finite-certificate definitions mention
ordinary rank without loading the larger product/direct-sum tensor environment.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

namespace RankLE

/-- Helper: the external product of one pure tensor with a sum of pure tensors expands term by
term into pure tensors of legwise elementary tensor products. -/
private theorem external_pure_sum (x : ∀ i, V i) (terms : List (∀ i, W i)) :
    external (pure (K := K) x) (terms.map pure).sum =
      (terms.map fun y ↦ pure (K := K) (fun i ↦ x i ⊗ₜ[K] y i)).sum := by
  induction terms with
  | nil => simp
  | cons y terms ih =>
      simp only [List.map_cons, List.sum_cons, external_add_right, external_pure, ih]

/-- Helper: the external product of two sums of pure tensors is the sum of the pure tensors
indexed by all pairs of one term from each list. -/
private theorem external_sums (left : List (∀ i, V i)) (right : List (∀ i, W i)) :
    external (left.map pure).sum (right.map pure).sum =
      ((left.flatMap fun x ↦ right.map fun y ↦ fun i ↦ x i ⊗ₜ[K] y i).map pure).sum := by
  induction left with
  | nil => simp
  | cons x left ih =>
      rw [List.map_cons, List.sum_cons, external_add_left, external_pure_sum, ih]
      simp [Function.comp_def]

/-- Tensor rank is submultiplicative under the factorwise external product.

Proof sketch: decompose `T` into at most `r` pure tensors and `S` into at most `s` pure
tensors.  The external product is bilinear, so it distributes over both sums, and the external
product of two pure tensors is the pure tensor whose leg-`i` entry is the elementary tensor
`x i ⊗ y i`.  The resulting decomposition of `external T S` is indexed by pairs of one term
from each list, hence has length at most `r * s`. -/
theorem external {r s : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : RankLE r T) (hS : RankLE s S) :
    RankLE (r * s) (Tensor.external T S) := by
  rcases hT with ⟨left, hleft, rfl⟩
  rcases hS with ⟨right, hright, rfl⟩
  let pairs : List (∀ i, TensorProduct K (V i) (W i)) :=
    left.flatMap fun x ↦ right.map fun y ↦ fun i ↦ x i ⊗ₜ[K] y i
  refine ⟨pairs, ?_, ?_⟩
  · change pairs.length ≤ r * s
    calc
      pairs.length = left.length * right.length := by simp [pairs]
      _ ≤ r * s := Nat.mul_le_mul hleft hright
  · exact external_sums left right

/-- Tensor rank is subadditive under direct sums. -/
theorem directSum {r s : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : RankLE r T) (hS : RankLE s S) :
    RankLE (r + s) (Tensor.directSum T S) := by
  exact (hT.map includeLeft).add (hS.map includeRight)

end RankLE

/-- Ordinary tensor rank is submultiplicative under the external product:
`rank (external T S) ≤ rank T * rank S`. -/
theorem rank_external_le (T : Tensor3 K V) (S : Tensor3 K W) :
    rank (external T S) ≤ rank T * rank S :=
  rank_le_iff.mpr ((rank_spec T).external (rank_spec S))

/-- Ordinary tensor rank is subadditive under direct sums:
`rank (directSum T S) ≤ rank T + rank S`. -/
theorem rank_directSum_le (T : Tensor3 K V) (S : Tensor3 K W) :
    rank (directSum T S) ≤ rank T + rank S :=
  rank_le_iff.mpr ((rank_spec T).directSum (rank_spec S))

end AlgebraicComplexity.Tensor
