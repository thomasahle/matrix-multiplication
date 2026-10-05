/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordType
import AlgebraicComplexity.Tensor.PartitionedPowerRelabeling

/-!
# Reordering typed constituents of partitioned tensor powers

Word-type extraction counts supported address words only through their letter multiplicities.
Tensor assembly, however, often needs one convenient representative in which equal constituent
kinds occur in consecutive chunks.  This module supplies the semantic bridge: two supported
address words of the same multiplicity type index isomorphic constituents of the partitioned
power.

This belongs above the tensor foundation because it combines the tensor position-relabeling API
with the finite word-type combinatorics.  It is independent of Coppersmith--Winograd tensors,
matrix dimensions, hashing, and entropy.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

namespace WordType

/-- Multiplicities of a concatenated pair of nonempty recursive words add pointwise. -/
theorem multiplicity_positiveWordAppend
    {I : Type*} [Fintype I]
    (left : PositiveWord I n) (right : PositiveWord I m) :
    multiplicity
        (positiveWordEquiv I (n + m + 1)
          (positiveWordAppend left m right)) =
      multiplicity (positiveWordEquiv I n left) +
        multiplicity (positiveWordEquiv I m right) := by
  rw [positiveWordEquiv_append]
  exact (multiplicity_cast (by omega)
    (Fin.append (positiveWordEquiv I n left)
      (positiveWordEquiv I m right))).trans
        (multiplicity_append _ _)

/-- Exact multiplicity vector of a constant positive word of length `n + 1`. -/
theorem multiplicity_positiveWordConst
    {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (n : ℕ) :
    multiplicity (positiveWordEquiv I n (positiveWordConst i n)) =
      fun j ↦ if j = i then n + 1 else 0 := by
  rw [positiveWordEquiv_const]
  funext j
  exact multiplicity_const (n + 1) i j

/-- Casting the recursive parameter of a positive word does not change its multiplicity type. -/
theorem multiplicity_positiveWordCast
    {I : Type*} [Fintype I] {n m : ℕ}
    (h : n = m) (word : PositiveWord I n) :
    multiplicity (positiveWordEquiv I m (positiveWordCast h word)) =
      multiplicity (positiveWordEquiv I n word) := by
  subst m
  rfl

end WordType

namespace Tensor.Isomorphic

/-- Supported words with the same letter multiplicities select isomorphic constituents of a
partitioned tensor power.

The multiplicity is taken on full support addresses, rather than independently on the three
legs.  Consequently the chosen position permutation is common to all legs and is realized by a
genuine structure-preserving tensor relabeling.

Proof sketch: `WordType.positionPermOfSameMultiplicity` produces a position permutation `e`
with `right ∘ e = left`.  Hence applying `e⁻¹` to the positions of `left` gives `right`.
The generic positive-power position relabeling then supplies the required constituent
isomorphism. -/
theorem positivePower_constituent_of_same_type
    (P : PartitionedTensor (K := K) (A := A) V)
    (r : ℕ) (left right : PositiveWord P.support r)
    (htype :
      WordType.multiplicity (positiveWordEquiv P.support r left) =
        WordType.multiplicity (positiveWordEquiv P.support r right)) :
    Isomorphic
      ((P.positivePower r).constituent
        (positiveSupportWordBlockAddress P.support r left))
      ((P.positivePower r).constituent
        (positiveSupportWordBlockAddress P.support r right)) := by
  let leftFunction := positiveWordEquiv P.support r left
  let rightFunction := positiveWordEquiv P.support r right
  let e := WordType.positionPermOfSameMultiplicity
    leftFunction rightFunction htype
  have he : rightFunction ∘ e = leftFunction :=
    WordType.positionPermOfSameMultiplicity_map
      leftFunction rightFunction htype
  have he' : leftFunction ∘ e.symm = rightFunction := by
    funext i
    have hi := congrFun he (e.symm i)
    simpa [Function.comp_apply] using hi.symm
  have hword :
      positiveWordPositionEquiv P.support r e.symm left = right := by
    apply (positiveWordEquiv P.support r).injective
    rw [positiveWordEquiv_position_apply]
    exact he'
  have h := PartitionedTensor.StructureRelabeling.positivePower_constituent_isomorphic_position
    P r e.symm left
  rwa [hword] at h

end Tensor.Isomorphic
end AlgebraicComplexity
