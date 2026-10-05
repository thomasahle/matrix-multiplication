/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.PartitionedTypeAssembly
import AlgebraicComplexity.Tensor.PartitionedPower

set_option autoImplicit false

/-!
# Reindexing heterogeneous positive-word tensor products

A `Tensor.positiveWordTensor W T n word` is the left-associated external product of the
possibly different tensors named by `word`.  This module proves that its isomorphism class
depends only on the multiplicity of every letter, not on their order.

The proof packages the heterogeneous family temporarily as the diagonal support of a partitioned
tensor.  The existing common-position relabeling theorem for constituents of a partitioned power
then performs the permutation, after which the auxiliary packaging is removed.  This keeps the
`WordType` dependency in layer 3; no combinatorial import is added to the tensor foundation.

The immediate paper use is purely structural.  The six region-major products in
[dupont2026improving, Section 2], `papers/sources/2608.16884/main.tex:499-545`, must be reordered
before the one global level-two extraction is applied.  This theorem licenses only that
reordering.  It proves no support identity, hashing estimate, whole-fiber survival, `E₂` count,
or tensor restriction for the Total-Weight construction.

## Reference

- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {I : Type w} [Fintype I] [DecidableEq I]

namespace Tensor

section DiagonalPartition

variable (W : I → LegModuleFamily.{u, v} K)
variable (T : ∀ i, Tensor3 K (W i).Space)

/-- Put one heterogeneous factor at the same label on all three legs. -/
private def wordTensorDiagonalAddress (i : I) :
    BlockAddress (fun _c : Leg ↦ I) :=
  fun _c ↦ i

/-- The diagonal-address map is injective. -/
private def wordTensorDiagonalEmbedding :
    I ↪ BlockAddress (fun _c : Leg ↦ I) where
  toFun := wordTensorDiagonalAddress
  inj' := by
    intro i j hij
    exact congrFun hij .X

/-- Extend a heterogeneous factor family by zero away from diagonal addresses.

At a diagonal address this is the corresponding tensor `T i`, transported only by the
proof-level casts needed by the dependent block-space type. -/
private noncomputable def wordTensorDiagonalConstituent
    (address : BlockAddress (fun _c : Leg ↦ I)) :
    Tensor3 K (fun c ↦ (W (address c)).Space c) :=
  if haddress : wordTensorDiagonalAddress (address .X) = address then
    Tensor.map (fun c ↦
      (LinearEquiv.cast (R := K)
        (M := fun i ↦ (W i).Space c)
        (congrFun haddress c)).toLinearMap)
      (T (address .X))
  else
    0

/-- Auxiliary partition whose supported constituents are exactly the tensors `T i`, on diagonal
block addresses. -/
private noncomputable def wordTensorDiagonalPartition :
    PartitionedTensor (K := K) (A := fun _c : Leg ↦ I)
      (fun c i ↦ (W i).Space c) where
  support := Finset.univ.map wordTensorDiagonalEmbedding
  constituent := wordTensorDiagonalConstituent W T

/-- Every family index gives a supported diagonal address in the auxiliary partition. -/
private noncomputable def wordTensorDiagonalSupport (i : I) :
    (wordTensorDiagonalPartition W T).support :=
  ⟨wordTensorDiagonalAddress i, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

omit [Fintype I] in
/-- The auxiliary constituent at a diagonal address is the original heterogeneous tensor. -/
private theorem wordTensorDiagonalConstituent_diagonal (i : I) :
    wordTensorDiagonalConstituent W T (wordTensorDiagonalAddress i) = T i := by
  unfold wordTensorDiagonalConstituent
  rw [dif_pos (show wordTensorDiagonalAddress
    ((wordTensorDiagonalAddress i) .X) = wordTensorDiagonalAddress i by rfl)]
  change Tensor.map (fun c ↦ LinearMap.id (R := K) (M := (W i).Space c)) (T i) = T i
  rw [Tensor.map_id]
  rfl

/-- Reading the auxiliary partition at its bundled diagonal support address recovers `T i`. -/
private theorem wordTensorDiagonalPartition_constituent (i : I) :
    (wordTensorDiagonalPartition W T).constituent
        (wordTensorDiagonalSupport W T i).1 = T i := by
  change wordTensorDiagonalConstituent W T (wordTensorDiagonalAddress i) = T i
  exact wordTensorDiagonalConstituent_diagonal W T i

/-- Lifting every letter to the diagonal support turns the partitioned word tensor back into the
original heterogeneous word tensor. -/
private theorem positiveSupportWordTensor_diagonal
    (n : ℕ) (word : PositiveWord I n) :
    Isomorphic
      ((wordTensorDiagonalPartition W T).positiveSupportWordTensor n
        (positiveWordMap (wordTensorDiagonalSupport W T) n word))
      (positiveWordTensor W T n word) := by
  induction n with
  | zero =>
      exact Isomorphic.of_eq (wordTensorDiagonalPartition_constituent W T word)
  | succ n ih =>
      rcases word with ⟨initial, last⟩
      exact Isomorphic.external (ih initial)
        (Isomorphic.of_eq (wordTensorDiagonalPartition_constituent W T last))

end DiagonalPartition

namespace Isomorphic

/-- Heterogeneous positive-word products with the same letter multiplicities are isomorphic.

In human-readable terms, an external product of a finite multiset of tensors does not depend on
the order in which those tensors are written.  Unlike the existing partitioned-tensor version,
the factor spaces and tensors here may depend directly on the letter.

Proof sketch: embed every factor as a diagonal constituent of an auxiliary partitioned tensor.
Mapping a word into this diagonal support preserves equality of multiplicity profiles.  Apply the
common-position relabeling theorem to the two resulting constituents of the same partitioned
power, rewrite those constituents as positive support-word tensors, and finally erase the
diagonal packaging factor by factor. -/
theorem positiveWordTensor_of_same_multiplicity
    (W : I → LegModuleFamily.{u, v} K)
    (T : ∀ i, Tensor3 K (W i).Space)
    (n : ℕ) (left right : PositiveWord I n)
    (htype :
      WordType.multiplicity (positiveWordEquiv I n left) =
        WordType.multiplicity (positiveWordEquiv I n right)) :
    Isomorphic (positiveWordTensor W T n left)
      (positiveWordTensor W T n right) := by
  have hliftedType :
      WordType.multiplicity
          (positiveWordEquiv (wordTensorDiagonalPartition W T).support n
            (positiveWordMap (wordTensorDiagonalSupport W T) n left)) =
        WordType.multiplicity
          (positiveWordEquiv (wordTensorDiagonalPartition W T).support n
            (positiveWordMap (wordTensorDiagonalSupport W T) n right)) := by
    rw [positiveWordEquiv_map, positiveWordEquiv_map,
      WordType.multiplicity_comp_eq_mappedType,
      WordType.multiplicity_comp_eq_mappedType, htype]
  have h := Tensor.Isomorphic.positivePower_constituent_of_same_type
    (wordTensorDiagonalPartition W T) n
    (positiveWordMap (wordTensorDiagonalSupport W T) n left)
    (positiveWordMap (wordTensorDiagonalSupport W T) n right) hliftedType
  rw [PartitionedTensor.positivePower_constituent_positiveSupportWordBlockAddress
      (wordTensorDiagonalPartition W T) n
        (positiveWordMap (wordTensorDiagonalSupport W T) n left),
    PartitionedTensor.positivePower_constituent_positiveSupportWordBlockAddress
      (wordTensorDiagonalPartition W T) n
        (positiveWordMap (wordTensorDiagonalSupport W T) n right)] at h
  exact (positiveSupportWordTensor_diagonal W T n left).symm.trans
    (h.trans (positiveSupportWordTensor_diagonal W T n right))

end Isomorphic

end Tensor

end AlgebraicComplexity
