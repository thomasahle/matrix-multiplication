/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedProductCore
import AlgebraicComplexity.Tensor.PositiveWordInstances

/-!
# Constituents of positive powers of partitioned tensors

This module is the lightweight semantic core of partitioned tensor powers.  It defines the
recursively paired block spaces and partition, transposes a supported address word legwise, and
identifies the selected constituent with the corresponding iterated external product.

Support enumeration, word concatenation, reassociation, cardinality, and comparison with
canonical tensor powers live in `Tensor.PartitionedPower`.  Clients that only construct explicit
maps on one selected constituent should import this module instead.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- A module family indexed by a block label on every tensor leg.  Packaging the instances avoids
dependent typeclass recursion when the labels themselves are recursively parenthesized words. -/
structure BlockModuleFamily (K : Type u) [CommSemiring K]
    (A : Leg → Type w) where
  Space : ∀ c, A c → Type (max u v)
  [addCommMonoid : ∀ c a, AddCommMonoid (Space c a)]
  [module : ∀ c a, Module K (Space c a)]

attribute [instance] BlockModuleFamily.addCommMonoid BlockModuleFamily.module

namespace BlockModuleFamily

/-- Package an ordinary block-space family. -/
def of (V : ∀ c, A c → Type (max u v))
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)] :
    BlockModuleFamily.{u, v, w} K A where
  Space := V

/-- Pair corresponding blocks and tensor their spaces. -/
@[reducible] def external
    {B : Leg → Type w}
    (P : BlockModuleFamily.{u, v, w} K A)
    (Q : BlockModuleFamily.{u, v, w} K B) :
    BlockModuleFamily.{u, v, w} K (ProductBlockIndex A B) where
  Space c q := TensorProduct K (P.Space c q.1) (Q.Space c q.2)

/-- Packaged block spaces selected by a positive word.  Parameter `n` represents `n + 1`
original blocks. -/
@[reducible] def positivePower (P : BlockModuleFamily.{u, v, w} K A) :
    (n : ℕ) → BlockModuleFamily.{u, v, w} K (fun c ↦ PositiveWord (A c) n)
  | 0 => P
  | n + 1 => (positivePower P n).external P

end BlockModuleFamily

/-- The block space selected by a positive word of block labels. -/
abbrev PositivePowerBlockSpace (K : Type u) [CommSemiring K]
    (V : ∀ c, A c → Type (max u v))
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
  (n : ℕ) := (BlockModuleFamily.positivePower
      (BlockModuleFamily.of (K := K) V) n).Space

/-- Transpose a word of supported full addresses into its three words of block labels. -/
def positiveSupportWordBlockAddress
    (support : Finset (BlockAddress A)) :
    (n : ℕ) → PositiveWord support n →
      BlockAddress (fun c ↦ PositiveWord (A c) n)
  | 0, q => q.1
  | n + 1, q => fun c ↦
      (positiveSupportWordBlockAddress support n q.1 c, q.2.1 c)

namespace PartitionedTensor

/-- Positive partitioned power.  Its support is formed recursively by Cartesian products, with
full addresses transposed into a word of labels independently on every tensor leg. -/
noncomputable def positivePower
    (P : PartitionedTensor (K := K) (A := A) V) :
    (n : ℕ) → PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n)
      (PositivePowerBlockSpace K V n)
  | 0 =>
      { support := P.support
        constituent := P.constituent }
  | n + 1 =>
      let Q := (positivePower P n).external P
      { support := Q.support
        constituent := Q.constituent }

@[simp] theorem positivePower_zero
    (P : PartitionedTensor (K := K) (A := A) V) :
    P.positivePower 0 = P := by
  cases P
  rfl

@[simp] theorem positivePower_succ
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) :
    P.positivePower (n + 1) = (P.positivePower n).external P := by
  rfl

/-- The iterated external product selected by a word of supported source addresses, with its
result type expressed directly in the block spaces of `positivePower`. -/
def positiveSupportWordTensor
    (P : PartitionedTensor (K := K) (A := A) V) :
    (n : ℕ) → (q : PositiveWord P.support n) →
      Tensor3 K (fun c ↦ PositivePowerBlockSpace K V n c
        (positiveSupportWordBlockAddress P.support n q c))
  | 0, q => P.constituent q.1
  | n + 1, q => Tensor.external
      (positiveSupportWordTensor P n q.1) (P.constituent q.2.1)

@[simp] theorem positiveSupportWordTensor_zero
    (P : PartitionedTensor (K := K) (A := A) V) (q : PositiveWord P.support 0) :
    positiveSupportWordTensor P 0 q = P.constituent q.1 := rfl

@[simp] theorem positiveSupportWordTensor_succ
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (q : PositiveWord P.support (n + 1)) :
    positiveSupportWordTensor P (n + 1) q = Tensor.external
      (positiveSupportWordTensor P n q.1) (P.constituent q.2.1) := rfl

/-- The constituent at a supported address word is the iterated external product of the source
constituents in that word. -/
theorem positivePower_constituent_positiveSupportWordBlockAddress
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (q : PositiveWord P.support n) :
    (P.positivePower n).constituent
        (positiveSupportWordBlockAddress P.support n q) =
      positiveSupportWordTensor P n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rcases q with ⟨q, s⟩
      change Tensor.external
          ((P.positivePower n).constituent
            (positiveSupportWordBlockAddress P.support n q))
          (P.constituent s.1) =
        Tensor.external
          (positiveSupportWordTensor P n q)
          (P.constituent s.1)
      rw [ih q]

end PartitionedTensor

end AlgebraicComplexity.Tensor
