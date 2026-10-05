/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Basic

/-!
# Finite support data for partitioned tensors

This module contains only the typed support certificate carried by a partitioned tensor.  Ambient
direct sums, realization maps, and semantic zeroing live in `Tensor.Partitioned`, which re-exports
this core.  Keeping the data layer independent of direct-sum realization lets finite type and
constituent clients elaborate without loading border-rank infrastructure.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- An address chooses one partition block on each tensor leg. -/
abbrev BlockAddress (A : Leg → Type w) := ∀ c, A c

/-- A finite, typed support decomposition of a tensor. -/
structure PartitionedTensor
    (K : Type u) [CommSemiring K]
    (A : Leg → Type w) [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (V : ∀ c, A c → Type v)
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)] where
  support : Finset (BlockAddress A)
  constituent : ∀ s : BlockAddress A, Tensor3 K (fun c ↦ V c (s c))

namespace PartitionedTensor

/-- Extensionality for the certificate data of a partitioned tensor. -/
@[ext] theorem ext
    {P Q : PartitionedTensor (K := K) (A := A) V}
    (hsupport : P.support = Q.support)
    (hconstituent : P.constituent = Q.constituent) : P = Q := by
  cases P
  cases Q
  cases hsupport
  cases hconstituent
  rfl

/-- Keep only addresses whose block survives independently on all three legs. -/
def select (P : PartitionedTensor (K := K) (A := A) V)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    PartitionedTensor (K := K) (A := A) V where
  support := P.support.filter fun s ↦ ∀ c, keep c (s c)
  constituent := P.constituent

@[simp] theorem mem_select_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)]
    (s : BlockAddress A) :
    s ∈ (P.select keep).support ↔ s ∈ P.support ∧ ∀ c, keep c (s c) := by
  exact Finset.mem_filter

end PartitionedTensor

/-- A support is tight if injective integer labels on each leg have constant total weight on every
supported address. -/
def IsTightSupport (support : Finset (BlockAddress A)) : Prop :=
  ∃ weight : ∀ c, A c → ℤ,
    (∀ c, Function.Injective (weight c)) ∧
      ∃ D : ℤ, ∀ s ∈ support, ∑ c, weight c (s c) = D

end AlgebraicComplexity.Tensor
