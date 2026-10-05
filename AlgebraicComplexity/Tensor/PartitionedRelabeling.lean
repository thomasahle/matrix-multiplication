/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.HoleRepair
import AlgebraicComplexity.Tensor.PartitionedProduct

/-!
# Product closure for structure-preserving partition relabelings

This module supplies the categorical operations used to build chunk permutations.  Independent
structure-preserving relabelings act on an external product componentwise, while the external
square of any partitioned tensor admits the factor-swap relabeling.

The definitions are kept separate from the generic hole-repair module: hole repair only consumes
an abstract `StructureRelabeling`, whereas tensor-power clients need these concrete constructors.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x y

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {B : Leg → Type x} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {W : ∀ c, B c → Type y}
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

namespace PartitionedTensor.StructureRelabeling

variable {P : PartitionedTensor (K := K) (A := A) V}
variable {Q : PartitionedTensor (K := K) (A := B) W}

/-- A structure-preserving relabeling restricts to any variable selection whose legwise keep
predicates are invariant under that relabeling. -/
noncomputable def select
    (r : P.StructureRelabeling)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)]
    (hinvariant : ∀ c a, keep c ((r.partEquiv c).symm a) ↔ keep c a) :
    (P.select keep).StructureRelabeling where
  partEquiv := r.partEquiv
  blockEquiv := r.blockEquiv
  invariant := by
    rw [P.reindex_select, r.invariant]
    congr 1
    funext c a
    exact propext (hinvariant c a)

/-- Independent structure-preserving relabelings act componentwise on an external product. -/
noncomputable def external
    (r : P.StructureRelabeling) (s : Q.StructureRelabeling) :
    (P.external Q).StructureRelabeling where
  partEquiv := fun c ↦ Equiv.prodCongr (r.partEquiv c) (s.partEquiv c)
  blockEquiv := fun c q ↦
    TensorProduct.congr (r.blockEquiv c q.1) (s.blockEquiv c q.2)
  invariant := by
    rw [PartitionedTensor.external_reindex, r.invariant, s.invariant]

/-- Swap the two factors of the external square of a partitioned tensor. -/
noncomputable def externalSelfComm
    (P : PartitionedTensor (K := K) (A := A) V) :
    (P.external P).StructureRelabeling where
  partEquiv := productBlockCommEquiv (A := A) (B := A)
  blockEquiv := productBlockSpaceCommEquiv (K := K) (V := V) (W := V)
  invariant := PartitionedTensor.external_reindex_comm P P

end PartitionedTensor.StructureRelabeling
end AlgebraicComplexity.Tensor
