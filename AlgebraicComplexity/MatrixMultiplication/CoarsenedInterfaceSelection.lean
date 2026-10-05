/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorRealization
import AlgebraicComplexity.Tensor.PartitionedCoarseningInterface

/-!
# Complete-split selection after quotienting block labels

This file connects the generic noninjective partition-coarsening API to the complete-split
profile selectors used by recursive laser-method interfaces.  A profile is stated entirely on
the coarse block alphabet through an encoding of each coarse label.  The selected tensor is an
exact restriction of the original tensor power because coarsening is an isomorphism and profile
selection is variable zeroing.

No representative of a coarse fiber is chosen, and the coarsening maps need not be injective.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Universe-explicit selected profile on a coarsened partition. -/
noncomputable abbrev Tensor.PartitionedTensor.selectCoarsenedEncodedCompleteSplitProfiles
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    (encode : ∀ c, B c → SplitWord depth)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1)) :=
  @Tensor.PartitionedTensor.selectEncodedCompleteSplitProfiles.{u, max v w, x}
    K _ depth n B _ _ (CoarsenedBlockSpace (V := V) f) _ _
    (P.coarsen f) encode index profile

/-- Universe-explicit exact interface term on a coarsened partition. -/
noncomputable abbrev Tensor.PartitionedTensor.selectCoarsenedEncodedExactInterfaceTerm
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    (encode : ∀ c, B c → SplitWord depth)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :=
  @Tensor.PartitionedTensor.selectEncodedExactInterfaceTerm.{u, max v w, x}
    K _ depth n B _ _ (CoarsenedBlockSpace (V := V) f) _ _
    (P.coarsen f) encode term hmultiplicity

/-- Select exact complete-split profiles on the coarsened block alphabet directly from a power
of the original realization. -/
theorem Tensor.Restricts.power_partitionedCoarsen_selectEncodedCompleteSplitProfiles
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    (encode : ∀ c, B c → SplitWord depth)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1)) :
    Restricts (Tensor.power P.realize (n + 1))
      (P.selectCoarsenedEncodedCompleteSplitProfiles f encode index profile).realize :=
  (Tensor.Restricts.power_partitionedCoarsen P f (n + 1)).trans
    (Tensor.Restricts.power_selectEncodedCompleteSplitProfiles
      (P.coarsen f) encode index profile)

/-- Exact interface-term form of
`power_partitionedCoarsen_selectEncodedCompleteSplitProfiles`. -/
theorem Tensor.Restricts.power_partitionedCoarsen_selectEncodedExactInterfaceTerm
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    (encode : ∀ c, B c → SplitWord depth)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    Restricts (Tensor.power P.realize (n + 1))
      (P.selectCoarsenedEncodedExactInterfaceTerm f encode term hmultiplicity).realize :=
  (Tensor.Restricts.power_partitionedCoarsen P f (n + 1)).trans
    (Tensor.Restricts.power_selectEncodedExactInterfaceTerm
      (P.coarsen f) encode term hmultiplicity)

end AlgebraicComplexity
