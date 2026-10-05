/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CyclicProductPowerCoherence
import AlgebraicComplexity.Tensor.PartitionedProduct
import AlgebraicComplexity.Tensor.PartitionedPermutation

/-!
# Partitioned coherence of cyclic orientation products and tensor powers

`CyclicProductPowerCoherence.lean` proves the tensor-only source isomorphism without importing
partitioned tensors.  This file adds the realization theorem needed when a symmetric
partitioned-tensor client first constructs the three-orientation product and then takes its
positive power.  The theorem is paper-independent, basis-free, and valid over a commutative
semiring.
-/

namespace AlgebraicComplexity.Tensor.Isomorphic

open AlgebraicComplexity.Tensor

universe u w x

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {W : ∀ c, A c → Type x}
variable [∀ c a, AddCommMonoid (W c a)] [∀ c a, Module K (W c a)]

/-- The cyclic power product of a realized partition is isomorphic to the corresponding positive
power of the realized three-orientation partitioned product.

This is the representation bridge used by symmetric laser-method clients.  It keeps the
partition structure available for ordinary three-leg hashing while certifying that the source is
the conventional cyclic product used by the value definition.

Proof sketch: first use `cyclicPowerProduct_positive` on the realized tensor.  The realization
theorems for partitioned permutation and external product then identify the three-orientation
ordinary tensor with the realization of the structured three-orientation product; take its
positive power and compose the two isomorphisms. -/
theorem cyclicPowerProduct_partitioned_positive
    (P : PartitionedTensor (K := K) (A := A) W) (n : ℕ) :
    Isomorphic (cyclicPowerProduct K P.realize (n + 1))
      (Tensor.power
        (((P.external (P.permute cycle)).external (P.permute cycle.symm)).realize)
        (n + 1)) := by
  have hcycle :
      Isomorphic (Tensor.permute cycle P.realize) (P.permute cycle).realize :=
    partitionedPermute P cycle
  have hcycleSymm :
      Isomorphic (Tensor.permute cycle.symm P.realize) (P.permute cycle.symm).realize :=
    partitionedPermute P cycle.symm
  have hleft :
      Isomorphic
        (Tensor.external P.realize (Tensor.permute cycle P.realize))
        (P.external (P.permute cycle)).realize :=
    ((Isomorphic.refl P.realize).external hcycle).trans
      (partitionedExternal P (P.permute cycle))
  have hbase :
      Isomorphic
        (Tensor.external
          (Tensor.external P.realize (Tensor.permute cycle P.realize))
          (Tensor.permute cycle.symm P.realize))
        (((P.external (P.permute cycle)).external (P.permute cycle.symm)).realize) :=
    (hleft.external hcycleSymm).trans
      (partitionedExternal (P.external (P.permute cycle)) (P.permute cycle.symm))
  exact (cyclicPowerProduct_positive P.realize n).trans (hbase.power (n + 1))

end AlgebraicComplexity.Tensor.Isomorphic
