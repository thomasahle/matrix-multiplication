/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.PositivePowerCoarseningFiberRestriction

set_option autoImplicit false

/-!
# Axiom audit for whole-fiber factorwise restriction

This companion enforces the trust boundary for the composition from a whole positive-power
coarsening fiber to the positive-word tensor of prescribed one-letter targets.
-/

#assert_axioms AlgebraicComplexity.Tensor.Restricts.positivePower_coarseningFiber_restricts_positiveWordTensor

namespace AlgebraicComplexity.Tensor

universe u v w x

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Identity restrictions instantiate every data-carrying hypothesis of the audited theorem. -/
example
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    (n : ℕ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n)) :
    Restricts
      (((P.positivePower n).coarseningFiber
        (fun c ↦ positiveWordMap (f c) n) target).realize)
      (positiveWordTensor
        (fun _address : BlockAddress B ↦
          LegModuleFamily.of.{u, max v w} (K := K)
            (PartitionedSpace K V))
        (fun address ↦ (P.coarseningFiber f address).realize)
        n ((positiveWordBlockAddressEquiv B n).symm target)) :=
  Restricts.positivePower_coarseningFiber_restricts_positiveWordTensor
    P f
    (fun _address : BlockAddress B ↦
      LegModuleFamily.of.{u, max v w} (K := K)
        (PartitionedSpace K V))
    (fun address ↦ (P.coarseningFiber f address).realize)
    (fun address ↦ Restricts.refl ((P.coarseningFiber f address).realize))
    n target

end AlgebraicComplexity.Tensor
