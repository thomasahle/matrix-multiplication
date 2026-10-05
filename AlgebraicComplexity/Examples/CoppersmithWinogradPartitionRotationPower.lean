/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradPartitionRotation
import AlgebraicComplexity.Tensor.PartitionedPowerExternalInterchange

set_option autoImplicit false

/-!
# The CW rotation, moved through positive powers and block cuts

Layer 4 (`AlgebraicComplexity/Examples/`).
`Examples/CoppersmithWinogradPartitionRotation.lean` proves that rotating the legs of the
Coppersmith--Winograd partition returns the same partitioned tensor.  This module carries that
equality where a client needs it: through the positive powers the level-two fine leaf is built
from, and through a block cut of such a power.

The end product is `isomorphic_permute_cycle_rawSquarePower_select`: rotating a cut of a power of
the raw CW square rotates the cut predicate and changes nothing else.  That is exactly the step
which turns `[duan2023faster]`'s `(1,2,1)` and `(2,1,1)` orbit regions into `(1,1,2)` regions with
their `alphatilde` condition on a different leg.

## The paper step this serves

`[duan2023faster]` arXiv:2210.10173, `second_power.tex:235` (`note:T112`) and
`second_power.tex:142-158` (`lem:non-rot-values`, the requirement
`α(1,1,2) = α(1,2,1) = α(2,1,1)`): the paper reads one `V^{(3)}` on all three rotations of
`T_{1,1,2}`.  The statements below are reusable partitioned-tensor infrastructure, not published
claims.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, `[duan2023faster]`, `second_power.tex:142-158`, `:235`; Don Coppersmith and Shmuel
Winograd, *Matrix Multiplication via Arithmetic Progressions*, `[coppersmith1990matrix]`,
pp. 270--272.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u w

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## Letterwise relabelling by the identity

INTEGRATION WINDOW: `positiveWordCongrEquiv_refl` belongs beside `positiveWordCongrEquiv` in
`Tensor/PartitionedPowerExternalInterchange.lean`; it is here only because that module is a
committed file this lane does not edit. -/

/-- Relabelling every letter of a positive word by the identity is the identity. -/
theorem positiveWordCongrEquiv_refl {I : Type w} :
    ∀ n : ℕ, positiveWordCongrEquiv (Equiv.refl I) n = Equiv.refl (PositiveWord I n)
  | 0 => rfl
  | n + 1 => by
      have ih := positiveWordCongrEquiv_refl (I := I) n
      apply Equiv.ext
      rintro ⟨u, a⟩
      show ((positiveWordCongrEquiv (Equiv.refl I) n) u, a) = (u, a)
      rw [ih]
      rfl

/-! ## The rotation, moved through the powers the fine leaf is built from -/

/-- **The raw CW square is invariant under rotating its legs**, as a reindex equivalence along the
identity relabelling. -/
theorem cwSquareRaw_reindexEquiv_permute_cycle :
    (((cwPartitionedTensor K q).positivePower 1).permute cycle).ReindexEquiv
      ((cwPartitionedTensor K q).positivePower 1) (fun _ ↦ Equiv.refl _) := by
  have h := PartitionedTensor.reindexEquiv_permute_positivePower
    (cwPartitionedTensor K q) cycle 1
  rwa [cwPartitionedTensor_permute_cycle] at h

/-- The same, for the inverse rotation. -/
theorem cwSquareRaw_reindexEquiv_permute_cycleSymm :
    (((cwPartitionedTensor K q).positivePower 1).permute cycle.symm).ReindexEquiv
      ((cwPartitionedTensor K q).positivePower 1) (fun _ ↦ Equiv.refl _) := by
  have h := PartitionedTensor.reindexEquiv_permute_positivePower
    (cwPartitionedTensor K q) cycle.symm 1
  rwa [cwPartitionedTensor_permute_cycleSymm] at h

/-- **Every positive power of the raw CW square is invariant under rotating its legs.** -/
theorem cwSquareRawPower_reindexEquiv_permute_cycle (n : ℕ) :
    ((((cwPartitionedTensor K q).positivePower 1).positivePower n).permute cycle).ReindexEquiv
      (((cwPartitionedTensor K q).positivePower 1).positivePower n) (fun _ ↦ Equiv.refl _) := by
  refine PartitionedTensor.ReindexEquiv.congr_equiv ?_
    ((PartitionedTensor.reindexEquiv_permute_positivePower
        ((cwPartitionedTensor K q).positivePower 1) cycle n).trans
      ((cwSquareRaw_reindexEquiv_permute_cycle K q).positivePower n))
  funext _c
  rw [positiveWordCongrEquiv_refl]
  rfl

/-- The same, for the inverse rotation. -/
theorem cwSquareRawPower_reindexEquiv_permute_cycleSymm (n : ℕ) :
    ((((cwPartitionedTensor K q).positivePower 1).positivePower n).permute cycle.symm).ReindexEquiv
      (((cwPartitionedTensor K q).positivePower 1).positivePower n) (fun _ ↦ Equiv.refl _) := by
  refine PartitionedTensor.ReindexEquiv.congr_equiv ?_
    ((PartitionedTensor.reindexEquiv_permute_positivePower
        ((cwPartitionedTensor K q).positivePower 1) cycle.symm n).trans
      ((cwSquareRaw_reindexEquiv_permute_cycleSymm K q).positivePower n))
  funext _c
  rw [positiveWordCongrEquiv_refl]
  rfl

/-! ## The client form: rotating a cut of a power of the raw square -/

/-- **Rotating the legs of a block cut of a power of the raw CW square rotates the cut predicate,
and nothing else.**

This is the form the rotated orbit rows use: the `(1,2,1)` and `(2,1,1)` regions of
`[duan2023faster]`'s fine leaf become, after one rotation, `(1,1,2)` regions whose
`alphatilde` condition sits on a different leg. -/
theorem isomorphic_permute_cycle_rawSquarePower_select (n : ℕ)
    (keep : ∀ _c : Leg, PositiveWord (PositiveWord CWBlock 1) n → Prop)
    [∀ c a, Decidable (keep c a)] :
    Isomorphic
      (Tensor.permute cycle
        ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select keep).realize)
      (((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
        (fun c a ↦ keep (cycle.symm c) a)).realize) := by
  classical
  refine Isomorphic.of_eq
      (PartitionedTensor.permute_realize
        ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select keep) cycle).symm
    |>.trans ?_
  rw [PartitionedTensor.permute_select]
  exact (cwSquareRawPower_reindexEquiv_permute_cycle K q n).isomorphic_select _

/-- The same, for the inverse rotation. -/
theorem isomorphic_permute_cycleSymm_rawSquarePower_select (n : ℕ)
    (keep : ∀ _c : Leg, PositiveWord (PositiveWord CWBlock 1) n → Prop)
    [∀ c a, Decidable (keep c a)] :
    Isomorphic
      (Tensor.permute cycle.symm
        ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select keep).realize)
      (((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
        (fun c a ↦ keep (cycle.symm.symm c) a)).realize) := by
  classical
  refine Isomorphic.of_eq
      (PartitionedTensor.permute_realize
        ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select keep) cycle.symm).symm
    |>.trans ?_
  rw [PartitionedTensor.permute_select]
  exact (cwSquareRawPower_reindexEquiv_permute_cycleSymm K q n).isomorphic_select _

end AlgebraicComplexity.Examples
