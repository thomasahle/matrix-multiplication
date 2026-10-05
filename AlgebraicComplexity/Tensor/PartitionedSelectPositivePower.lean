/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedPowerConstituent

set_option autoImplicit false

/-!
# Block selection leaves the constituents of a positive power alone

Layer 1 (`AlgebraicComplexity/Tensor/`).  `PartitionedTensor.select`
(`Tensor/PartitionedCore.lean`) filters the support and keeps the constituent family verbatim, so
a positive power of a selected partitioned tensor carries exactly the constituents of the positive
power of the whole.

The equality is **not** definitional for a variable exponent: `PartitionedTensor.positivePower`
recurses on the exponent, so the two sides only reduce against each other once the exponent is a
literal.  One induction settles it, and clients then move freely between the two spellings.

## Who needs it

A client that compares a *type cut* of a partitioned power with a cut of a second partitioned
tensor states the cut on the whole power --- a `select` of `P.positivePower n`, whose constituents
are literally `(P.positivePower n).constituent` --- while the letter-level blockwise data it owns
lives on the selected letters, hence on `(P.select keep).positivePower n`.  The constituent
hypothesis of `Tensor.Restricts.partitionedBlockMap` is exactly where the two meet.

Primary source: none; this is partitioned-tensor infrastructure.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **Selecting blocks leaves every constituent of a positive power unchanged.**

Proof sketch: induction on the exponent.  At `0` both powers are the underlying tensor and
`select` copies the constituent field.  At a successor both are the same external product, with
the inductive hypothesis on the prefix and the `select` field equation on the last letter. -/
theorem PartitionedTensor.positivePower_select_constituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    ∀ n : ℕ, ((P.select keep).positivePower n).constituent =
      (P.positivePower n).constituent
  | 0 => rfl
  | n + 1 => by
      have ih := PartitionedTensor.positivePower_select_constituent P keep n
      funext s
      show Tensor.external
          (((P.select keep).positivePower n).constituent fun c ↦ (s c).1)
          ((P.select keep).constituent fun c ↦ (s c).2) =
        Tensor.external ((P.positivePower n).constituent fun c ↦ (s c).1)
          (P.constituent fun c ↦ (s c).2)
      rw [ih]
      rfl

end AlgebraicComplexity.Tensor
