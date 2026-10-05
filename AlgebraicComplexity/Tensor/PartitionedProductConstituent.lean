/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedProductCore

set_option autoImplicit false

/-!
# Constituent factorization of a partitioned external product

Layer 1 (`AlgebraicComplexity/Tensor/`).  `Tensor/PartitionedProductCore.lean` defines
`PartitionedTensor.external` and states its two support companions, `mem_external_support` and
`card_external_support`.  The third companion — what the *constituents* of the product are — is
true by construction there and has never been named, so every client so far has had to unfold the
definition with `simp only [PartitionedTensor.external, ...]`.

`constituent_external` names it.  A product constituent at a paired block address is the ordinary
external product of the two factor constituents at the two halves of that address:

`(P.external Q).constituent q = Tensor.external (P.constituent (q ·).1) (Q.constituent (q ·).2)`.

This is the factorization that lets a regional argument build a stage, a weight, or a restriction
for one factor at a time and then multiply: it is what turns the *binary* laws
`Tensor.external`, `HasTauWeight.external` and `WholeConstituentLaserVolumeStage.external` into a
statement about a constituent of the assembled partitioned product, and it is why no `n`-ary
partitioned product has to be named — regions are multiplied in one at a time.

The proof is `rfl`; the value of the lemma is that it is a `simp` lemma with a stable name rather
than a definitional unfolding, so a client rewriting at a product block address does not have to
re-expose `PartitionedTensor.external` and the `blockAddressProductEquiv` support image alongside
it.
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

namespace PartitionedTensor

/-- **The constituents of an external product are external products of constituents.**

Definitional by the construction in `Tensor/PartitionedProductCore.lean`; naming it keeps clients
from unfolding `PartitionedTensor.external` and its support image when all they need is the
tensor at one paired address. -/
@[simp] theorem constituent_external
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (q : BlockAddress (ProductBlockIndex A B)) :
    (P.external Q).constituent q =
      Tensor.external
        (P.constituent fun c ↦ (q c).1)
        (Q.constituent fun c ↦ (q c).2) := rfl

end PartitionedTensor

end AlgebraicComplexity.Tensor
