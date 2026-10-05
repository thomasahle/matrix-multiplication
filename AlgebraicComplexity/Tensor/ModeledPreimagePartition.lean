/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.CoarsenedSupportPreimage
import AlgebraicComplexity.Tensor.PartitionedProductCore

set_option autoImplicit false

/-!
# Cutting a partition to the addresses that model a present family

Layer 1 (`AlgebraicComplexity/Tensor/`).  An aggregate extraction asks its source partition for an
*exact support equality*: the partition's support must be, on the nose, the set of block addresses
representing a given finite family of present targets.  Writing that family as
`present.image addr` for a representation map `addr : Γ → BlockAddress A`, the premise reads

`P.support = present.image addr`.

Proving such an equality by transport is painful and usually false; the way to make it hold is not
to prove it at all but to *cut the partition by it*, so that it holds by `Finset.mem_filter`.
`Tensor/CoarsenedSupportPreimage.lean` does exactly this for a coarsening
(`coarseningPreimageSupport`, `mem_coarseningPreimageSupport`), and
`Examples/DuanWuZhouLevelTwoPreimageAmbient.lean` records the method in prose: *do not uncross
downstream — take the cut that was already made upstream and pull it back*.

This module states the same construction for a representation map rather than a coarsening, which
is the shape an aggregate whole-inner theorem's support premise has, and then specialises it to a
**regional product**.

## The three statements

* `modeledPreimagePartition_support_eq_image` — the support equality itself, under the one honest
  hypothesis `present.image addr ⊆ Q.support` (a present target must be representable in the
  partition at all).  Everything else is `Finset.mem_filter`.
* `mem_modeledPreimageSupport_external` and
  `external_modeledPreimagePartition_support_eq_image` — the regional form.  For a product
  `P.external Q`, `mem_external_support` splits the cover hypothesis into one condition per
  region: each present target's left half is supported in `P` and its right half in `Q`.  Regions
  are multiplied in one at a time, so an `n`-region product discharges `n` such conditions and no
  `n`-ary product is ever named.
* `Restricts.regionalSource_to_coarsePreimagePartition` — the arrow that carries a source tensor
  onto the cut partition.  Cutting a support loses constituents, so this direction is *not* free:
  it needs an upstream restriction onto the coarse cut, which is what a hashing or selection step
  supplies.  Given that, `Restricts.coarsen_withSupport_to_preimage` finishes.  This is
  `dwz63_power_restricts_preimageFine`'s last two steps with the level-two data removed.

## What a client must still supply

Only the cover hypothesis, and it is per region.  Nothing here fixes the representation map, the
present family, or how many regions there are.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x y z

section Modeled

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {Γ : Type y}

/-- **The supported addresses that model a present target.**

`addr` represents each element of `Γ` by a block address; `present.image addr` is the family of
addresses the client wants the partition to expose, and this is that family intersected with what
the partition actually supports. -/
noncomputable def modeledPreimageSupport
    (Q : PartitionedTensor (K := K) (A := A) V) (addr : Γ → BlockAddress A)
    (present : Finset Γ) : Finset (BlockAddress A) := by
  classical
  exact Q.support.filter fun s ↦ s ∈ present.image addr

@[simp] theorem mem_modeledPreimageSupport
    (Q : PartitionedTensor (K := K) (A := A) V) (addr : Γ → BlockAddress A)
    (present : Finset Γ) (s : BlockAddress A) :
    s ∈ modeledPreimageSupport Q addr present ↔
      s ∈ Q.support ∧ s ∈ present.image addr := by
  classical
  simp [modeledPreimageSupport]

namespace PartitionedTensor

/-- **The partition cut to the modeled present targets.**  Same constituents, smaller support. -/
noncomputable def modeledPreimagePartition
    (Q : PartitionedTensor (K := K) (A := A) V) (addr : Γ → BlockAddress A)
    (present : Finset Γ) : PartitionedTensor (K := K) (A := A) V :=
  Q.withSupport (modeledPreimageSupport Q addr present)

@[simp] theorem modeledPreimagePartition_support
    (Q : PartitionedTensor (K := K) (A := A) V) (addr : Γ → BlockAddress A)
    (present : Finset Γ) :
    (Q.modeledPreimagePartition addr present).support =
      modeledPreimageSupport Q addr present := rfl

@[simp] theorem modeledPreimagePartition_constituent
    (Q : PartitionedTensor (K := K) (A := A) V) (addr : Γ → BlockAddress A)
    (present : Finset Γ) (s : BlockAddress A) :
    (Q.modeledPreimagePartition addr present).constituent s = Q.constituent s := rfl

/-- **The exact support equality, by `Finset.mem_filter`.**

The premise an aggregate whole-inner theorem carries as `hsupport : P.support = modeledTargets
present` holds on the nose for the cut partition, as soon as every present target is representable
in `Q` at all. -/
theorem modeledPreimagePartition_support_eq_image
    (Q : PartitionedTensor (K := K) (A := A) V) (addr : Γ → BlockAddress A)
    (present : Finset Γ) (hcover : present.image addr ⊆ Q.support) :
    (Q.modeledPreimagePartition addr present).support = present.image addr := by
  classical
  ext s
  rw [modeledPreimagePartition_support, mem_modeledPreimageSupport]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hcover h, h⟩⟩

end PartitionedTensor

end Modeled

/-! ## The regional form: one condition per region -/

section Regional

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {B : Leg → Type x} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {W : ∀ c, B c → Type z}
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]
variable {Γ : Type y}

/-- **Regional membership.**  In a product partition the supported half of the condition splits
into one membership per region, by `mem_external_support`; the modeled half is untouched. -/
@[simp] theorem mem_modeledPreimageSupport_external
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (addr : Γ → BlockAddress (ProductBlockIndex A B)) (present : Finset Γ)
    (s : BlockAddress (ProductBlockIndex A B)) :
    s ∈ modeledPreimageSupport (P.external Q) addr present ↔
      ((fun c ↦ (s c).1) ∈ P.support ∧ (fun c ↦ (s c).2) ∈ Q.support) ∧
        s ∈ present.image addr := by
  classical
  rw [mem_modeledPreimageSupport, PartitionedTensor.mem_external_support]

/-- **The exact regional support equality.**

The cover hypothesis is checked one region at a time: for every present target, its left half is
supported in `P` and its right half in `Q`.  An `n`-region product is `n - 1` applications of
`PartitionedTensor.external`, so it discharges `n` such conditions; no `n`-ary partitioned product
is named anywhere. -/
theorem PartitionedTensor.external_modeledPreimagePartition_support_eq_image
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (addr : Γ → BlockAddress (ProductBlockIndex A B)) (present : Finset Γ)
    (hleft : ∀ t ∈ present, (fun c ↦ (addr t c).1) ∈ P.support)
    (hright : ∀ t ∈ present, (fun c ↦ (addr t c).2) ∈ Q.support) :
    ((P.external Q).modeledPreimagePartition addr present).support = present.image addr := by
  classical
  refine PartitionedTensor.modeledPreimagePartition_support_eq_image _ addr present ?_
  intro s hs
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  exact PartitionedTensor.mem_external_support P Q (addr t) |>.mpr ⟨hleft t ht, hright t ht⟩

end Regional

/-! ## Reaching the cut partition from an upstream restriction -/

section Source

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {B : Leg → Type x} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **The regional source reaches the coarse preimage partition.**

Cutting a support discards constituents, so this arrow is not free: the client must already hold a
restriction of its source onto the *coarse* cut, which is what a hashing or selection step
produces.  Given that, `Restricts.coarsen_withSupport_to_preimage` pulls the cut back to the fine
level, where it is a filter and therefore an exact support description.

`dwz63_power_restricts_preimageFine`
(`Examples/DuanWuZhouLevelTwoPreimageAmbient.lean:75`) is this statement with the level-two power,
degree map and retained family substituted. -/
theorem Restricts.regionalSource_to_coarsePreimagePartition
    {Source : Leg → Type z}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    (source : Tensor3 K Source)
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c)
    (S : Finset (BlockAddress B)) (hS : S ⊆ (P.coarsen f).support)
    (hupstream : Restricts source ((P.coarsen f).withSupport S).realize) :
    Restricts source (P.withSupport (coarseningPreimageSupport P f S)).realize :=
  hupstream.trans (Restricts.coarsen_withSupport_to_preimage P f S hS)

end Source

end AlgebraicComplexity.Tensor
