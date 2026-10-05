/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.LocalizedCoarsenedSelection

set_option autoImplicit false

/-!
# The two normal forms of a localized fiber selection

`PartitionedTensor.coarseningFiber_select_eq_box`
(`Tensor/LocalizedCoarsenedSelection.lean`) says that localizing a partitioned tensor to one
coarse-address fiber and then selecting legwise is a single Cartesian **box**.  Downstream lanes
also want the same fact in **select** normal form --- the fiber condition conjoined onto the keep
predicate --- because `StructureRelabeling.select` and the segmented Hole Lemma consume a
`select`.  Restating the identity twice is the duplication this module removes.

`PartitionedTensor.box` is *by definition* a `select` by membership in the legwise parts, so the
two right-hand sides differ only by unfolding a membership.  That observation is
`box_eq_select_of_mem_iff`, and `box_coarseningFiberSelectParts_eq_select` is its instance at
`coarseningFiberSelectParts`.  Either spelling of the fiber identity now follows from the other by
a single `trans`:

```
(P.coarseningFiber f target).select keep
    = P.box (coarseningFiberSelectParts f target keep)   -- coarseningFiber_select_eq_box
    = P.select (fun c a ↦ f c a = target c ∧ keep c a)   -- this module
```

Nothing here is specific to a paper; the two clients are the `[CoppersmithWinograd1990]` recursive
route (which reads the `box` form) and the `[duan2023faster]` localized segmented leaf (which
reads the `select` form).
-/

namespace AlgebraicComplexity.Tensor

universe u v w x

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- A Cartesian box is the selection by legwise membership in its parts: any predicate with the
same legwise extension cuts out the same partitioned tensor.  This is the whole difference between
the `box` and `select` normal forms of a selection. -/
theorem PartitionedTensor.box_eq_select_of_mem_iff
    (P : PartitionedTensor (K := K) (A := A) V)
    (parts : ∀ c, Finset (A c)) (keep : ∀ c, A c → Prop)
    [∀ c a, Decidable (keep c a)]
    (hparts : ∀ c a, a ∈ parts c ↔ keep c a) :
    P.box parts = P.select keep := by
  classical
  apply PartitionedTensor.ext
  · ext address
    rw [PartitionedTensor.mem_box_support, PartitionedTensor.mem_select_support]
    exact and_congr_right fun _ ↦ forall_congr' fun c ↦ hparts c (address c)
  · rfl

/-- **The bridge between the two spellings of the localized-fiber selection identity.**

The box that `coarseningFiber_select_eq_box` produces is the selection by the fiber condition
conjoined legwise onto the keep predicate.  Composing the two gives the `select` normal form
without a second support computation. -/
theorem PartitionedTensor.box_coarseningFiberSelectParts_eq_select
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    P.box (coarseningFiberSelectParts f target keep) =
      P.select (fun c a ↦ f c a = target c ∧ keep c a) :=
  P.box_eq_select_of_mem_iff _ _ fun c a ↦
    mem_coarseningFiberSelectParts f target keep c a

end AlgebraicComplexity.Tensor
