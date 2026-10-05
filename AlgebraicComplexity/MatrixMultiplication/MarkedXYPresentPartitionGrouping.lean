/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MarkedXYPresentPartitionExtraction
import AlgebraicComplexity.Tensor.IndexedSubfamily
import AlgebraicComplexity.Tensor.PartitionedGrouping

/-!
# Grouping an actually present marked family by its shared third leg

Marked affine hashing isolates the X and Y block labels while deliberately retaining repeated
Z labels.  The selected constituents are therefore not, in general, an indexed tensor direct
sum.  They are a direct sum of shared-Z fibers, each of which has the support pattern of a
C-tensor.

This module composes the actual-present-support restriction with the generic legwise grouping
theorem.  The construction keeps the distinction between abstract selected targets and targets
actually present in the source partition.  It assumes no bound on the missing family and performs
no constituent retyping inside a fiber.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

variable {R : Type u} [Field R]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

namespace PartitionHashEncoding

variable {support : Finset (BlockAddress A)}
variable {K : Type v} [CommSemiring K] {n : ℕ}
variable {V : ∀ c, PositiveWord (A c) n → Type x}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- The subpartition consisting of exactly the marked isolated addresses that are present in the
source tensor. -/
noncomputable def presentMarkedXYIsolatedPartition
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :=
  P.withSupport
    (H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed P)

@[simp] theorem presentMarkedXYIsolatedPartition_support
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :
    (H.presentMarkedXYIsolatedPartition ambientWords markedWords B seed P).support =
      H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed P :=
  rfl

/-- The actually present marked partition grouped by its shared Z block word.

The supplied fallback label is consulted only on ambient block labels absent from the selected
support.  Injectivity on X and Y is inherited from marked hashing and is proved against the
actual present intersection. -/
noncomputable def presentMarkedXYIsolatedZGrouping
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (z₀ : PositiveWord (A .Z) n) :
    (H.presentMarkedXYIsolatedPartition ambientWords markedWords B seed P).LegGrouping
      (PositiveWord (A .Z) n) := by
  apply PartitionedTensor.LegGrouping.byZ _ z₀
  · simpa only [presentMarkedXYIsolatedPartition_support] using
      H.x_injectiveOn_presentMarkedXYIsolatedPowerAddresses
        ambientWords markedWords hwords B hB seed P
  · simpa only [presentMarkedXYIsolatedPartition_support] using
      H.y_injectiveOn_presentMarkedXYIsolatedPowerAddresses
        ambientWords markedWords hwords B hB seed P

/-- The present marked cardinality is the exact sum of its occupied shared-Z fiber sizes. -/
theorem card_presentMarkedXYIsolated_eq_sum_occupiedZFiber
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (z₀ : PositiveWord (A .Z) n) :
    (H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed P).card =
      ∑ z :
          (H.presentMarkedXYIsolatedZGrouping
            ambientWords markedWords hwords B hB seed P z₀).occupiedGroups,
        ((H.presentMarkedXYIsolatedZGrouping
          ambientWords markedWords hwords B hB seed P z₀).fiberSupport z.1).card := by
  simpa only [presentMarkedXYIsolatedPartition_support] using
    (H.presentMarkedXYIsolatedZGrouping
      ambientWords markedWords hwords B hB seed P z₀).card_support_eq_sum_occupied_fiber_card

/-- The actual source restricts to the indexed direct sum of every shared-Z fiber of the
present marked family.

The first restriction is the hash zero-out on the actual support intersection.  The second is the
global legwise grouping map; no independent map is applied to a shared source variable. -/
theorem restricts_presentMarkedXYIsolated_groupedZFibers
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : P.support ⊆ H.modeledAddresses n (H.legalTargets n ambientWords))
    (z₀ : PositiveWord (A .Z) n) :
    Restricts P.realize
      (Tensor.indexedDirectSum
        (fun z : PositiveWord (A .Z) n ↦
          ((H.presentMarkedXYIsolatedZGrouping
            ambientWords markedWords hwords B hB seed P z₀).fiber z).realize)) := by
  exact
    (Tensor.Restricts.presentModeledTargets_to_presentMarkedXYIsolated
      H ambientWords markedWords hwords B hB seed P hsupport).trans
    (H.presentMarkedXYIsolatedZGrouping
      ambientWords markedWords hwords B hB seed P z₀).restricts_groupedIndexedDirectSum

/-- Empty shared-Z fibers can be discarded after grouping. -/
theorem restricts_presentMarkedXYIsolated_occupiedGroupedZFibers
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : P.support ⊆ H.modeledAddresses n (H.legalTargets n ambientWords))
    (z₀ : PositiveWord (A .Z) n) :
    Restricts P.realize
      (Tensor.indexedDirectSum
        (fun z :
            (H.presentMarkedXYIsolatedZGrouping
              ambientWords markedWords hwords B hB seed P z₀).occupiedGroups ↦
          ((H.presentMarkedXYIsolatedZGrouping
            ambientWords markedWords hwords B hB seed P z₀).fiber z.1).realize)) := by
  apply (H.restricts_presentMarkedXYIsolated_groupedZFibers
    ambientWords markedWords hwords B hB seed P hsupport z₀).trans
  exact Tensor.Restricts.indexedDirectSum_subfamily
    (fun z : PositiveWord (A .Z) n ↦
      ((H.presentMarkedXYIsolatedZGrouping
        ambientWords markedWords hwords B hB seed P z₀).fiber z).realize)
    (H.presentMarkedXYIsolatedZGrouping
      ambientWords markedWords hwords B hB seed P z₀).occupiedGroups

end PartitionHashEncoding

end AlgebraicComplexity
