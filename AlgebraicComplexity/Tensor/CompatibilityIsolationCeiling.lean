/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.CompatibilityZeroing

/-!
# How much a compatibility zero-out can retain

`AlgebraicComplexity/Tensor/CompatibilityZeroing.lean` implements "compatibility zero-out II": it
deletes every `pivot` label compatible with more than one ambient address and proves the survivors
have unique fibers (`compatibilityIsolatedSupport_hasUniqueLegFibers`).  That theorem is normally
read as a *positive* certificate — it is the `HasUniqueLegFibers` premise of legwise variable
zeroing.

This file records its *negative* reading, which is a ceiling rather than a certificate.

**The ceiling.**  Soundness says every ambient address is compatible with the label it uses.  So if
two ambient addresses share a `pivot` label, each of them is compatible with the other's label, and
*neither* can survive the isolation — whatever the compatibility relation is.  Hence

```
compatibilityIsolatedSupport ambient pivot compatible ⊆ uniqueLegFiberSupport ambient pivot
```

where the right-hand side is the ambient's own set of addresses that their `pivot` label already
determines.  The bound is uniform in `compatible`: **no choice of compatibility relation beats the
ambient's singleton-fiber ceiling**, so it cannot be improved by strengthening the relation, and a
counting argument that needs many survivors cannot be repaired at the relation.

**Why this is worth stating separately.**  A laser-style argument uses the isolation pass to
produce an exponentially large family of independent copies.  Doing so requires the *ambient* to
have exponentially many singleton `pivot` fibers.  Ambients that arise as full canonical powers of
a partitioned tensor typically do not: a leg word of such a power usually has many completions, and
the ceiling then collapses the isolation pass to the handful of leg words whose completion is
forced.  The standard remedy is the paper's own order of operations — hash or otherwise restrict
the support *first*, and run the isolation against that restricted ambient, which is what the
`ambient` parameter of every declaration below is for.  Applying the isolation to an unrestricted
power and expecting a large survivor family is exactly the error this ceiling rules out.

Everything here is a two-line consequence of the committed unique-fiber theorem; nothing new is
assumed.  The statements are packaged as a `Finset` inclusion and a cardinality bound because that
is the shape a counting client needs.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- The ambient addresses that their own `pivot` label already determines: no *other* ambient
address carries the same label on `pivot`.

This is the exact set a compatibility zero-out on `pivot` can hope to retain. -/
noncomputable def uniqueLegFiberSupport
    (ambient : Finset (BlockAddress A)) (pivot : Leg) : Finset (BlockAddress A) := by
  classical
  exact ambient.filter
    (fun address ↦ ∀ other ∈ ambient, other pivot = address pivot → other = address)

@[simp] theorem mem_uniqueLegFiberSupport
    (ambient : Finset (BlockAddress A)) (pivot : Leg) (address : BlockAddress A) :
    address ∈ uniqueLegFiberSupport ambient pivot ↔
      address ∈ ambient ∧
        ∀ other ∈ ambient, other pivot = address pivot → other = address := by
  classical
  simp [uniqueLegFiberSupport]

theorem uniqueLegFiberSupport_subset
    (ambient : Finset (BlockAddress A)) (pivot : Leg) :
    uniqueLegFiberSupport ambient pivot ⊆ ambient := by
  classical
  intro address haddress
  exact ((mem_uniqueLegFiberSupport ambient pivot address).mp haddress).1

/-- **The ceiling.**  A sound compatibility zero-out on `pivot` retains only ambient addresses
whose `pivot` label is theirs alone.

The bound does not mention `compatible`: it holds for every sound compatibility relation, so it is
a property of the *ambient*, not of the client's cleanup. -/
theorem compatibilityIsolatedSupport_subset_uniqueLegFiberSupport
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (hsound : IsCompatibilitySound ambient pivot compatible) :
    compatibilityIsolatedSupport ambient pivot compatible ⊆
      uniqueLegFiberSupport ambient pivot := by
  classical
  have hunique :=
    compatibilityIsolatedSupport_hasUniqueLegFibers ambient pivot compatible hsound
  intro address haddress
  exact (mem_uniqueLegFiberSupport ambient pivot address).mpr
    ⟨hunique.1 haddress,
      fun other hother hlabel ↦ hunique.2 address haddress other hother hlabel⟩

/-- The counting form of the ceiling: an isolation pass cannot retain more addresses than the
ambient has singleton `pivot` fibers, uniformly in the compatibility relation. -/
theorem card_compatibilityIsolatedSupport_le_card_uniqueLegFiberSupport
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (hsound : IsCompatibilitySound ambient pivot compatible) :
    (compatibilityIsolatedSupport ambient pivot compatible).card ≤
      (uniqueLegFiberSupport ambient pivot).card :=
  Finset.card_le_card
    (compatibilityIsolatedSupport_subset_uniqueLegFiberSupport ambient pivot compatible hsound)

/-- The pointwise refutation form: one ambient collision on `pivot` deletes *both* colliding
addresses, whatever the sound compatibility relation is.

This is the shape a no-go argument uses — exhibit a second ambient address with the same `pivot`
label and the first cannot have survived. -/
theorem notMem_compatibilityIsolatedSupport_of_leg_eq
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (hsound : IsCompatibilitySound ambient pivot compatible)
    {address other : BlockAddress A} (hother : other ∈ ambient)
    (hne : other ≠ address) (hlabel : other pivot = address pivot) :
    address ∉ compatibilityIsolatedSupport ambient pivot compatible := by
  classical
  intro haddress
  have hmem := (mem_uniqueLegFiberSupport ambient pivot address).mp
    (compatibilityIsolatedSupport_subset_uniqueLegFiberSupport ambient pivot compatible hsound
      haddress)
  exact hne (hmem.2 other hother hlabel)

end AlgebraicComplexity.Tensor
