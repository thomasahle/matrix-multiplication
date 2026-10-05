/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSegmentedFiberStabilizer
import AlgebraicComplexity.Tensor.SingleLegHoleRepair

set_option autoImplicit false

/-!
# Breaking: a retained constituent restricts to a broken localized leaf

`dwz63_hleaf_segmentedFineFiber` restricts one retained coarse constituent onto the *intact*
segmented fine fiber over that constituent's coarse target.  The hashing step then destroys some
`Z`-words in each retained copy, and `hole_lemma.tex` repairs the damage.  This module supplies the
step between: zeroing the damaged `Z`-words is itself a restriction, so the constituent restricts
onto the *broken* fiber.

Both statements are about the **localized** fiber, not the global segmented power.  See the module
docstring of `Examples/DuanWuZhouLevelTwoSegmentedFiberStabilizer.lean`: a retained constituent
contains only fine words over its own coarse target, so the global segmented power is strictly
larger than it and no restriction from the constituent onto the global power exists.  The
localization is not a convenience; it is forced.

`[DuanWuZhou2022]`, `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- The localized segmented leaf with a finite set of `Z`-words destroyed. -/
noncomputable def dwz63BrokenSegmentedFineFiber (K : Type u) [CommRing K] (n m : ℕ)
    (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (holes : Finset (SegmentedAvailableWord seg alphaTilde)) :=
  (dwz63SegmentedFineFiber K n m seg alphaTilde target).holeSelect Leg.Z
    fun word ↦ word ∈ holes.image Subtype.val

/-- **Breaking is a restriction.**  Destroying `Z`-words only zeroes coordinates. -/
theorem dwz63_breaking_segmentedFineFiber (K : Type u) [CommRing K] (n m : ℕ)
    (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (holes : Finset (SegmentedAvailableWord seg alphaTilde)) :
    Restricts (dwz63SegmentedFineFiber K n m seg alphaTilde target).realize
      (dwz63BrokenSegmentedFineFiber K n m seg alphaTilde target holes).realize := by
  classical
  rw [dwz63BrokenSegmentedFineFiber, PartitionedTensor.holeSelect]
  exact Restricts.partitionedSelect _ _

/-- **`hleaf`, with the hashing damage already taken.**

One retained coarse constituent restricts onto the broken localized segmented leaf.  This is the
premise the Hole Lemma consumes, in the localized shape the constituent actually supports. -/
theorem dwz63_hleaf_brokenSegmentedFineFiber (K : Type u) [CommRing K] (n m : ℕ)
    (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (htarget : target ∈
      (((cwPartitionedTensor K dwz63Q).positivePower 1).coarsenedPositivePower
        cwSquareDegreeMap n).support)
    (holes : Finset (SegmentedAvailableWord seg alphaTilde)) :
    Restricts
      ((((cwPartitionedTensor K dwz63Q).positivePower 1).coarsenedPositivePower
        cwSquareDegreeMap n).constituent target)
      (dwz63BrokenSegmentedFineFiber K n m seg alphaTilde target holes).realize :=
  (dwz63_hleaf_segmentedFineFiber K n m seg alphaTilde target htarget).trans
    (dwz63_breaking_segmentedFineFiber K n m seg alphaTilde target holes)

end AlgebraicComplexity.Examples
