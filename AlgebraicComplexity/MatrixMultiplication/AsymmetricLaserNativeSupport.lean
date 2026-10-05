/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserSplitProfile

/-!
# Native support of a decoded finite split profile

This is the support implication in [duan2023faster], definition `def:global-compatible`,
`papers/sources/2210.10173/global_value.tex:35-51`: a retained small Z-block lies over its
owner's coarse Z-block. A finite constructor checks the declared letters' physical degrees.
Zero extension then gives that property for every nonzero decoded entry, at any period.

This implication needs neither normalized counts nor a positive denominator: an undeclared
letter decodes to zero even for invalid arithmetic data. It does not establish validity,
integrality, nonempty word families, a seed, or a repair budget.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.AsymmetricLaserData

universe u v

/-- A physical-degree check on the declared alphabet holds on the decoded support.
Proof sketch: an undeclared letter has count zero, hence zero decoded count, contradicting
support membership. Apply the finite alphabet check to the remaining declared letter. -/
theorem splitRequirementsFromProfiles_support (coarse : FiniteLaw)
    (profiles : Fin coarse.counts.length → LegProfile) {L : Type u} {Z : Type v}
    (zIndex : Fin coarse.counts.length → Z) (boundary : Fin coarse.counts.length → Bool)
    (encode : L → List Nat) (period : Nat) (degreeMap : L → Z)
    (hdegree : ∀ c letter, encode letter ∈ (profiles c).alphabet →
      degreeMap letter = zIndex c) :
    ∀ c letter,
      (splitRequirementsFromProfiles coarse profiles zIndex boundary encode
        period).splitCount c letter ≠ 0 → degreeMap letter = zIndex c := by
  classical
  intro c letter hnonzero
  apply hdegree c letter
  by_contra hnot
  have hzero := (profiles c).countAt_eq_zero_of_not_mem (encode letter) hnot
  apply hnonzero
  simp only [splitRequirementsFromProfiles, hzero, Nat.mul_zero, Nat.zero_div]

end AlgebraicComplexity.AsymmetricLaserData
