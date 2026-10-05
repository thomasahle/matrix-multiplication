/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserData
import AlgebraicComplexity.Combinatorics.CompatibleSplitCountDefs

/-!
# Finite profile decoding into the existing split requirements

This transcribes the integral joint profile in [duan2023faster],
`papers/sources/2210.10173/global_value.tex:35-51`, definition `def:global-compatible`.
At period P, coarse count A/D and ordered-profile count B/E give P*A*B/(D*E).
The native letter encoder keeps an ordered pair as one letter at one coarse position.
The boundary and Z-index maps remain inputs to the existing `SplitRequirements` record.

This is the raw arithmetic decoder. Valid laws, complete native alphabets, the physical leg,
and exact divisibility must be checked by a constructor before using the decoded counts.
The theorem below proves the quotient exact when P is a multiple of the product denominator.
It neither defines a tensor extraction nor admits a certificate by itself.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.AsymmetricLaserData

universe u v

/-- Decode finite coarse and conditional laws into the existing compatibility record.
Natural division is raw decoding; constructor admission must establish exact integrality. -/
def splitRequirementsFromProfiles (coarse : FiniteLaw)
    (profiles : Fin coarse.counts.length → LegProfile) {L : Type u} {Z : Type v}
    (zIndex : Fin coarse.counts.length → Z) (boundary : Fin coarse.counts.length → Bool)
    (encode : L → List Nat) (period : Nat) :
    CompatibleSplit.SplitRequirements (Fin coarse.counts.length) L Z where
  zIndex := zIndex
  boundary := boundary
  splitCount c letter := period * coarse.profile c * (profiles c).countAt (encode letter) /
    (coarse.denominator * (profiles c).law.denominator)

/-- A common product-denominator period decodes exactly to an integral joint profile.
The scale may be zero; positive cofinal periods are a separate constructor obligation. -/
theorem splitRequirementsFromProfiles_splitCount_of_period (coarse : FiniteLaw)
    (profiles : Fin coarse.counts.length → LegProfile) {L : Type u} {Z : Type v}
    (zIndex : Fin coarse.counts.length → Z) (boundary : Fin coarse.counts.length → Bool)
    (encode : L → List Nat) (period : Nat) (c : Fin coarse.counts.length) (letter : L)
    (scale : Nat) (hden : 0 < coarse.denominator * (profiles c).law.denominator)
    (hperiod : period = coarse.denominator * (profiles c).law.denominator * scale) :
    (splitRequirementsFromProfiles coarse profiles zIndex boundary encode period).splitCount
        c letter = (profiles c).countAt (encode letter) * (coarse.profile c * scale) := by
  change period * coarse.profile c * (profiles c).countAt (encode letter) /
    (coarse.denominator * (profiles c).law.denominator) = _
  rw [hperiod]
  have hfactor :
      coarse.denominator * (profiles c).law.denominator * scale * coarse.profile c *
          (profiles c).countAt (encode letter) =
        ((profiles c).countAt (encode letter) * (coarse.profile c * scale)) *
          (coarse.denominator * (profiles c).law.denominator) := by ac_rfl
  rw [hfactor, Nat.mul_div_cancel _ hden]

end AlgebraicComplexity.AsymmetricLaserData
