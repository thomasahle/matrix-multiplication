/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.AsymmetricLaserCWBoundaryChild
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteBoundaryRate
import AlgebraicComplexity.MatrixMultiplication.SixSymmetrizedValue

/-!
# Checked full022 children with their native transported weight

This literal client formalizes [duan2023faster],
`papers/sources/2210.10173/prelim.tex:337-367` (`def:restricted_splitting`)
and `component_value.tex:459-475` (the boundary restricted-splitting argument).
The finite prefix contains the admitted full022 law in both native zero frames.
The checked cyclic frame moves its complete ordered Z profile to physical X.
Both endpoint classes and the middle class remain, with denominator 200000000.

The existing cofinal native rate is transported through the same partition that
the reference decodes. A common positive cutoff gives inhabited actual sources;
the rate still pays a positive deficit. No producing-DAG Checks, parent extraction,
hole repair or new exponent bound is asserted.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open Tensor AsymmetricLaserData

/-- The two earlier native entries carry the full022 law in zero-X and zero-Y frames. -/
def dwz63Row022BoundaryPrefix : List CWBoundaryProfileData :=
  [dwz63Row022BoundaryData 0, dwz63Row022BoundaryData 1]

/-- One literal child rotates its native tensor and complete Z law by the same cycle. -/
def dwz63Row022BoundaryChild (zero : Fin 2) : CWBoundaryChild :=
  ⟨dwz63Row022BoundaryData zero, if zero.val = 0 then Leg.X else Leg.Y,
    2, dwz63Row022Profile, cycle⟩

/-- Both backward references decode their actual native entry and the cyclic physical frame. -/
theorem dwz63Row022BoundaryChild_decodes (zero : Fin 2) :
    decodeCWBoundaryChild dwz63Row022BoundaryPrefix ⟨zero.val, [2, 0, 1]⟩ =
      some (dwz63Row022BoundaryChild zero) := by
  fin_cases zero <;>
    simp [decodeCWBoundaryChild, dwz63Row022BoundaryPrefix, dwz63Row022BoundaryChild,
      dwz63Row022Boundary_decodes, decodePhysicalLegs]

/-- The output law is the complete input law on physical X, without dropping endpoints. -/
theorem dwz63Row022BoundaryChild_profile (zero : Fin 2) :
    (cwBoundaryChildProfile (dwz63Row022BoundaryChild zero)).physicalLeg = 0 ∧
      (cwBoundaryChildProfile (dwz63Row022BoundaryChild zero)).alphabet =
        dwz63Row022Profile.alphabet ∧
      (cwBoundaryChildProfile (dwz63Row022BoundaryChild zero)).law = dwz63Row022Profile.law :=
  ⟨rfl, rfl, rfl⟩

/-- The checked literal children have inhabited actual support and the native cofinal weight
in the same output partition, in both zero frames and with one positive cutoff. -/
theorem dwz63Row022BoundaryChild_exists_cofinalWeight (K : Type*) [CommRing K]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j : ℕ, N ≤ j → ∀ zero : Fin 2,
      (cwBoundaryChildCell K (dwz63Row022BoundaryChild zero)
        j (200000000 * j - 1)).support.Nonempty ∧
      HasTauWeight K
        (cwBoundaryChildCell K (dwz63Row022BoundaryChild zero)
          j (200000000 * j - 1)).realize dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal022 - ε))) := by
  obtain ⟨N, hN, hnative⟩ := dwz63Row022Boundary_exists_cofinalWeight K ε hε
  refine ⟨N, hN, fun j hj zero ↦ ?_⟩
  have hw := (hnative j hj zero).2
  constructor
  · apply cwBoundaryChild_nonempty K dwz63Row022BoundaryPrefix ⟨zero.val, [2, 0, 1]⟩ _
      (dwz63Row022BoundaryChild_decodes zero)
    change 200000000 * j - 1 + 1 = 200000000 * j
    have hjpos : 0 < j := lt_of_lt_of_le (by decide : 0 < 1) (hN.trans hj)
    have hpos : 0 < 200000000 * j := Nat.mul_pos (by decide) hjpos
    omega
  · rw [cwBoundaryChild_realize]
    exact hw.permute cycle

end AlgebraicComplexity.Examples
