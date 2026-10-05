/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserOrientationRule
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateOrientation
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteBaseRule

/-!
# Finite admission of the DWZ zero-X011 frame

This client transcribes the unrestricted base orientation in [duan2023faster],
`papers/sources/2210.10173/component_value.tex:459-475`, with the ordered-child convention
of `prelim.tex:294-309`. A separate reference to the existing 011 registry entry carries
the physical table [1,2,0]. Its decode is the committed `zeroOrientation .X = cycle.symm`.
The shared base admission gives MM(1,1,6); the shared finite orientation rule derives
the actual permuted source restriction to MM(1,6,1).

The source frame is the one used by `cw011ZeroXOneSliceRestriction`. This proposition
does not assert equality to that provider's canonical Z map. The paired-011 identity
references stay unchanged. Full restricted-splitting value, profile transport, shared-map
coherence, producing-DAG checks and the shared exponent regression remain open.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open Tensor AsymmetricLaserData MoreAsymmetryCompatibility

universe u

/-- A separate zero-X frame reference to the committed native 011 registry entry. -/
def dwz63ZeroX011Child : ChildRef :=
  { dwz63Row022MiddleChild with physicalLegs := [1, 2, 0] }

/-- The reference's output-to-input table decodes to the actual committed zero-X frame. -/
theorem dwz63ZeroX011Child_decodes :
    decodePhysicalLegs dwz63ZeroX011Child.physicalLegs = some (zeroOrientation .X) := rfl

/-- Apply both finite admission steps to obtain the rotated native 011 restriction at q = 6. -/
theorem dwz63ZeroX011Child_restricts (K : Type u) [CommRing K] :
    Restricts
      (Tensor.permute (zeroOrientation .X)
        (cwSupportedConstituent K dwz63Q ⟨cw011, by decide⟩))
      (matrixMultiplication (K := K) 1 6 1) := by
  obtain ⟨s, hd, _, _, hs⟩ :=
    cwBaseRuleCheck_sound K (dwz63Row022BaseRuleData dwz63ZeroX011Child) rfl
  change some (⟨cw011, by decide⟩ : cwBlockSupport) = some s at hd
  have heq := Option.some.inj hd
  subst s
  change Restricts (cwSupportedConstituent K dwz63Q ⟨cw011, by decide⟩)
    (matrixMultiplication (K := K) 1 1 6) at hs
  exact decodePhysicalLegs_restricts K dwz63ZeroX011Child.physicalLegs
    (zeroOrientation .X) 1 1 6 dwz63ZeroX011Child_decodes _ hs

end AlgebraicComplexity.Examples
