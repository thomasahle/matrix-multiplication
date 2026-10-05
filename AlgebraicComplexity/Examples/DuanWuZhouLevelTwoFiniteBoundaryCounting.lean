/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.AsymmetricLaserCWBoundaryProfileCounting
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteBoundaryProfile

/-!
# The complete DWZ022 native multinomial dimension

This literal instance follows [duan2023faster],
`papers/sources/2210.10173/component_value.tex:468-475` and
`second_power_appendix.tex:1-50`. Both zero frames retain the complete law
[6954806,186090388,6954806]/200000000 in the actual localized source.
Its native nine-pair counts are the landed `dwz63AlphaTilde 2`; the finite
multinomial dimension is derived from them and both half-word middle counts.
No factorial of the large literal is evaluated and no analytic rate is assumed.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open Tensor AsymmetricLaserData MoreAsymmetryCompatibility

/-- The full022 native source has its exact nine-pair multinomial count in both zero frames. -/
theorem dwz63Row022Boundary_card_eq_multinomial (K : Type*) [CommRing K]
    (zero : Fin 2) (j n : Nat) (hlength : n + 1 = 200000000 * j) :
    (cwBoundaryProfileCell K 6 (if zero.val = 0 then Leg.X else Leg.Y)
      2 dwz63Row022Profile j n).support.card =
      Nat.multinomial Finset.univ (WordType.proportionalCounts (dwz63AlphaTilde 2) j) := by
  have h := cwBoundaryProfile_card_eq_multinomial K (dwz63Row022BoundaryData zero)
    _ 2 dwz63Row022Profile (dwz63Row022Boundary_decodes zero) j n hlength
  rw [dwz63Row022Boundary_counts] at h
  exact h

/-- The full022 finite constructor derives the actual matrix dimension at each integral length. -/
theorem dwz63Row022Boundary_restricts_multinomial (K : Type*) [CommRing K]
    (zero : Fin 2) (j n : Nat) (hlength : n + 1 = 200000000 * j) :
    Restricts
      (Tensor.permute (zeroOrientation (if zero.val = 0 then Leg.X else Leg.Y))
        (cwBoundaryProfileCell K 6 (if zero.val = 0 then Leg.X else Leg.Y)
          2 dwz63Row022Profile j n).realize)
      (matrixMultiplication (K := K) 1
        (Nat.multinomial Finset.univ (WordType.proportionalCounts (dwz63AlphaTilde 2) j) *
          6 ^ cwBoundaryProfileExponent dwz63Row022Profile j) 1) := by
  have h := dwz63Row022Boundary_restricts K zero j n
  rwa [dwz63Row022Boundary_card_eq_multinomial K zero j n hlength] at h

end AlgebraicComplexity.Examples
