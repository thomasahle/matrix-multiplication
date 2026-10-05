/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.AsymmetricLaserCWBoundaryProfileRestriction
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteData

/-!
# The complete DWZ022 boundary profile as a finite native constructor

This literal client of [duan2023faster],
`papers/sources/2210.10173/component_value.tex:459-475` and
`second_power_appendix.tex:1-50`, uses the committed full022 law
[6954806, 186090388, 6954806]/200000000. Both endpoint classes remain in
its actual localized source. The zero-X case is 022; zero-Y is its 202 mirror
with the same physical-Z law. Every positive multiplier has an inhabited source.

The exact one-slice dimension retains the actual support cardinality. This
finite restriction supplies no entropy comparison, full DAG Checks or new bound.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open Tensor AsymmetricLaserData MoreAsymmetryCompatibility

/-- The full022 physical-Z law at q6, in either of the two admitted zero frames. -/
def dwz63Row022BoundaryData (zero : Fin 2) : CWBoundaryProfileData :=
  { q := 6, zeroLeg := zero.val, zDegree := 2, profile := dwz63Row022Descriptor }

/-- Both zero frames carry the exact three-letter profile, including both endpoints. -/
theorem dwz63Row022Boundary_decodes (zero : Fin 2) :
    decodeCWBoundaryProfile (dwz63Row022BoundaryData zero) =
      some (if zero.val = 0 then Leg.X else Leg.Y, 2, dwz63Row022Profile) := by
  fin_cases zero <;>
    norm_num [decodeCWBoundaryProfile, dwz63Row022BoundaryData, dwz63Row022Descriptor,
      dwz63Row022Profile_eq, orderedSplitAlphabet, List.range_succ, Fin.ext_iff]

/-- Decoding the complete profile recovers all nine native entries of the landed DWZ table. -/
theorem dwz63Row022Boundary_counts :
    cwBoundaryProfileCounts dwz63Row022Profile = dwz63AlphaTilde 2 := by
  funext p
  rcases p with ⟨left, right⟩
  exact dwz63FiniteProfile_countAt 2 left right

/-- The literal q6 full profile produces the actual native one-slice restriction. -/
theorem dwz63Row022Boundary_restricts (K : Type*) [CommRing K] (zero : Fin 2) (j n : Nat) :
    Restricts
      (Tensor.permute (zeroOrientation (if zero.val = 0 then Leg.X else Leg.Y))
        (cwBoundaryProfileCell K 6 (if zero.val = 0 then Leg.X else Leg.Y)
          2 dwz63Row022Profile j n).realize)
      (matrixMultiplication (K := K) 1
        ((cwBoundaryProfileCell K 6 (if zero.val = 0 then Leg.X else Leg.Y)
          2 dwz63Row022Profile j n).support.card *
          6 ^ cwBoundaryProfileExponent dwz63Row022Profile j) 1) :=
  cwBoundaryProfile_restricts K (dwz63Row022BoundaryData zero) _ 2 dwz63Row022Profile
    (dwz63Row022Boundary_decodes zero) j n

/-- Every positive multiple of the literal denominator has an inhabited native source
and a positive fused middle dimension. No universal zero-length convention is used. -/
theorem dwz63Row022Boundary_nonempty (K : Type*) [CommRing K] (zero : Fin 2)
    (j : Nat) (hj : 0 < j) :
    (cwBoundaryProfileCell K 6 (if zero.val = 0 then Leg.X else Leg.Y)
      2 dwz63Row022Profile j (200000000 * j - 1)).support.Nonempty ∧
      0 < (cwBoundaryProfileCell K 6 (if zero.val = 0 then Leg.X else Leg.Y)
        2 dwz63Row022Profile j (200000000 * j - 1)).support.card *
        6 ^ cwBoundaryProfileExponent dwz63Row022Profile j := by
  apply cwBoundaryProfile_nonempty K (dwz63Row022BoundaryData zero) _ 2 dwz63Row022Profile
    (dwz63Row022Boundary_decodes zero) j (200000000 * j - 1)
  change 200000000 * j - 1 + 1 = 200000000 * j
  have hpos : 0 < 200000000 * j := Nat.mul_pos (by decide) hj
  omega

end AlgebraicComplexity.Examples
