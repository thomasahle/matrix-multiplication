/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserSplitProfile
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteData
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSplitAlphabetBridge

/-!
# The finite DWZ second-power profile decoder at the existing provider period

This is the literal instance of [duan2023faster], section 6.3,
`papers/sources/2210.10173/global_value.tex:332-378`, and the compatibility definition
`def:global-compatible` at lines 35-51. All fifteen coarse counts and conditional profiles are
read from the existing tables. The nine ordered Z-pairs remain one letter per coarse position.

The provider period is 20000000000000000 times s. It is ten times the least integral joint
period of the printed input; replacing it would change the established count/seed schedule.
This module proves equality to the existing fine-pair split record and applies its competitor
inclusion. That inclusion is not equality of competitor families. Leaf divisibilities, positive
cofinal reference families, common-seed extraction, repair and paid analytic margins remain
separate obligations; this finite bridge does not prove an exponent bound.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity AsymmetricLaserData
open AlgebraicComplexity.Tensor

/-- The normalized printed coarse law, in the existing fifteen-cell order. -/
def dwz63FiniteCoarseLaw : FiniteLaw :=
  { denominator := 100000000, counts := List.ofFn dwz63Alpha }

/-- The coarse finite record has positive denominator and total count equal to it. -/
theorem dwz63FiniteCoarseLaw_valid : dwz63FiniteCoarseLaw.Valid := by
  constructor
  · norm_num [dwz63FiniteCoarseLaw]
  · rfl

/-- The finite record preserves every entry of the existing coarse type. -/
theorem dwz63FiniteCoarseLaw_profile (row : Fin 15) :
    dwz63FiniteCoarseLaw.profile row = dwz63Alpha row := by
  fin_cases row <;> rfl

/-- Decode all fifteen Z-pair laws at the period used by the existing DWZ providers. -/
def dwz63FiniteSplitPair (s : Nat) :
    CompatibleSplit.SplitRequirements (Fin 15) (PositiveWord CWBlock 1) (Fin 5) :=
  splitRequirementsFromProfiles dwz63FiniteCoarseLaw dwz63FiniteProfile
    dwz63ZIndex dwz63Boundary (fun pair => [cwBlockDegree pair.1, cwBlockDegree pair.2])
    (20000000000000000 * s)

/-- The decoded product-denominator quotient is exactly the established joint count. -/
theorem dwz63FiniteSplitPair_splitCount (s : Nat) (row : Fin 15)
    (pair : PositiveWord CWBlock 1) :
    (dwz63FiniteSplitPair s).splitCount row pair =
      dwz63AlphaTilde row pair * (dwz63Alpha row * s) := by
  change CWBlock × CWBlock at pair
  calc
    _ = (dwz63FiniteProfile row).countAt [cwBlockDegree pair.1, cwBlockDegree pair.2] *
        (dwz63FiniteCoarseLaw.profile row * s) :=
      splitRequirementsFromProfiles_splitCount_of_period dwz63FiniteCoarseLaw
        dwz63FiniteProfile dwz63ZIndex dwz63Boundary
        (fun p : PositiveWord CWBlock 1 => [cwBlockDegree p.1, cwBlockDegree p.2])
        (20000000000000000 * s) row pair s (by norm_num [dwz63FiniteCoarseLaw,
          dwz63FiniteProfile, dwz63AlphaTildeMass]) (by
            norm_num [dwz63FiniteCoarseLaw, dwz63FiniteProfile, dwz63AlphaTildeMass])
    _ = _ := by
      rw [dwz63FiniteProfile_countAt, dwz63FiniteCoarseLaw_profile]
      rfl

/-- The decoded record equals the existing fine-pair record, including its boundary and Z maps. -/
theorem dwz63FiniteSplitPair_eq (s : Nat) : dwz63FiniteSplitPair s = dwz63SplitPair s := by
  exact congrArg (fun f : Fin 15 → PositiveWord CWBlock 1 → Nat =>
    (⟨dwz63ZIndex, dwz63Boundary, f⟩ :
      CompatibleSplit.SplitRequirements (Fin 15) (PositiveWord CWBlock 1) (Fin 5)))
    (funext fun row => funext fun pair => dwz63FiniteSplitPair_splitCount s row pair)

/-- Existing left-letter pushforward applies directly to the decoded fine record. -/
theorem dwz63FiniteSplitPair_letterPushforward (s : Nat) (row : Fin 15) (left : Fin 3) :
    WordType.mappedType dwz63FineLeftDegree
      (fun pair => (dwz63FiniteSplitPair s).splitCount row pair) left =
        (dwz63Split s).splitCount row left := by
  rw [dwz63FiniteSplitPair_eq]
  exact dwz63_splitPair_letterPushforward s row left

/-- A competitor for the decoded ordered-pair constraints is a competitor for the left law.
This applies the existing inclusion theorem; no new competitor-count argument is introduced. -/
theorem dwz63FiniteSplitPair_matchableCompatible_subset (s : Nat) (alphaType : Fin 15 → Nat)
    {N : Nat} (K : Fin N → Fin 5) (w : Fin N → PositiveWord CWBlock 1) :
    (dwz63FiniteSplitPair s).matchableCompatible alphaType K w ⊆
      (dwz63Split s).matchableCompatible alphaType K (dwz63FineLeftDegree ∘ w) := by
  rw [dwz63FiniteSplitPair_eq]
  exact dwz63_matchableCompatiblePair_subset s alphaType K w

end AlgebraicComplexity.Examples
