/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserSplitRefinement
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteSplit

/-!
# The DWZ finite decoder refines its coarse type and retains legal ordered letters

This is the literal instance of [duan2023faster], `global_value.tex:32-51,75-82,332-378`,
`def:global-compatible`, `def:useful_g`, and the section 6.3 profile table. The native row
normalizations are read from the existing nine-pair table, with all fifteen rows retained.
The shared finite refinement theorem uses the established period 20000000000000000*s.
For any useful word, every physical Z pair has its component's prescribed total degree.

These are constructor inputs to existing word-type counts. They do not provide a marked
hashing seed, a support identity for a whole tensor, repair, or an exponent conclusion.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity AsymmetricLaserData Tensor
open scoped BigOperators

/-- Zero extension to all nine native pairs has exactly the declared profile mass. -/
theorem dwz63FiniteProfile_nativeMass (row : Fin 15) :
    (∑ pair : PositiveWord CWBlock 1,
      (dwz63FiniteProfile row).countAt [cwBlockDegree pair.1, cwBlockDegree pair.2]) =
        (dwz63FiniteProfile row).law.denominator := by
  change (∑ pair : CWBlock × CWBlock,
    (dwz63FiniteProfile row).countAt [cwBlockDegree pair.1, cwBlockDegree pair.2]) = _
  calc
    _ = ∑ pair : CWBlock × CWBlock, dwz63AlphaTilde row pair := by
      apply Finset.sum_congr rfl
      intro pair _
      exact dwz63FiniteProfile_countAt row pair.1 pair.2
    _ = dwz63AlphaTildeMass := dwz63_profileMass_alphaTilde row
    _ = (dwz63FiniteProfile row).law.denominator := rfl

/-- The shared finite checks derive the existing refinement premise at every DWZ repetition. -/
theorem dwz63FiniteSplitPair_refinesType (s : Nat) :
    (dwz63FiniteSplitPair s).RefinesType
      (WordType.proportionalCounts dwz63Alpha (200000000 * s)) := by
  have h := splitRequirementsFromProfiles_refinesType dwz63FiniteCoarseLaw
    dwz63FiniteProfile dwz63ZIndex dwz63Boundary
    (fun pair : PositiveWord CWBlock 1 => [cwBlockDegree pair.1, cwBlockDegree pair.2])
    (200000000 * s) (fun _ => s)
    (fun _ => by norm_num [dwz63FiniteCoarseLaw, dwz63FiniteProfile, dwz63AlphaTildeMass])
    dwz63FiniteProfile_nativeMass (fun _ => rfl)
  have hperiod : dwz63FiniteCoarseLaw.denominator * (200000000 * s) =
      20000000000000000 * s := by
    change 100000000 * (200000000 * s) = 20000000000000000 * s
    ring
  rw [hperiod] at h
  intro row
  have hrow := h row
  change (∑ pair, (dwz63FiniteSplitPair s).splitCount row pair) =
    dwz63FiniteCoarseLaw.profile row * (200000000 * s) at hrow
  simpa only [WordType.proportionalCounts, dwz63FiniteCoarseLaw_profile] using hrow

/-- Each ordered Z letter of a decoded useful word has the actual coarse Z degree. -/
theorem dwz63FiniteSplitPair_isUseful_degree (s : Nat) {N : Nat}
    (comp : Fin N → Fin 15) (word : Fin N → PositiveWord CWBlock 1)
    (huseful : (dwz63FiniteSplitPair s).IsUseful comp word) (position : Fin N) :
    cwBlockDegree (word position).1 + cwBlockDegree (word position).2 =
      (dwz63ZIndex (comp position)).val := by
  have hmem := splitRequirementsFromProfiles_isUseful_mem_alphabet dwz63FiniteCoarseLaw
    dwz63FiniteProfile dwz63ZIndex dwz63Boundary
    (fun pair : PositiveWord CWBlock 1 => [cwBlockDegree pair.1, cwBlockDegree pair.2])
    (20000000000000000 * s) comp word huseful position
  rw [(dwz63FiniteProfile_isOrderedSplitFor (comp position)).2] at hmem
  simpa only [List.sum_cons, List.sum_nil, Nat.add_zero] using
    orderedSplitAlphabet_degree_of_mem hmem

end AlgebraicComplexity.Examples
