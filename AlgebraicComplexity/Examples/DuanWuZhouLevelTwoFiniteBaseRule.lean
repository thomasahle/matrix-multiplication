/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.AsymmetricLaserCWBaseRule
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteData
import AlgebraicComplexity.MatrixMultiplication.TypeExtraction

/-!
# The two finite 011 base rules in the DWZ 022 middle split

This literal client of [duan2023faster] follows `prelim.tex:294-309` (the two labelled
children of a split) and `second_power.tex:51-63` (native base components and their matrix
multiplication products), under `papers/sources/2210.10173/`. The committed 022 middle-state
registry supplies both child shapes. Their physical transports are checked to be identities.
The shared finite CW admission theorem then supplies each native 011 restriction at q = 6;
their external product restricts to matrix multiplication of dimensions (1, 1, 36).

Both references are used even though they have the same node ID. They denote two factors
already present in one split, not an additional root source copy. This is admission of this
literal pair of base rules, not extraction of the full 022 component or a completed producing
DAG. The full finite checks and shared exponent regression remain separate obligations.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open Tensor

universe u

/-- Read a base-rule shape from the committed local 022 child registry at the DWZ parameter.
This lookup does not interpret leg transport; the literal consumer checks its identities below.
An absent registry entry yields the empty shape, which the shared decoder rejects. -/
def dwz63Row022BaseRuleData (child : AsymmetricLaserData.ChildRef) : CWBaseRuleData :=
  { q := dwz63Q, shape := dwz63Row022ChildShapes[child.nodeId]?.getD [] }

/-- Both actual middle-state references pass base admission and have identity physical transport. -/
theorem dwz63Row022MiddleBaseRules_checked :
    cwBaseRuleCheck (dwz63Row022BaseRuleData dwz63Row022MiddleChildren.left) = true ∧
      cwBaseRuleCheck (dwz63Row022BaseRuleData dwz63Row022MiddleChildren.right) = true ∧
      dwz63Row022MiddleChildren.left.physicalLegs = [0, 1, 2] ∧
      dwz63Row022MiddleChildren.right.physicalLegs = [0, 1, 2] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Admit both labelled 011 occurrences through the shared finite rule and multiply their
native matrix dimensions. The source contains precisely the two factors of the middle split. -/
theorem dwz63Row022MiddleBaseRules_restricts (K : Type u) [CommRing K] :
    Restricts
      (Tensor.external
        (cwSupportedConstituent K dwz63Q ⟨cw011, by decide⟩)
        (cwSupportedConstituent K dwz63Q ⟨cw011, by decide⟩))
      (matrixMultiplication (K := K) 1 1 36) := by
  rcases dwz63Row022MiddleBaseRules_checked with ⟨hleft, hright, _, _⟩
  obtain ⟨sL, hdL, _, _, hL⟩ := cwBaseRuleCheck_sound K
    (dwz63Row022BaseRuleData dwz63Row022MiddleChildren.left) hleft
  obtain ⟨sR, hdR, _, _, hR⟩ := cwBaseRuleCheck_sound K
    (dwz63Row022BaseRuleData dwz63Row022MiddleChildren.right) hright
  change some (⟨cw011, by decide⟩ : cwBlockSupport) = some sL at hdL
  change some (⟨cw011, by decide⟩ : cwBlockSupport) = some sR at hdR
  have hsL := Option.some.inj hdL
  have hsR := Option.some.inj hdR
  subst sL
  subst sR
  change Restricts (cwSupportedConstituent K dwz63Q ⟨cw011, by decide⟩)
    (matrixMultiplication (K := K) 1 1 6) at hL hR
  exact (Restricts.external hL hR).trans
    (Isomorphic.matrixMultiplication_external (K := K) 1 1 6 1 1 6).restricts

end AlgebraicComplexity.Examples
