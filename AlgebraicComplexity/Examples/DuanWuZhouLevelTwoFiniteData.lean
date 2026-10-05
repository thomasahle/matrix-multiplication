/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserData
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAlphaTilde

/-!
# Literal DWZ second-power finite profile data

This client transcribes [duan2023faster], section 6.3 (`global_value.tex:332-378`),
through the existing `dwz63AlphaTilde` table. Each of its fifteen profiles retains exactly
the full legal ordered Z-pair alphabet. The common denominator remains the provider's chosen
`200000000`; this is not asserted to be the least denominator or a cofinal integral period.
The free value parameter for the exceptional constituents is not substituted into their profiles.

The literal 022 profile has alphabet `[(0,2),(1,1),(2,0)]`. Its middle state on the zero-X
boundary has two occurrences of the same 011 child (`prelim.tex:294-309` and
`component_value.tex:205-225`). The small local shape registry below only demonstrates that
occurrence accounting; it is not a completed value-pair DAG or a tensor extraction.

The separate denominator-one probe retains two legal zero-count letters. Those zeros are
not part of the published second-power profile, whose legal entries are all positive.
All conclusions here concern finite data, profile decoding and integer occurrence counts.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity AsymmetricLaserData Tensor

/-- The full nine-letter ordered native pair alphabet, in left-major degree order. -/
def dwz63ProfilePairs : List (PositiveWord CWBlock 1) :=
  [(.zero, .zero), (.zero, .middle), (.zero, .last),
    (.middle, .zero), (.middle, .middle), (.middle, .last),
    (.last, .zero), (.last, .middle), (.last, .last)]

/-- Each finite Z-profile is read from the committed pair table on its full legal fiber.
The filter uses only native degree, never positivity of a primal entry. -/
def dwz63FiniteProfile (row : Fin 15) : LegProfile where
  physicalLeg := 2
  alphabet := orderedSplitAlphabet 2 (dwz63ZIndex row).val
  law :=
    { denominator := dwz63AlphaTildeMass
      counts := (dwz63ProfilePairs.filter fun pair =>
        decide (cwBlockDegree pair.1 + cwBlockDegree pair.2 = (dwz63ZIndex row).val)).map
          (dwz63AlphaTilde row) }

/-- All fifteen decoded profiles have distinct legal letters and normalized aligned counts. -/
theorem dwz63FiniteProfile_valid (row : Fin 15) : (dwz63FiniteProfile row).Valid := by
  unfold LegProfile.Valid FiniteLaw.Valid
  -- Each closed case filters nine native pairs and checks at most three entries.
  fin_cases row <;> decide

/-- Each profile has the complete bounded ordered-pair alphabet of its native Z degree. -/
theorem dwz63FiniteProfile_isOrderedSplitFor (row : Fin 15) :
    (dwz63FiniteProfile row).IsOrderedSplitFor 2 (dwz63ZIndex row).val :=
  ⟨dwz63FiniteProfile_valid row, rfl⟩

/-- Zero extension to all nine native pairs recovers every entry of the existing profile table. -/
theorem dwz63FiniteProfile_countAt (row : Fin 15) (left right : CWBlock) :
    (dwz63FiniteProfile row).countAt [cwBlockDegree left, cwBlockDegree right] =
      dwz63AlphaTilde row (left, right) := by
  fin_cases row <;> cases left <;> cases right <;> rfl

/-- The literal `(0,2,2)` profile is row two in the committed lexicographic cell order. -/
def dwz63Row022Profile : LegProfile := dwz63FiniteProfile 2

/-- The complete three-letter 022 alphabet and its exact counts are the published a-profile. -/
theorem dwz63Row022Profile_eq :
    dwz63Row022Profile =
      { physicalLeg := 2
        alphabet := [[0, 2], [1, 1], [2, 0]]
        law := { denominator := 200000000, counts := [6954806, 186090388, 6954806] } } := rfl

/-- The literal 022 profile passes structural alignment and normalization. -/
theorem dwz63Row022Profile_valid : dwz63Row022Profile.Valid := dwz63FiniteProfile_valid 2

/-- The literal law actually instantiates the existing exact rational-probability API. -/
theorem dwz63Row022Profile_isProbability : dwz63Row022Profile.law.toRational.IsProbability :=
  FiniteLaw.toRational_isProbability _ dwz63Row022Profile_valid.2.2.2

/-- The DWZ interface constrains one physical Z leg, not a joint law on all three legs. -/
def dwz63Row022Descriptor : ProfileDescriptor :=
  { view := .orderedSplit, legs := [dwz63Row022Profile] }

/-- The literal one-Z-leg descriptor has the prescribed structural shape. -/
theorem dwz63Row022Descriptor_valid : dwz63Row022Descriptor.Valid := by
  constructor
  · intro leg hleg
    have heq : leg = dwz63Row022Profile := by simpa [dwz63Row022Descriptor] using hleg
    subst leg
    exact dwz63Row022Profile_valid
  · rfl

/-- A separate grammar probe keeps the same full alphabet with legal endpoint counts zero. -/
def dwz63Row022ZeroProfile : LegProfile :=
  { physicalLeg := 2
    alphabet := [[0, 2], [1, 1], [2, 0]]
    law := { denominator := 1, counts := [0, 1, 0] } }

/-- Zero primal counts do not invalidate or shrink the complete legal ordered alphabet. -/
theorem dwz63Row022ZeroProfile_valid : dwz63Row022ZeroProfile.IsOrderedSplitFor 2 2 := by
  constructor
  · norm_num [dwz63Row022ZeroProfile, LegProfile.Valid, FiniteLaw.Valid]
  · rfl

/-- The zero-primal endpoint remains a declared legal letter with decoded count zero. -/
theorem dwz63Row022ZeroProfile_keeps_zero :
    [0, 2] ∈ dwz63Row022ZeroProfile.alphabet ∧ dwz63Row022ZeroProfile.countAt [0, 2] = 0 := by
  constructor
  · exact List.mem_cons_self
  · rfl

/-- The one-entry local child-shape registry for the middle-state occurrence probe. -/
def dwz63Row022ChildShapes : List (List Nat) := [[0, 1, 1]]

/-- The probe's level-one 011 child has local node ID zero and identity physical transport. -/
def dwz63Row022MiddleChild : ChildRef :=
  { nodeId := 0, physicalLegs := [0, 1, 2] }

/-- The middle split retains both labelled references, despite their identical target. -/
def dwz63Row022MiddleChildren : SplitChildren :=
  { left := dwz63Row022MiddleChild, right := dwz63Row022MiddleChild }

/-- Both references precede the local parent ID one and use a genuine leg permutation. -/
theorem dwz63Row022MiddleChildren_valid : dwz63Row022MiddleChildren.ValidBefore 1 := by
  constructor <;> constructor
  · norm_num [dwz63Row022MiddleChildren, dwz63Row022MiddleChild]
  · exact List.Perm.refl _
  · norm_num [dwz63Row022MiddleChildren, dwz63Row022MiddleChild]
  · exact List.Perm.refl _

/-- Both references resolve to 011, and 011 is its own complement within parent 022. -/
theorem dwz63Row022MiddleChildren_shapes :
    dwz63Row022ChildShapes[dwz63Row022MiddleChildren.left.nodeId]?.getD [] = [0, 1, 1] ∧
      dwz63Row022ChildShapes[dwz63Row022MiddleChildren.right.nodeId]?.getD [] = [0, 1, 1] ∧
      List.zipWith Nat.sub [0, 2, 2] [0, 1, 1] = [0, 1, 1] :=
  ⟨rfl, rfl, rfl⟩

/-- At the profile denominator, the middle state contributes both 011 occurrences.
The result is an integer occurrence count, not an additional root source copy. -/
theorem dwz63Row022MiddleChildren_count :
    dwz63Row022MiddleChildren.occurrenceCount dwz63Row022MiddleChild
      (dwz63Row022Profile.countAt [1, 1]) = 372180776 := by
  change (SplitChildren.mk dwz63Row022MiddleChild dwz63Row022MiddleChild).occurrenceCount
    dwz63Row022MiddleChild (dwz63Row022Profile.countAt [1, 1]) = 372180776
  rw [SplitChildren.occurrenceCount_self]
  rfl

end AlgebraicComplexity.Examples
