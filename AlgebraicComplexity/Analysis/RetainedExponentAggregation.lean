/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.RegionalExponent
import Mathlib.Tactic.Linarith

/-!
# Aggregating certified floors for retained exponents

Recursive laser certificates attach three directional branch values to each retained group and
use their minimum.  Generated arithmetic checkers often certify one common lower floor for all
three branches of a group.  This module is the small semantic adapter from those componentwise
checks to the summed retained exponent.

The four-family endpoint is named for the root, level-4, level-3, and level-2 families occurring
in current recursive CW constructions, but remains completely independent of those tensors and
of any certificate representation.
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace RetainedExponentAggregation

universe u v w x

/-- Retained contribution of a family of three-way bottleneck groups. -/
noncomputable def familyExponent {Group : Type u} [Fintype Group]
    (rate : Group → Fin 3 → ℝ) : ℝ :=
  ∑ group, RegionalExponent.threeWayMin (rate group)

/-- Sum of independently certified common branch floors. -/
noncomputable def familyFloor {Group : Type u} [Fintype Group]
    (floor : Group → ℝ) : ℝ :=
  ∑ group, floor group

/-- A common lower bound for all three branches is a lower bound for their bottleneck. -/
theorem floor_le_threeWayMin {rate : Fin 3 → ℝ} {floor : ℝ}
    (h : ∀ branch, floor ≤ rate branch) :
    floor ≤ RegionalExponent.threeWayMin rate := by
  unfold RegionalExponent.threeWayMin
  exact le_min (h 0) (le_min (h 1) (h 2))

/-- Componentwise common floors add to a lower bound for the retained family exponent. -/
theorem familyFloor_le_familyExponent
    {Group : Type u} [Fintype Group]
    (rate : Group → Fin 3 → ℝ) (floor : Group → ℝ)
    (hfloor : ∀ group branch, floor group ≤ rate group branch) :
    familyFloor floor ≤ familyExponent rate := by
  classical
  unfold familyFloor familyExponent
  apply Finset.sum_le_sum
  intro group _hgroup
  exact floor_le_threeWayMin (hfloor group)

/-- Retained exponent obtained by adding four independently indexed recursive families. -/
noncomputable def fourFamilyExponent
    {Root : Type u} {LevelFour : Type v} {LevelThree : Type w} {LevelTwo : Type x}
    [Fintype Root] [Fintype LevelFour] [Fintype LevelThree] [Fintype LevelTwo]
    (rootRate : Root → Fin 3 → ℝ)
    (levelFourRate : LevelFour → Fin 3 → ℝ)
    (levelThreeRate : LevelThree → Fin 3 → ℝ)
    (levelTwoRate : LevelTwo → Fin 3 → ℝ) : ℝ :=
  familyExponent rootRate + familyExponent levelFourRate +
    familyExponent levelThreeRate + familyExponent levelTwoRate

/-- Sum of common floors across the same four recursive families. -/
noncomputable def fourFamilyFloor
    {Root : Type u} {LevelFour : Type v} {LevelThree : Type w} {LevelTwo : Type x}
    [Fintype Root] [Fintype LevelFour] [Fintype LevelThree] [Fintype LevelTwo]
    (rootFloor : Root → ℝ)
    (levelFourFloor : LevelFour → ℝ)
    (levelThreeFloor : LevelThree → ℝ)
    (levelTwoFloor : LevelTwo → ℝ) : ℝ :=
  familyFloor rootFloor + familyFloor levelFourFloor +
    familyFloor levelThreeFloor + familyFloor levelTwoFloor

/-- Four-level composition theorem used by a generated recursive exponent checker.

Every hypothesis is local to one group and one branch; the conclusion contains all minima and
all finite sums.  Thus a data-heavy client never has to unfold nested `min` expressions. -/
theorem fourFamilyFloor_le_fourFamilyExponent
    {Root : Type u} {LevelFour : Type v} {LevelThree : Type w} {LevelTwo : Type x}
    [Fintype Root] [Fintype LevelFour] [Fintype LevelThree] [Fintype LevelTwo]
    (rootRate : Root → Fin 3 → ℝ)
    (levelFourRate : LevelFour → Fin 3 → ℝ)
    (levelThreeRate : LevelThree → Fin 3 → ℝ)
    (levelTwoRate : LevelTwo → Fin 3 → ℝ)
    (rootFloor : Root → ℝ)
    (levelFourFloor : LevelFour → ℝ)
    (levelThreeFloor : LevelThree → ℝ)
    (levelTwoFloor : LevelTwo → ℝ)
    (hroot : ∀ group branch, rootFloor group ≤ rootRate group branch)
    (hlevelFour : ∀ group branch,
      levelFourFloor group ≤ levelFourRate group branch)
    (hlevelThree : ∀ group branch,
      levelThreeFloor group ≤ levelThreeRate group branch)
    (hlevelTwo : ∀ group branch,
      levelTwoFloor group ≤ levelTwoRate group branch) :
    fourFamilyFloor rootFloor levelFourFloor levelThreeFloor levelTwoFloor ≤
      fourFamilyExponent rootRate levelFourRate levelThreeRate levelTwoRate := by
  have h₀ := familyFloor_le_familyExponent rootRate rootFloor hroot
  have h₄ := familyFloor_le_familyExponent levelFourRate levelFourFloor hlevelFour
  have h₃ := familyFloor_le_familyExponent levelThreeRate levelThreeFloor hlevelThree
  have h₂ := familyFloor_le_familyExponent levelTwoRate levelTwoFloor hlevelTwo
  unfold fourFamilyFloor fourFamilyExponent
  linarith

end RetainedExponentAggregation
end AlgebraicComplexity
