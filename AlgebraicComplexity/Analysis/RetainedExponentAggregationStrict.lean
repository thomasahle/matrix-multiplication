/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.RetainedExponentAggregation

/-!
# Strict aggregation of certified floors for retained exponents

`AlgebraicComplexity/Analysis/RetainedExponentAggregation.lean` turns componentwise certified
floors into a lower bound for a summed retained exponent.  Every inequality there is `≤`, and for
the copy-growth clients that is one epsilon too weak.

## Why a strict sum is needed

A counting client converts a family exponent `E` into a copy base `2 ^ (stride · E)` and asks
`AlgebraicComplexity/Analysis/CopyGrowth.lean` for a loss-free eventual count.  The available
theorem is

```text
Growth.Subexponential.exists_forall_pow_le_natCast_of_pow_le_mul :
  Subexponential loss → 0 < lowerBase → lowerBase < base →
    ∃ cutoff, ∀ k copies, cutoff ≤ k → base ^ k ≤ loss k * copies → lowerBase ^ k ≤ copies
```

whose `lowerBase < base` is *strict*: a subexponential ambient loss can only be absorbed into a
genuine gap between the base the construction grows at and the base the packaging exports.  If the
certified floor merely satisfies `floor ≤ E`, the two bases may coincide and no cutoff exists.  So
the packaging's floor must be **strictly** below the semantic family exponent, and this module is
the generic half of that upgrade.

## What is proved

Each statement is the exact strict analogue of one non-strict theorem next door, and they compose
the same way:

* `lt_threeWayMin` — a common strict lower bound for all three directional branches is a strict
  lower bound for their bottleneck (the strict `RegionalExponent.le_threeWayMin`);
* `familyFloor_lt_familyExponent` — over a **nonempty** family, componentwise strictness sums
  (`Finset.sum_lt_sum_of_nonempty`; emptiness is the only obstruction, an empty sum being `0 < 0`);
* `fourFamilyFloor_lt_fourFamilyExponent_of_familyBounds` — **one strict summand and three
  non-strict ones give a strict four-family sum**.  This is the shape a client actually has: only
  one of the four recursive stages ever carries a certificate with a strict margin, and the other
  three are transferred at `≤`;
* `fourFamilyFloor_lt_fourFamilyExponent_of_levelTwo` — the componentwise corollary, with level two
  as the strict family.

Level two is where the strictness is spent because it is the one stage whose branch floors come
from an exact rational certificate; the statement is fixed at that position only for the client's
convenience.  Any other position is the same `linarith` over
`fourFamilyFloor_lt_fourFamilyExponent_of_familyBounds`'s four family-level hypotheses, with the
strict one moved — no new lemma about `threeWayMin` or about finite sums is involved.

Like its non-strict neighbour this module is independent of any tensor, of any certificate
representation, and of the names "root", "level four", "level three", "level two".
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace RetainedExponentAggregation

universe u v w x

/-- A value strictly below all three directional branches is strictly below their bottleneck.

The strict analogue of `RegionalExponent.le_threeWayMin`, and like it stated over an arbitrary
linear order. -/
theorem lt_threeWayMin {α : Type*} [LinearOrder α] {a : α} {f : Fin 3 → α}
    (h : ∀ branch, a < f branch) :
    a < RegionalExponent.threeWayMin f :=
  lt_min (h 0) (lt_min (h 1) (h 2))

/-- Componentwise **strict** common floors add to a strict lower bound for the retained family
exponent.

`Nonempty` is essential and not a technicality: over an empty family both sides are the empty sum
`0`, so no strict inequality can hold. -/
theorem familyFloor_lt_familyExponent
    {Group : Type u} [Fintype Group] [Nonempty Group]
    (rate : Group → Fin 3 → ℝ) (floor : Group → ℝ)
    (hfloor : ∀ group branch, floor group < rate group branch) :
    familyFloor floor < familyExponent rate := by
  classical
  unfold familyFloor familyExponent
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty ?_
  intro group _hgroup
  exact lt_threeWayMin (hfloor group)

/-- **One strict family makes the four-family sum strict.**  Three of the four recursive stages are
transferred at `≤` and one — here level two — at `<`.

This is the generic bridge a copy-growth client needs: `fourFamilyFloor_le_fourFamilyExponent`
leaves the certified floor and the semantic exponent possibly equal, and a subexponential ambient
loss cannot be absorbed into a zero gap. -/
theorem fourFamilyFloor_lt_fourFamilyExponent_of_familyBounds
    {Root : Type u} {LevelFour : Type v} {LevelThree : Type w} {LevelTwo : Type x}
    [Fintype Root] [Fintype LevelFour] [Fintype LevelThree] [Fintype LevelTwo]
    {rootRate : Root → Fin 3 → ℝ}
    {levelFourRate : LevelFour → Fin 3 → ℝ}
    {levelThreeRate : LevelThree → Fin 3 → ℝ}
    {levelTwoRate : LevelTwo → Fin 3 → ℝ}
    {rootFloor : Root → ℝ}
    {levelFourFloor : LevelFour → ℝ}
    {levelThreeFloor : LevelThree → ℝ}
    {levelTwoFloor : LevelTwo → ℝ}
    (hroot : familyFloor rootFloor ≤ familyExponent rootRate)
    (hlevelFour : familyFloor levelFourFloor ≤ familyExponent levelFourRate)
    (hlevelThree : familyFloor levelThreeFloor ≤ familyExponent levelThreeRate)
    (hlevelTwo : familyFloor levelTwoFloor < familyExponent levelTwoRate) :
    fourFamilyFloor rootFloor levelFourFloor levelThreeFloor levelTwoFloor <
      fourFamilyExponent rootRate levelFourRate levelThreeRate levelTwoRate := by
  unfold fourFamilyFloor fourFamilyExponent
  linarith

/-- The componentwise form of the strict four-family sum: per-group, per-branch domination of the
certified floors, strict on the level-two family and non-strict on the other three.

Same argument order as `fourFamilyFloor_le_fourFamilyExponent`, so a client upgrades by replacing
`hlevelTwo` and nothing else. -/
theorem fourFamilyFloor_lt_fourFamilyExponent_of_levelTwo
    {Root : Type u} {LevelFour : Type v} {LevelThree : Type w} {LevelTwo : Type x}
    [Fintype Root] [Fintype LevelFour] [Fintype LevelThree] [Fintype LevelTwo]
    [Nonempty LevelTwo]
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
      levelTwoFloor group < levelTwoRate group branch) :
    fourFamilyFloor rootFloor levelFourFloor levelThreeFloor levelTwoFloor <
      fourFamilyExponent rootRate levelFourRate levelThreeRate levelTwoRate :=
  fourFamilyFloor_lt_fourFamilyExponent_of_familyBounds
    (familyFloor_le_familyExponent rootRate rootFloor hroot)
    (familyFloor_le_familyExponent levelFourRate levelFourFloor hlevelFour)
    (familyFloor_le_familyExponent levelThreeRate levelThreeFloor hlevelThree)
    (familyFloor_lt_familyExponent levelTwoRate levelTwoFloor hlevelTwo)

end RetainedExponentAggregation
end AlgebraicComplexity
