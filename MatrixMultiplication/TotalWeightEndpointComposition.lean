/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedSequencePackaging
import MatrixMultiplication.TotalQuotientExponentStrictFloorBridge
import MatrixMultiplication.TotalWeightEventualVolumeLossEndpoint

set_option autoImplicit false

/-!
# The `ω < 2.36999` composition, and the milestone's machine-readable residual

This module is the volume-only total-weight milestone's **final composition**.  It contains no
mathematics of its own: every step is an application of a committed theorem.  Its purpose is that
`omega_lt_236999_final` below has a hypothesis list which *is* the residual — the exact set of
statements that still have to be proved for `ω < 2.36999` to become unconditional, each written in
the vocabulary of the module that owns it.

## The residual, in four hypotheses

`omega_lt_236999_final` takes exactly four inputs.

* `hroot`, `hlevelFour`, `hlevelThree` — the **A-family**: the three outer componentwise floor
  dominations.  They are copied verbatim from
  `TotalQuotientExponentStrictFloorBridge.coarseFourFamilyFloor_lt_fourFamilyExponent`, which in
  turn copies them from the committed non-strict
  `TotalQuotientExponentStageAggregation.coarseFourFamilyFloor_le_fourFamilyExponent`.  A landing
  that proves `A2`/`A3`/`A4` in the scoped shape
  (`better_bound/r4_scoping/OBLIGATIONS.md` §2, Group A) discharges them without an adapter.
  There is deliberately **no** level-two hypothesis: the level-two family is discharged outright by
  the compact grouped certificate inside the strict bridge.

* `stages` — the **B/C-group**: one tail-native stage-data object, at the concrete semantic
  four-family retained exponent and at nominal mean rectangular-volume exponent `6`.  It is
  `AlgebraicComplexity.EventualWholeConstituentLaserVolumeLossData`, the interface of
  `AlgebraicComplexity/MatrixMultiplication/EventualWholeConstituentLaserVolumeLoss.lean`, so it
  asks for stages only past a cutoff and allows an explicit subexponential loss in **both** the
  copy count and the integral rectangular volume.  It is reached from an exact recursive division
  tree by the committed
  `EventualExactInterfaceDivisionStageData.toEventualWholeConstituentLaserVolumeLossData`, and from
  a cleanup stage family by `WholeConstituentLaserVolumeStage.precompose` through the committed
  source bridge; nothing in this module asks for an assembled degeneration, a level-two rate, a
  positivity witness, a volume floor, or a finite prefix.

Everything else the milestone needs — Schönhage's inequality, the border-rank certificate of
`CW₅⁸`, the regularization bridge, the laser-rate limit, the strict level-two floor, the rational
margin arithmetic, and the `6 → 5.999` volume backoff — is already committed and is discharged
here, not assumed.

## What `sourcePower` is, and what it is not

`stages` is an **already transported** family: its source is literally the endpoint's honest
tensor `Tensor.power (coppersmithWinograd K 5) sourcePower`, so its stage at repetition `r` lives
on `(CW₅⊗ sourcePower)⊗(strideValue · r)` and its **final CW-letter exponent is**
`sourcePower * (strideValue * r) = 304 · r`, recorded as `sourceLetters_eq` below.

`sourcePower` here is that CW power of the endpoint's source and nothing else.  It is **not** a
recursive division tree's `blockPower`, and this module deliberately exposes no `blockPower` field:
a producer is free to use any `P`, `encode`, `blockPower` and root multiplicity — for the accepted
chunk adapters over `cwChunkPartitionedTensor K 5 depth` the natural blocked-power parameter is one
chunk — provided the `304 · r` invariant holds after the chunk/source isomorphism
(`cwChunkPartitionedTensor_isomorphic_power`) has been applied.  Transporting the family across
that isomorphism is the producer's step; `WholeConstituentLaserVolumeStage.precompose` and the
committed source bridge are what perform it.

## Which committed theorems are composed, and in which direction

```text
  hroot, hlevelFour, hlevelThree
      │  TotalQuotientExponentStrictFloorBridge.coarseFourFamilyFloor_lt_fourFamilyExponent
      ▼
  coarseFourFamilyFloor < fourFamilyRetainedExponent …          (strict; `.le` is what is used)
      │
      ├──────────────────────────────► TotalWeightEventualVolumeLossEndpoint
      │                                  .omega_lt_236999_of_eventualStages   ◄── `stages`
      │                                     ▼
      │                                omega K < 2.36999
      │
      └─ Growth.Subexponential.exists_forall_pow_le_natCast_of_pow_le_mul (needs the *strict* gap)
             ▼
         SimplifiedSequencePackaging.RetainedCountValid retainedFloor …
```

The right-hand branch is the milestone.  The bottom branch is `exists_retainedCountValid_of_…`
below: it is the strict bridge's named count-side client, and it is **not** on the milestone's
path — see the honest note attached to it.

## Why the endpoint is the eventual/loss one and not the sequence packaging

`SimplifiedSequencePackaging.TotalWeightTrackResidual` is a *stronger* residual than the one taken
here: its `RetainedExtractionValid` conjunct demands a degeneration at **every** positive
repetition, and its `RetainedCountValid` conjunct demands a **loss-free** count.  The eventual
interface asks for neither.  Since both endpoints prove the same conclusion from committed
arithmetic, the composition is stated at the weaker hypothesis, and the packaging is imported only
for its stride/source constants and for the count-side converter below.

## The strict bridge is cited, and what it is actually spent on

The retained-floor comparison the eventual endpoint needs is non-strict, so the milestone consumes
`coarseFourFamilyFloor_lt_fourFamilyExponent … |>.le`; the eventual endpoint absorbs `copyLoss`
through `Growth.Subexponential.exists_ge_pos_log_le_mul`, i.e. into the laser rate's own `ε`, and
therefore does **not** need the strict gap.  The strict gap is what buys a *loss-free* count, and
that is `exists_retainedCountValid_of_fourFamilyCopyGrowth`, where
`Growth.Subexponential.exists_forall_pow_le_natCast_of_pow_le_mul`'s `lowerBase < base` is a real
premise.  Its rational witness is branch 2's certified slack
`1345218400141681 / 4294967296000000000000 ≈ 3.132e-07` — a lower bound for the guaranteed strict
gap, not the value of `fourFamilyExponent … − coarseFourFamilyFloor`.

## Pinned constants

`sourcePower = 8`, `strideValue = 38`, `nominalVolume = 6`, `acceptanceTarget = 236999/100000`,
`retainedFloor = coarseFourFamilyFloor = 8.241973`.  No numerical datum is introduced here.
-/

namespace MatrixMultiplication.TotalWeightEndpointComposition

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.RetainedExponentAggregation
open MatrixMultiplication.Generated.TotalQuotientExponentStageFloors
open MatrixMultiplication.SimplifiedSequencePackaging (sourcePower strideValue strideValue_pos)
open MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedProvenance
open MatrixMultiplication.TotalQuotientExponentStrictFloorBridge

universe u

noncomputable section

/-! ## The audited source invariant -/

/-- **The source invariant of the composition.**  A stage of `stages` at repetition `r` lives on
`Tensor.power (Tensor.power (coppersmithWinograd K 5) sourcePower) (strideValue * r)`, whose CW
letter count is `sourcePower * (strideValue * r) = 304 · r`.

This — not any numeric field of a producer's division tree — is the quantity a producer has to
match, and it is `SimplifiedSequencePackaging.strideBlockLetters` per repetition, the same constant
the packaging's chunk alignment `strideBlock_chunkAlignment` is stated at. -/
theorem sourceLetters_eq (r : ℕ) :
    sourcePower * (strideValue * r) =
      MatrixMultiplication.SimplifiedSequencePackaging.strideBlockLetters * r := by
  rw [← Nat.mul_assoc, MatrixMultiplication.SimplifiedSequencePackaging.strideBlockLetters_eq]

/-- The same invariant with the constant spelled out: `304 · r` CW letters per repetition. -/
theorem sourceLetters_eq_304 (r : ℕ) : sourcePower * (strideValue * r) = 304 * r :=
  sourceLetters_eq r

/-! ## The semantic retained exponent the count side must realize -/

/-- **The concrete four-family retained exponent of the `e7987` total-weight candidate.**

The three outer families are carried by the rates a client supplies; the level-two family is the
compact grouped certificate's own
`TotalQuotientExponentLevelTwoRecurrence.familyRate certifiedTables certifiedMassThree`, which is
*not* a parameter — it is the certificate the strict bridge discharges outright.

This is the exponent the counting construction has to realize, and it is the only place where the
A-family rates and the B/C-group's copy base meet. -/
def fourFamilyRetainedExponent
    (rootRate levelFourRate levelThreeRate : Region → Fin 3 → ℝ) : ℝ :=
  fourFamilyExponent rootRate levelFourRate levelThreeRate
    (TotalQuotientExponentLevelTwoRecurrence.familyRate certifiedTables certifiedMassThree)

/-- The committed stage-floor sum lies strictly below the semantic four-family retained exponent.

Verbatim `TotalQuotientExponentStrictFloorBridge.coarseFourFamilyFloor_lt_fourFamilyExponent`,
restated through `fourFamilyRetainedExponent` so that the composition below reads in one
vocabulary. -/
theorem coarseFourFamilyFloor_lt_fourFamilyRetainedExponent
    (rootRate levelFourRate levelThreeRate : Region → Fin 3 → ℝ)
    (hroot : ∀ region branch, rootFloor region ≤ rootRate region branch)
    (hlevelFour : ∀ region branch, levelFourFloor region ≤ levelFourRate region branch)
    (hlevelThree : ∀ region branch, levelThreeFloor region ≤ levelThreeRate region branch) :
    coarseFourFamilyFloor <
      fourFamilyRetainedExponent rootRate levelFourRate levelThreeRate :=
  coarseFourFamilyFloor_lt_fourFamilyExponent rootRate levelFourRate levelThreeRate
    hroot hlevelFour hlevelThree

/-- The retained floor the endpoint is pinned at is dominated by the semantic retained exponent.

This is the exact comparison `TotalWeightEventualVolumeLossEndpoint.omega_lt_236999_of_eventualStages`
consumes; it is the strict bridge's `≤` shadow, and no separate numerical hypothesis replaces it. -/
theorem retainedFloor_le_fourFamilyRetainedExponent
    (rootRate levelFourRate levelThreeRate : Region → Fin 3 → ℝ)
    (hroot : ∀ region branch, rootFloor region ≤ rootRate region branch)
    (hlevelFour : ∀ region branch, levelFourFloor region ≤ levelFourRate region branch)
    (hlevelThree : ∀ region branch, levelThreeFloor region ≤ levelThreeRate region branch) :
    MatrixMultiplication.TotalWeightVolumeLossEndpoint.retainedFloor ≤
      fourFamilyRetainedExponent rootRate levelFourRate levelThreeRate :=
  (coarseFourFamilyFloor_lt_fourFamilyRetainedExponent rootRate levelFourRate levelThreeRate
    hroot hlevelFour hlevelThree).le

/-! ## The composition -/

/-- **The milestone, over one field.**

Four named inputs and nothing else: the three outer componentwise floor dominations, and one
tail-native eventual whole-constituent stage family on the honest source `(CW₅⁸)^(38·r)` whose copy
base is the semantic four-family retained exponent and whose volume base is the nominal mean
rectangular-volume exponent `6`.

Both losses in `stages` are the client's own and may be any subexponential functions; the endpoint
absorbs the copy loss into the laser rate and the volume loss into the committed `6 → 5.999`
backoff, whose exact residual margin is `17590838479/25000000000000 = 7.0363353916e-4 > 0`. -/
theorem omega_lt_236999_of_eventualStageFamily (K : Type u) [Field K]
    (rootRate levelFourRate levelThreeRate : Region → Fin 3 → ℝ)
    (hroot : ∀ region branch, rootFloor region ≤ rootRate region branch)
    (hlevelFour : ∀ region branch, levelFourFloor region ≤ levelFourRate region branch)
    (hlevelThree : ∀ region branch, levelThreeFloor region ≤ levelThreeRate region branch)
    (stages : EventualWholeConstituentLaserVolumeLossData K
      (Tensor.power (coppersmithWinograd K 5) sourcePower) strideValue
      ((2 : ℝ) ^ ((strideValue : ℝ) *
        fourFamilyRetainedExponent rootRate levelFourRate levelThreeRate))
      ((2 : ℝ) ^ (3 * (strideValue : ℝ) *
        MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume))) :
    omega K < MatrixMultiplication.TotalWeightVolumeLossEndpoint.acceptanceTarget :=
  MatrixMultiplication.TotalWeightEventualVolumeLossEndpoint.omega_lt_236999_of_eventualStages
    K stages
    (retainedFloor_le_fourFamilyRetainedExponent rootRate levelFourRate levelThreeRate
      hroot hlevelFour hlevelThree)

/-- **THE FINAL COMPOSITION THEOREM OF THE VOLUME-ONLY `ω < 2.36999` MILESTONE.**

Its hypothesis list is the milestone's residual, and the conclusion is exactly the shape of the
leaderboard's primary generality class `Frontier.OmegaBound (236999/100000)`: `ω < 2.36999` over
every field, in every universe.  (`Frontier.lean` is a leaf that no library may import, so the
shape is written out rather than cited.)

Discharging the four hypotheses — three componentwise dominations and one eventual stage family —
turns this into an unconditional record.  Nothing else remains. -/
theorem omega_lt_236999_final
    (rootRate levelFourRate levelThreeRate : Region → Fin 3 → ℝ)
    (hroot : ∀ region branch, rootFloor region ≤ rootRate region branch)
    (hlevelFour : ∀ region branch, levelFourFloor region ≤ levelFourRate region branch)
    (hlevelThree : ∀ region branch, levelThreeFloor region ≤ levelThreeRate region branch)
    (stages : ∀ (K : Type u) [Field K],
      EventualWholeConstituentLaserVolumeLossData K
        (Tensor.power (coppersmithWinograd K 5) sourcePower) strideValue
        ((2 : ℝ) ^ ((strideValue : ℝ) *
          fourFamilyRetainedExponent rootRate levelFourRate levelThreeRate))
        ((2 : ℝ) ^ (3 * (strideValue : ℝ) *
          MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume))) :
    ∀ (K : Type u) [Field K], omega K < (236999 / 100000 : ℝ) := by
  intro K _
  have hendpoint :
      MatrixMultiplication.TotalWeightVolumeLossEndpoint.acceptanceTarget
        = (236999 / 100000 : ℝ) := rfl
  have hbound := omega_lt_236999_of_eventualStageFamily K
    rootRate levelFourRate levelThreeRate hroot hlevelFour hlevelThree (stages K)
  rwa [hendpoint] at hbound

/-! ## The strict bridge's count-side client

Not on the milestone's path; see the module docstring. -/

/-- **From a lossy count at the four-family copy base to a loss-free `RetainedCountValid`.**

This is `OBLIGATIONS.md` §2 B4 in its generic form, and it is the one place where the strict bridge
is spent on strictness rather than on its `≤` shadow: the absorption theorem
`Growth.Subexponential.exists_forall_pow_le_natCast_of_pow_le_mul` needs `lowerBase < base`, and
`retainedCopyBase_lt_fourFamilyCopyBase` at `stride := strideValue` supplies exactly that pair of
bases.

The input is what a recursive construction naturally produces — `base ^ r ≤ loss r * count r` past
a cutoff, with `loss` subexponential — and the output is the loss-free eventual bound
`SimplifiedSequencePackaging.RetainedCountValid` asks for at the committed floor `8.241973`.

It is stated because the packaging endpoint remains available and because the milestone's board
record cites the strict bridge; it is **not** used by `omega_lt_236999_final`, whose endpoint
absorbs the copy loss without any strict gap. -/
theorem exists_retainedCountValid_of_fourFamilyCopyGrowth
    (rootRate levelFourRate levelThreeRate : Region → Fin 3 → ℝ)
    (hroot : ∀ region branch, rootFloor region ≤ rootRate region branch)
    (hlevelFour : ∀ region branch, levelFourFloor region ≤ levelFourRate region branch)
    (hlevelThree : ∀ region branch, levelThreeFloor region ≤ levelThreeRate region branch)
    {count : ℕ → ℕ} {copyLoss : ℕ → ℝ} {cutoff : ℕ}
    (hloss : Growth.Subexponential copyLoss)
    (hcount : ∀ r, 0 < r → 0 < count r)
    (hgrowth : ∀ r, cutoff ≤ r → 0 < r →
      ((2 : ℝ) ^ ((strideValue : ℝ) *
        fourFamilyRetainedExponent rootRate levelFourRate levelThreeRate)) ^ r ≤
        copyLoss r * (count r : ℝ)) :
    ∃ lossFreeCutoff : ℕ,
      MatrixMultiplication.SimplifiedSequencePackaging.RetainedCountValid
        MatrixMultiplication.SimplifiedSequencePackaging.retainedFloor lossFreeCutoff count := by
  have hstride : (0 : ℝ) < (strideValue : ℝ) := by exact_mod_cast strideValue_pos
  obtain ⟨absorbCutoff, habsorb⟩ :=
    hloss.exists_forall_pow_le_natCast_of_pow_le_mul
      (Real.rpow_pos_of_pos (by norm_num) _)
      (retainedCopyBase_lt_fourFamilyCopyBase (strideValue : ℝ) hstride
        rootRate levelFourRate levelThreeRate hroot hlevelFour hlevelThree)
  refine ⟨max cutoff absorbCutoff, hcount, ?_⟩
  intro r hr hrpos
  exact habsorb r (count r) ((le_max_right cutoff absorbCutoff).trans hr)
    (hgrowth r ((le_max_left cutoff absorbCutoff).trans hr) hrpos)

end

end MatrixMultiplication.TotalWeightEndpointComposition
