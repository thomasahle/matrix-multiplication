/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MergedRationalTypedLeaf
import MatrixMultiplication.SimplifiedSequencePackaging

set_option autoImplicit false

/-!
# The merged leaf against the total-weight track's per-leg bit budgets

## What this module is

`MatrixMultiplication/FineAddressStage.lean` says of itself: *"It is not C1b. … The fine reading
formalized here carries `637.586` bits per stride block against the `683.852` the milestone needs,
so it is not on its own a route to `ω < 2.36999`."*  This module is the other half of that sentence:
the arithmetic and the composition by which a **merged** leaf — one whose designated leg carries a
zero-coordinate class's merged dimension `∑ s ∈ cls, 5 ^ ones s` rather than one representative's
`5 ^ ones s` — meets the per-leg budgets `(225, 227, 232)` that the fine reading misses.

It contains three things and no certificate table.

* **The census, as checked arithmetic.**  E2's per-leg FINE floors and merge gains, in CW leg
  order, with `fineLeafBits + mergedGainBits = budget` on each leg
  (`xFineLeafBits_add_xMergedGainBits` and its two siblings) and the three **negative controls**
  `xExponentBudget_not_le_xFineLeafBits`, … which turn E2's obstruction into theorems: the fine
  reading misses its budget on *every* leg, not only in total.
* **The leg convention, again as theorems.**  `legBudgetOfLeg` indexes the committed budgets by a
  `Leg` — which is how a `MergedRationalTypedLeaf.mergeLeg` is spelled — and
  `legBudgetOfLeg_legOfCertificateCoordinateLeg` connects it to E1's certificate volume-coordinate
  publication order through `SimplifiedSequencePackaging.legOfCertificateCoordinate`.  So a merged
  leaf that merges the certificate's zero coordinate `c` and a budget triple in leg order are
  paired by a proved rotation and never by hand.
* **The composition.**  `totalWeightTrackResidual_of_mergedStageFamily` and
  `omega_lt_236999_of_mergedStageFamily_at_floor`: a family of whole-constituent stages whose three
  side lengths clear the budgets, plus a retained count, *is* the milestone.  Every remaining
  obligation is one named hypothesis of those two theorems.

## The named hypotheses, and who owns them

`omega_lt_236999_of_mergedStageFamily_at_floor` has exactly two:

1. `hcount : RetainedCountValid retainedFloor cutoff count` — the counting cone's obligation
   (B group).  `FineAddressStage` already discharges everything *below* the cutoff.
2. `stage` — a merged whole-constituent stage at every repetition, with sides at least
   `(2 ^ (225 r), 2 ^ (227 r), 2 ^ (232 r))`.  This is what C1b items 8--9 build:
   `Examples.cwTotalWeightMergedCleanupStage` produces the stage from the relaxed cleanup, its
   source is bridged to `((CW₅^⊗8)^⊗38)^⊗r` by `Tensor.Restricts.power_partitionedPositivePower`
   plus `strideBlock_chunkAlignment` and `WholeConstituentLaserVolumeStage.precompose`, and the
   three side inequalities come from `leafBase_pow_mul_le_mergedDimensionProduct` below, whose
   hypothesis is E2's per-leg accounting `budget ≤ fine bits + class-cardinality bits`.  Its own
   residual premise is the per-letter merged degeneration, which rests on the shared-`Z` map
   coherence of `OBLIGATIONS.md` §9.9 (codex-2.36x's zero-dimension tranche).

## Honest gap

Nothing here is an unconditional bound and no certificate inequality moves.  In particular the
census constants below are E2's *measurements* named as Lean constants: `xFineLeafBits = 209` is
`⌊209.928424990⌋` and `xMergedGainBits = 16` is `⌈15.071575010⌉` from
`better_bound/r4_scoping/E2_LATTICE.md` §1, not quantities derived inside Lean from the certificate.
What *is* proved here is that those three splits are consistent with the committed budgets, that
the fine halves alone are not, and that a stage family at the merged sides closes the milestone.
Deriving the census from the certificate's own tables is the per-stage semantic identification and
is not attempted.
-/

namespace MatrixMultiplication.MergedLeafBudget

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedSequencePackaging

universe u v w

/-! ## The per-leg budgets, indexed by a `Leg`

`MergedRationalTypedLeaf.mergeLeg` is a `Leg`, while `SimplifiedSequencePackaging.legBudget` is
indexed by `Fin 3`.  The three declarations below make the identification and carry it through to
E1's certificate volume-coordinate order, so that "the merged leg is the certificate's zero
coordinate `c`" and "its budget is `certificateCoordinateBudget c`" are the same statement. -/

/-- The committed per-leg bit budgets, indexed by the matrix-shape leg. -/
def legBudgetOfLeg : Leg → ℕ
  | .X => xExponentBudget
  | .Y => yExponentBudget
  | .Z => zExponentBudget

@[simp] theorem legBudgetOfLeg_X : legBudgetOfLeg .X = xExponentBudget := rfl
@[simp] theorem legBudgetOfLeg_Y : legBudgetOfLeg .Y = yExponentBudget := rfl
@[simp] theorem legBudgetOfLeg_Z : legBudgetOfLeg .Z = zExponentBudget := rfl

/-- The numbering of the three legs used by `SimplifiedSequencePackaging.legBudget`. -/
def legIndex : Leg → Fin 3
  | .X => 0
  | .Y => 1
  | .Z => 2

theorem legBudgetOfLeg_eq_legBudget (c : Leg) : legBudgetOfLeg c = legBudget (legIndex c) := by
  cases c <;> rfl

/-- The matrix-shape leg of a certificate volume coordinate, as a `Leg`.  This is
`SimplifiedSequencePackaging.legOfCertificateCoordinate` read through `legIndex`. -/
def legOfCertificateCoordinateLeg : Fin 3 → Leg
  | 0 => .Z
  | 1 => .X
  | 2 => .Y

theorem legIndex_legOfCertificateCoordinateLeg (c : Fin 3) :
    legIndex (legOfCertificateCoordinateLeg c) = legOfCertificateCoordinate c := by
  fin_cases c <;> rfl

/-- **The leg convention for a merged leaf, as a theorem.**  A merged leaf that merges the
certificate's zero coordinate `c` carries its merged dimension on the leg
`legOfCertificateCoordinateLeg c`, whose committed budget is exactly the budget E1 publishes at
coordinate `c`.  Neither triple is ever hand-copied into the other's indexing. -/
theorem legBudgetOfLeg_legOfCertificateCoordinateLeg (c : Fin 3) :
    legBudgetOfLeg (legOfCertificateCoordinateLeg c) = certificateCoordinateBudget c := by
  rw [legBudgetOfLeg_eq_legBudget, legIndex_legOfCertificateCoordinateLeg,
    legBudget_legOfCertificateCoordinate]

/-- The three leg budgets total the committed leaf budget `684`. -/
theorem legBudgetOfLeg_add :
    legBudgetOfLeg .X + legBudgetOfLeg .Y + legBudgetOfLeg .Z = leafExponentBudget :=
  leafExponentBudget_eq

/-! ## E2's census: the fine floors, the merge gains, and the three negative controls

`better_bound/r4_scoping/E2_LATTICE.md` §1 publishes both readings in the certificate's volume
coordinate order; the constants below are that table **rotated into CW leg order**, exactly as
`FineAddressStage`'s letter constants are.  The FINE row `(215.742954773, 209.928424990,
211.914585974)` at coordinates `(0, 1, 2)` is the leg triple `(209.928…, 211.914…, 215.742…)`, and
E2's per-leg shortfalls `(−16.257045227, −15.071575010, −15.085414026)` are the leg triple
`(15.071…, 15.085…, 16.257…)` in magnitude.  Flooring the first and rounding the second up gives
three exact integer splits of the committed budgets. -/

/-- `⌊209.928424990⌋`: the bits the *fine* reading — `MergedRationalTypedLeaf.representativeLeaf`,
one representative address per zero class — puts on the `X` leg of one stride block. -/
def xFineLeafBits : ℕ := 209

/-- `⌊211.914585974⌋`: the fine reading's `Y` leg. -/
def yFineLeafBits : ℕ := 211

/-- `⌊215.742954773⌋`: the fine reading's `Z` leg. -/
def zFineLeafBits : ℕ := 215

/-- `⌈15.071575010⌉`: the bits the zero-coordinate merge must add on the `X` leg, i.e.
`log₂` of that leg's share of `MergedRationalTypedLeaf.classCardProduct`. -/
def xMergedGainBits : ℕ := 16

/-- `⌈15.085414026⌉`: the merge's `Y` leg. -/
def yMergedGainBits : ℕ := 16

/-- `⌈16.257045227⌉`: the merge's `Z` leg. -/
def zMergedGainBits : ℕ := 17

theorem xFineLeafBits_add_xMergedGainBits :
    xFineLeafBits + xMergedGainBits = xExponentBudget := by
  norm_num [xFineLeafBits, xMergedGainBits, xExponentBudget]

theorem yFineLeafBits_add_yMergedGainBits :
    yFineLeafBits + yMergedGainBits = yExponentBudget := by
  norm_num [yFineLeafBits, yMergedGainBits, yExponentBudget]

theorem zFineLeafBits_add_zMergedGainBits :
    zFineLeafBits + zMergedGainBits = zExponentBudget := by
  norm_num [zFineLeafBits, zMergedGainBits, zExponentBudget]

/-- The three merge gains total `49` bits per `38`-word stride block — the integer form of E2's
`46.414034263`, inflated by the three separate roundings. -/
theorem mergedGainBits_add :
    xMergedGainBits + yMergedGainBits + zMergedGainBits = 49 := by
  norm_num [xMergedGainBits, yMergedGainBits, zMergedGainBits]

/-- The fine floors and the merge gains split the committed leaf budget `684`. -/
theorem fineLeafBits_add_mergedGainBits :
    (xFineLeafBits + yFineLeafBits + zFineLeafBits) +
        (xMergedGainBits + yMergedGainBits + zMergedGainBits) = leafExponentBudget := by
  norm_num [xFineLeafBits, yFineLeafBits, zFineLeafBits,
    xMergedGainBits, yMergedGainBits, zMergedGainBits, leafExponentBudget]

/-- **E2's obstruction on the `X` leg, as a theorem.**  `225 ≤ 209` is false. -/
theorem xExponentBudget_not_le_xFineLeafBits : ¬ xExponentBudget ≤ xFineLeafBits := by
  norm_num [xExponentBudget, xFineLeafBits]

/-- **E2's obstruction on the `Y` leg.**  `227 ≤ 211` is false. -/
theorem yExponentBudget_not_le_yFineLeafBits : ¬ yExponentBudget ≤ yFineLeafBits := by
  norm_num [yExponentBudget, yFineLeafBits]

/-- **E2's obstruction on the `Z` leg.**  `232 ≤ 215` is false. -/
theorem zExponentBudget_not_le_zFineLeafBits : ¬ zExponentBudget ≤ zFineLeafBits := by
  norm_num [zExponentBudget, zFineLeafBits]

/-- **The fine reading fails the leaf interface.**  Not merely in total: `LeafExponentsValid` is
per leg, and the fine census misses on all three.  This is the E2 verdict in the packaging's own
vocabulary. -/
theorem not_leafExponentsValid_fine :
    ¬ LeafExponentsValid xExponentBudget yExponentBudget zExponentBudget
        xFineLeafBits yFineLeafBits zFineLeafBits := by
  intro hleaf
  exact xExponentBudget_not_le_xFineLeafBits hleaf.1

/-- **The merged reading meets it, exactly.**  Adding E2's three merge gains to the fine floors
gives the committed budgets on the nose. -/
theorem leafExponentsValid_merged :
    LeafExponentsValid xExponentBudget yExponentBudget zExponentBudget
      (xFineLeafBits + xMergedGainBits) (yFineLeafBits + yMergedGainBits)
      (zFineLeafBits + zMergedGainBits) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [xFineLeafBits_add_xMergedGainBits]
  · rw [yFineLeafBits_add_yMergedGainBits]
  · rw [zFineLeafBits_add_zMergedGainBits]

/-! ## From a budget at one stride block to every repetition -/

/-- One stride block's comparison is the comparison at `r` stride blocks: exact powers are
monotone. -/
theorem leafBase_pow_mul_le_pow {budget side : ℕ} (h : leafBase ^ budget ≤ side) (r : ℕ) :
    leafBase ^ (budget * r) ≤ side ^ r := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left h r

/-- **The merged dimension product pays the budget — against the fine reading, exactly.**

At uniform local powers the merged leaf's designated-leg dimension product *equals* the class
cardinality product times the fine (representative) leaf's, so the budget is met as soon as
`2 ^ budget` fits inside that product.  Taking `log₂`, the hypothesis reads

```
budget ≤ (fine bits on this leg) + ∑ i, count i · log₂ (card i)
```

which is exactly E2's per-leg accounting: the fine floor plus the zero blocks' support
multiplicity.  This is the inequality that converts E2's `46.414` bits of zero-block entropy into
leaf volume.

The `fine` leaf here is `MergedRationalTypedLeaf.representativeLeaf residual mergeLeg hq k`, i.e.
the residual leaf with each class's own `q ^ k i` put back on the designated leg; instantiating
`residual` itself with a fine leaf would double-count that power. -/
theorem leafBase_pow_mul_le_mergedDimensionProduct
    {I : Type u} {A : Leg → Type v} {ι : Type w}
    (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    {q : ℕ} (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) (k : I → ℕ)
    (huniform : ∀ i, ∀ s ∈ cls i, ones i s = k i) {budget : ℕ}
    (hbudget : leafBase ^ budget ≤
      MergedRationalTypedLeaf.classCardProduct residual.profile cls *
        (MergedRationalTypedLeaf.representativeLeaf residual mergeLeg hq k).dimensionProduct
          mergeLeg) (r : ℕ) :
    leafBase ^ (budget * r) ≤
      ((MergedRationalTypedLeaf.ofZeroClasses residual mergeLeg q hq ones cls
        hne).toRationalTypedLeaf.dimensionProduct mergeLeg) ^ r := by
  rw [MergedRationalTypedLeaf.dimensionProduct_mergeLeg_eq_classCardProduct_mul_representative
    residual mergeLeg hq ones cls hne k huniform]
  exact leafBase_pow_mul_le_pow hbudget r

/-- The residual-side form, with no uniformity hypothesis and a weaker conclusion: the comparison
is against the *residual* leaf, so it does not by itself say anything about E2's fine row. -/
theorem leafBase_pow_mul_le_mergedDimensionProduct_of_residual
    {I : Type u} {A : Leg → Type v} {ι : Type w}
    (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    {q : ℕ} (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) {budget : ℕ}
    (hbudget : leafBase ^ budget ≤
      MergedRationalTypedLeaf.classCardProduct residual.profile cls *
        residual.dimensionProduct mergeLeg) (r : ℕ) :
    leafBase ^ (budget * r) ≤
      ((MergedRationalTypedLeaf.ofZeroClasses residual mergeLeg q hq ones cls
        hne).toRationalTypedLeaf.dimensionProduct mergeLeg) ^ r :=
  le_trans (leafBase_pow_mul_le_pow hbudget r)
    (Nat.pow_le_pow_left
      (MergedRationalTypedLeaf.classCardProduct_mul_residual_le_dimensionProduct_mergeLeg
        residual mergeLeg hq ones cls hne) r)

/-! ## The composition -/

section Composition

variable (K : Type u) [Field K]

/-- **A merged stage family supplies the extraction interface.**

The three side lengths need only *dominate* the committed budgets at every repetition; the shrink
to the exact powers the interface asks for is `WholeConstituentLaserVolumeStage.shrinkDimensions`,
i.e. dimension monotonicity of `matrixMultiplication` applied inside the direct sum. -/
theorem retainedExtractionValid_of_mergedStageFamily
    {count : ℕ → ℕ} {xSide ySide zSide : ℕ → ℕ}
    (stage : ∀ r, 0 < r →
      WholeConstituentLaserVolumeStage.{u, u, 0} K
        (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (strideValue * r))
        (count r) (xSide r) (ySide r) (zSide r))
    (hx : ∀ r, 0 < r → leafBase ^ (xExponentBudget * r) ≤ xSide r)
    (hy : ∀ r, 0 < r → leafBase ^ (yExponentBudget * r) ≤ ySide r)
    (hz : ∀ r, 0 < r → leafBase ^ (zExponentBudget * r) ≤ zSide r) :
    RetainedExtractionValid K count xExponentBudget yExponentBudget zExponentBudget :=
  RetainedExtractionValid.of_stageFamily.{u, 0} fun r hr ↦
    (stage r hr).shrinkDimensions (hx r hr) (hy r hr) (hz r hr)

/-- **The whole tensor-side residual from a merged stage family and a retained count.**

`LeafExponentsValid` is met at the budgets themselves, so the milestone's three-part residual
reduces to the two named inputs below. -/
theorem totalWeightTrackResidual_of_mergedStageFamily
    {retained : ℝ} {cutoff : ℕ} {count : ℕ → ℕ} {xSide ySide zSide : ℕ → ℕ}
    (hcount : RetainedCountValid retained cutoff count)
    (stage : ∀ r, 0 < r →
      WholeConstituentLaserVolumeStage.{u, u, 0} K
        (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (strideValue * r))
        (count r) (xSide r) (ySide r) (zSide r))
    (hx : ∀ r, 0 < r → leafBase ^ (xExponentBudget * r) ≤ xSide r)
    (hy : ∀ r, 0 < r → leafBase ^ (yExponentBudget * r) ≤ ySide r)
    (hz : ∀ r, 0 < r → leafBase ^ (zExponentBudget * r) ≤ zSide r) :
    TotalWeightTrackResidual K retained :=
  ⟨cutoff, count, xExponentBudget, yExponentBudget, zExponentBudget, hcount,
    ⟨le_rfl, le_rfl, le_rfl⟩,
    retainedExtractionValid_of_mergedStageFamily K stage hx hy hz⟩

/-- **`ω < 2.36999` from a merged stage family at the committed retained floor.**

This is the milestone with its tensor side reduced to exactly two named hypotheses: a retained
count that clears `8.241973` past some cutoff, and a merged whole-constituent stage at every
repetition whose three side lengths clear the per-leg bit budgets `(225, 227, 232)`.

The fine reading cannot supply the second (`not_leafExponentsValid_fine`); a merged leaf can, and
`leafBase_pow_mul_le_mergedDimensionProduct` is the inequality it uses. -/
theorem omega_lt_236999_of_mergedStageFamily_at_floor
    {cutoff : ℕ} {count : ℕ → ℕ} {xSide ySide zSide : ℕ → ℕ}
    (hcount : RetainedCountValid retainedFloor cutoff count)
    (stage : ∀ r, 0 < r →
      WholeConstituentLaserVolumeStage.{u, u, 0} K
        (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (strideValue * r))
        (count r) (xSide r) (ySide r) (zSide r))
    (hx : ∀ r, 0 < r → leafBase ^ (xExponentBudget * r) ≤ xSide r)
    (hy : ∀ r, 0 < r → leafBase ^ (yExponentBudget * r) ≤ ySide r)
    (hz : ∀ r, 0 < r → leafBase ^ (zExponentBudget * r) ≤ zSide r) :
    omega K < TotalWeightVolumeEndpoint.acceptanceTarget :=
  omega_lt_236999_of_totalWeightTrackResidual_at_floor K
    (totalWeightTrackResidual_of_mergedStageFamily K hcount stage hx hy hz)

end Composition

end MatrixMultiplication.MergedLeafBudget
