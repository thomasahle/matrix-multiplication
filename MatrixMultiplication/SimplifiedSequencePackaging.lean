/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.EventualCopyGrowth
import AlgebraicComplexity.MatrixMultiplication.LaserVolumeRegularization
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolume
import MatrixMultiplication.Generated.TotalQuotientExponentStageFloors
import MatrixMultiplication.TotalWeightVolumeEndpoint

set_option autoImplicit false

/-!
# Sequence packaging for the total-weight certificate's volume-only endpoint

## STATUS — live, and on the sound track.

This module was re-based on 2026-08-28 (residual **R3** of the routing verdict) after experiment
**E1** refuted its previous shape.  Two things changed and both were forced:

* **The leaf base is `2`, not `5`, and the budget is per leg.**  E1 recomputed the certificate's
  three per-leg matrix-size rates exactly (`M = (6.1112127771…, 5.9264774981…, 5.9896173098…)` bits
  per `CW₅⁸` word) and found that a *sum* budget is not an achievable budget: in base five the
  realized triple at stride `38` is `(100, 96, 98)`, so `Σ⌊aᵈ⌋ = 294 < 295 = ⌊Σ aᵈ⌋` and the old
  `leafExponentBudget = 304 ≤ x + y + z` constrained the wrong object.  Floored in **bits** the
  same three rates give `(232, 225, 227)` — that is E1's *certificate volume-coordinate* order, and
  it is `(225, 227, 232)` per **CW leg**, which is the order every constant and statement below is
  in; see "The two leg conventions".  Total `684` either way, and mean rectangular volume
  `684 / 114 = 6` **exactly**.  See `better_bound/finding_v_e1/ANALYSIS.md`.
* **The retained constant is the committed stage-floor sum `8.241973`**
  (`Generated/TotalQuotientExponentStageFloors.coarseFourFamilyFloor_eq`), not the acceptance split
  `411/50 = 8.22`.  At volume `6` the acceptance inequality needs retained
  `≥ 22.45883937646084 − 6·2.36999 = 8.23889937646084`, which `8.22` misses by
  `−472484411521/25000000000000 = −1.889938e-2`.  The stage-floor sum clears it by
  `+76840588479/25000000000000 = +3.073624e-3` (`rankBudgetUpper_lt_endpoint_margin`).

## Provenance — the `eab2c7` quarantine is discharged for this file

The previous packaging composed through `SimplifiedRetainedCompressionSeam`, and therefore reached
the `eab2c7` retained-exponent payload whose numbers come from the ARCHIVED (uncorrected)
evaluator complement table (`scripts/artifact_provenance_quarantine.txt`).  That import is **gone**:
this module now reads only the sound total-weight (`e7987`) track — the committed stage floors and
`MatrixMultiplication/TotalWeightVolumeEndpoint.lean`.  Nothing here can inherit the refuted
provenance any more, so the file is a former, not a current, quarantine consumer.

## What this module is

The volume-only `2.36999` milestone consumes exactly one tensor-side object: a
`SubexponentialLaserVolumeSequence` for the eighth power of `CW₅` at stride `38`, in the base-two
coordinates `copyBase = 2 ^ (38 · E)` and `volumeBase = 2 ^ (3 · 38 · M)`.  Everything downstream
of that object is proved: the regularization bridge turns the sequence into CW90 value
certificates, Schönhage's inequality bounds their value by the source border rank `7⁸`, and the
endpoint arithmetic is `TotalWeightVolumeEndpoint`'s.

This module is the layer *above* the certificate's per-node counting cone and *below* that
endpoint.  It supplies the bookkeeping that the counting cone should not have to carry, and names
the remainder as three propositions:

* `RetainedCountValid` — the surviving retained-constituent count at each repetition, eventually
  above the stride's retained copy base;
* `LeafExponentsValid` — the three **per-leg bit** budgets of one stride block (the A5
  stride-realizability datum), with the budgets as arguments so that a re-tuned certificate
  re-instantiates the predicate without touching a single lemma;
* `RetainedExtractionValid` — the finite degeneration of one stride block onto `count r` equal
  rectangular leaves.

`TotalWeightTrackResidual` bundles the three, and `omega_lt_236999_of_totalWeightTrackResidual`
composes them into the milestone.  So the milestone's whole remaining obligation is
machine-readable as that theorem's hypothesis list — and the volume side is no longer part of it:
at leaf base `2` the packaging *realizes* volume `6`, so no external volume witness survives.

## What this module discharges

* **The subexponential loss (OB-8).**  The loss is *constructed*, not assumed: an eventual count
  bound is upgraded to a bound at every positive repetition by
  `Growth.finitePrefixPowerLoss`, whose positivity and subexponentiality are proved in
  `AlgebraicComplexity/Analysis/EventualCopyGrowth.lean`.  A counting theorem therefore never has
  to exhibit a loss sequence, only a cutoff.
* **The volume growth, now losslessly.**  `two_pow_le_leafBase_pow_budget` used to be the exact
  integer inequality `2 ^ 705 ≤ 5 ^ 304` — a ratio of `1.82`, and that slack *was* the whole
  base-five quantization loss.  At leaf base `2` it degenerates to `le_rfl`, the
  `set_option exponentiation.threshold 800` block disappears, and `volume_growth_of_leafExponents`
  turns a bare exponent inequality into the `volume_growth` field at every repetition.
* **The index alignment.**  Paper level `ℓ` is Lean word depth `ℓ - 1` (`wordDepth`) and Lean
  occurrence depth `ℓ - 2` (`occurrenceDepth`, the *child* depth); `occurrenceDepth_add_one`
  and `two_pow_wordDepth_succ` make the off-by-one a checked identity rather than prose.  The
  stride block's chunk alignment `8 · (38 · r) = 16 · (19 · r)` is `strideBlock_chunkAlignment`.
* **The leg convention.**  E1 publishes the per-leg budgets in the *certificate's* volume-coordinate
  order and the Lean statements are in CW *leg* order; the two differ by the rotation
  `c ↦ (c + 2) % 3`.  `legBudget_legOfCertificateCoordinate` makes both readings theorems and
  `sum_comp_legOfCertificateCoordinate` makes the invariance of the total a theorem, so the
  off-by-a-rotation is a checked identity rather than prose.  See "The two leg conventions".
* **The endpoint arithmetic at the committed constants.**
  `omega_lt_236999_of_sequence_at_stageFloor` is the bridge that
  `TotalWeightVolumeEndpoint.omega_lt_236999_of_subexponentialVolumeSequence_acceptanceFloors`
  cannot supply, because that theorem is pinned to `acceptanceRetainedFloor = 411/50` *and* to
  `volumeFloor = 6.0091024`, and neither is available at the realized volume `6`.  The bridge
  consumes only committed `TotalQuotientExponentStageFloors` theorems and the same generic
  `omega_lt_of_cwPower_volumeSequence_lowerBounds`; `TotalWeightVolumeEndpoint.lean` is not edited.
* **The B2 regularization application.**  `exists_tauValueCertificate_term_ge_of_residual` reads
  the packaged sequence as a family of finite CW90 value certificates of weight arbitrarily close
  to `2 ^ (E + 3τ·M)`, directly from
  `SubexponentialLaserVolumeSequence.exists_tauValueCertificate_term_ge`.

## What this module deliberately does not do

It contains no counting, no hashing, no compatibility cleanup, and no certificate table.  In
particular it does not import the `SimplifiedRecursive*` counting cone: the three propositions
above are stated in this module's own vocabulary, in the counting cone's naming style
(`UpperCamelCase` `Prop`-valued `def`s with bare `∀`/`∧` bodies against named constants), and are
meant to be discharged by theorems of that cone plus the compatibility-cleanup stage constructors
of `AlgebraicComplexity/MatrixMultiplication/WholeConstituentExtraction.lean`.

`RetainedExtractionValid.of_stageFamily` accepts the `WholeConstituentLaserVolumeStage` form in
any index universe, which is what those constructors produce.

## Honest gap

`WholeConstituentLaserVolumeSequenceData.volume_growth` carries **no** loss term — unlike
`copy_growth` it is demanded at `r = 1` too.  So `LeafExponentsValid` is a claim about a *finite*
stride block: the per-leg rates must be attained at `r = 1`, not merely in the limit.  E1
determined the triple `(225, 227, 232)` per leg from the certificate under the extraction model
this packaging fixes; whether a finite 38-word stage already attains those rates is the per-stage
semantic identification against `Generated/TotalQuotientExponentStageFloors.lean`, and it is not
done here.  Likewise `RetainedCountValid` at `8.241973` is exactly what that identification owes.
-/

namespace MatrixMultiplication.SimplifiedSequencePackaging

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.CurrentProofObligations

universe u z

/-! ## The stride block and its index alignment -/

/-- Stride of the total-weight track's depth-four leaf construction.  The only depth-four leaf
construction available on this track is stride `38`; see the A5 stride note.  E1 confirmed that
growing the stride is unnecessary once the leaf base is `2`. -/
def strideValue : ℕ := 38

theorem strideValue_pos : 0 < strideValue := by
  norm_num [strideValue]

theorem strideValue_cast : ((strideValue : ℕ) : ℝ) = 38 := by
  norm_num [strideValue]

/-- Power of `CW₅` used as the milestone's source tensor. -/
def sourcePower : ℕ := 8

/-- Letters of `CW₅` spelled by one stride block, `8 · 38`.  This is a letter count, not a budget:
E1 showed that only `274.59` of these letters are one-type letters carrying a factor `5`, the rest
being `⟨1,1,1⟩` zero-block letters whose leaf contribution is support *entropy*. -/
def strideBlockLetters : ℕ := 304

theorem strideBlockLetters_eq : sourcePower * strideValue = strideBlockLetters := by
  norm_num [sourcePower, strideValue, strideBlockLetters]

/-- Depth-four chunk alignment of the stride block: the `8 · (38 · r)` source letters of `r`
stride blocks are exactly `19 · r` chunks of `16` letters each.  This is the identity that fixes
the depth-four chunk count to `19 · r`. -/
theorem strideBlock_chunkAlignment (r : ℕ) :
    sourcePower * (strideValue * r) = 16 * (19 * r) := by
  unfold sourcePower strideValue
  ring

/-- Word depth of a paper level: level `ℓ` complete-split words are `SplitWord (ℓ - 1)`, and the
level's leg index is a `LevelConstituentIndex (ℓ - 1)`. -/
def wordDepth (level : ℕ) : ℕ := level - 1

/-- Occurrence depth of a paper level: the recursive occurrence data of a level-`ℓ` node is
indexed by its *children*, hence lives at depth `ℓ - 2`. -/
def occurrenceDepth (level : ℕ) : ℕ := level - 2

theorem wordDepth_levelTwo : wordDepth 2 = 1 := rfl

theorem wordDepth_levelThree : wordDepth 3 = 2 := rfl

theorem wordDepth_levelFour : wordDepth 4 = 3 := rfl

theorem occurrenceDepth_levelThree : occurrenceDepth 3 = 1 := rfl

theorem occurrenceDepth_levelFour : occurrenceDepth 4 = 2 := rfl

/-- The two depth conventions differ by exactly one: a level's occurrence data sits one depth
below its own words. -/
theorem occurrenceDepth_add_one {level : ℕ} (hlevel : 2 ≤ level) :
    occurrenceDepth level + 1 = wordDepth level := by
  unfold occurrenceDepth wordDepth
  omega

/-- The leg totals of a level-`ℓ` constituent index are `2 ^ ℓ`, written in the word depth the
Lean statements use. -/
theorem two_pow_wordDepth_succ {level : ℕ} (hlevel : 1 ≤ level) :
    2 ^ (wordDepth level + 1) = 2 ^ level := by
  unfold wordDepth
  congr 1
  omega

/-! ## The leaf dimensions and the per-leg bit budgets -/

/-- Base of the depth-four leaf dimensions.  **E1 (2026-08-28): `2`, not `5`.**  The endpoint never
asked for powers of anything — `WholeConstituentLaserVolumeSequenceData` takes
`xSize ySize zSize : ℕ → ℕ` arbitrary — and base `5` was the sole source of the quantization loss
that put the milestone out of reach at stride `38`. -/
def leafBase : ℕ := 2

/-- Bit budget of the **`X` leg** of one stride block, `⌊38 · M₁⌋ = ⌊225.206144930⌋ = 225`.  The
subscript is E1's *certificate volume coordinate*, not the leg: the `X` leg is coordinate `1`.  See
"The two leg conventions" below.

This is the leg that kills the base-five reading: `225.206144930 / log₂ 5 = 96.99101` lands
`0.008993` short of `97`. -/
def xExponentBudget : ℕ := 225

/-- Bit budget of the **`Y` leg** of one stride block, `⌊38 · M₂⌋ = ⌊227.605457774⌋ = 227`.  The
`Y` leg is E1's certificate volume coordinate `2`. -/
def yExponentBudget : ℕ := 227

/-- Bit budget of the **`Z` leg** of one stride block, `⌊38 · M₀⌋ = ⌊232.226085530⌋ = 232`.  The
`Z` leg is E1's certificate volume coordinate `0`. -/
def zExponentBudget : ℕ := 232

/-- Total bit budget of one stride block, `225 + 227 + 232 = 684`.  The total is the one thing the
leg convention cannot move (`sum_comp_legOfCertificateCoordinate`), which is why every downstream
constant — `volumeCeiling = 6`, the acceptance margin, the endpoint — is rotation-invariant.

It is deliberately **not** `strideBlockLetters = 304`: those are letters, these are bits. -/
def leafExponentBudget : ℕ := 684

theorem leafExponentBudget_eq :
    xExponentBudget + yExponentBudget + zExponentBudget = leafExponentBudget := by
  norm_num [xExponentBudget, yExponentBudget, zExponentBudget, leafExponentBudget]

/-! ## The two leg conventions

E1's volume decomposition indexes the certificate's per-leg rates by the **certificate's own volume
coordinate**, and publishes the floored triple in that order: `(232, 225, 227)` at coordinates
`(0, 1, 2)`.  Every Lean statement here — and every `matrixMultiplication` shape downstream —
indexes by the **CW matrix-shape leg** `(X, Y, Z)`.  *The two orders differ by a rotation*:
certificate volume coordinate `c` is CW matrix-shape leg `(c + 2) % 3`.

That was verified exhaustively, two independent ways, against the committed dimension table
`AlgebraicComplexity.Examples.cwBlockMatrixDimensions`: on the zero rows (`zero{2,3,4}_w0` is the
*zero* coordinate, and a zero-`w0` block carries its `q`-power at slot `(w0 + 2) % 3`, for all
three orientations over all legal two-letter words) and on the positive level-two edges (`heavy2`'s
`2μ` lands at slot `(heavy + 2) % 3`, for all three heavy coordinates and five values of `μ`).  The
record is `better_bound/r4_scoping/OBLIGATIONS.md` §9.1.

Because the rotation is uniform over *every* contributing term it is a convention difference and
not a correction: `684`, E1's requirement `683.852154193` and E2's `46.414034263`-bit shortfall are
the same numbers, and so are `volumeCeiling = 6` and `rankBudgetUpper_lt_endpoint_margin`, all of
which see the budgets only through their **sum**.  What moves is the pairing to legs — and it moves
for `LeafExponentsValid`, which is stated per leg and is *false* on the unrotated triple.

So the three constants above are in Lean/CW leg order, and the bridge back to E1's published order
is `legBudget_legOfCertificateCoordinate`: neither reading has to be taken on trust, and neither
triple should ever be hand-copied into a leg-indexed statement. -/

/-- CW matrix-shape leg of a certificate volume coordinate: `c ↦ (c + 2) % 3`.  Legs are numbered
`0 = X`, `1 = Y`, `2 = Z`, so the certificate's coordinates `(0, 1, 2)` are the legs `(Z, X, Y)`. -/
def legOfCertificateCoordinate : Fin 3 → Fin 3
  | 0 => 2
  | 1 => 0
  | 2 => 1

/-- The committed budgets indexed by CW matrix-shape leg: `(225, 227, 232)`. -/
def legBudget : Fin 3 → ℕ
  | 0 => xExponentBudget
  | 1 => yExponentBudget
  | 2 => zExponentBudget

/-- The same three numbers exactly as E1 publishes them, indexed by the certificate's volume
coordinate: `(232, 225, 227)` at coordinates `(0, 1, 2)`. -/
def certificateCoordinateBudget : Fin 3 → ℕ
  | 0 => 232
  | 1 => 225
  | 2 => 227

/-- **The leg convention, as a theorem.**  The budget this module gives to leg `(c + 2) % 3` is
exactly the budget E1 publishes at certificate volume coordinate `c`.  `(225, 227, 232)` and
`(232, 225, 227)` are therefore one datum read in two orders. -/
theorem legBudget_legOfCertificateCoordinate (c : Fin 3) :
    legBudget (legOfCertificateCoordinate c) = certificateCoordinateBudget c := by
  fin_cases c <;> rfl

/-- **The rotation is invisible to any total.**  Summing an arbitrary per-coordinate datum along
the legs and along the certificate's volume coordinates gives the same number, because the
convention change is a bijection of the three coordinates.  This is the general reason the
endpoint arithmetic is untouched by the rotation. -/
theorem sum_comp_legOfCertificateCoordinate (f : Fin 3 → ℕ) :
    ∑ c, f (legOfCertificateCoordinate c) = ∑ l, f l := by
  simp only [Fin.sum_univ_three, legOfCertificateCoordinate]
  ring

/-- The leg-indexed budgets total the committed leaf budget. -/
theorem sum_legBudget : ∑ l, legBudget l = leafExponentBudget := by
  simp only [Fin.sum_univ_three, legBudget]
  exact leafExponentBudget_eq

/-- **E1's published triple totals the same `684`** — obtained *through* the rotation rather than
by re-adding the numerals, so the two orders cannot silently drift apart. -/
theorem sum_certificateCoordinateBudget :
    ∑ c, certificateCoordinateBudget c = leafExponentBudget := by
  calc ∑ c, certificateCoordinateBudget c
      = ∑ c, legBudget (legOfCertificateCoordinate c) :=
        Finset.sum_congr rfl fun c _ ↦ (legBudget_legOfCertificateCoordinate c).symm
    _ = ∑ l, legBudget l := sum_comp_legOfCertificateCoordinate legBudget
    _ = leafExponentBudget := sum_legBudget

/-! ## The volume bookkeeping -/

/-- Mean rectangular-volume exponent the bit budget realizes: `684 / 114 = 6` **exactly**.  Under
the old base-five packaging this was a ceiling with `1.82` of unusable slack (`705/114`); here it
is attained, which is why the volume side of the milestone needs no external witness. -/
noncomputable def volumeCeiling : ℝ := 6

theorem volumeCeiling_pos : 0 < volumeCeiling := by
  norm_num [volumeCeiling]

/-- The budget and the ceiling are the same number in the endpoint's coordinates:
`684 = 3 · 38 · 6`. -/
theorem volumeCeiling_eq :
    3 * ((strideValue : ℕ) : ℝ) * volumeCeiling = ((leafExponentBudget : ℕ) : ℝ) := by
  norm_num [strideValue, volumeCeiling, leafExponentBudget]

set_option exponentiation.threshold 700 in
/-- **The leaf budget, degenerate.**  At leaf base `2` the exact integer inequality behind the
volume growth is `2 ^ 684 ≤ 2 ^ 684`.  The base-five predecessor was `2 ^ 705 ≤ 5 ^ 304`, whose
`1.82` ratio was pure quantization loss. -/
theorem two_pow_le_leafBase_pow_budget :
    (2 : ℕ) ^ leafExponentBudget ≤ leafBase ^ leafExponentBudget := le_rfl

/-- The rectangular-volume base of one stride sits below any leaf dimension product whose total
bit exponent dominates it.  This is the whole volume argument at leaf base `2`: an exponent
comparison, with no integer inequality left over. -/
theorem two_rpow_le_leafDimensionProduct {volume : ℝ} {xExponent yExponent zExponent : ℕ}
    (hvolume : 3 * ((strideValue : ℕ) : ℝ) * volume ≤
      ((xExponent + yExponent + zExponent : ℕ) : ℝ)) :
    (2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) * volume) ≤
      ((leafBase ^ (xExponent + yExponent + zExponent) : ℕ) : ℝ) := by
  have hcast : ((leafBase ^ (xExponent + yExponent + zExponent) : ℕ) : ℝ) =
      (2 : ℝ) ^ (((xExponent + yExponent + zExponent : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]
    push_cast [leafBase]
    ring
  rw [hcast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hvolume

/-- The same bound at the committed per-leg budgets, for every mean volume exponent at or below
`volumeCeiling = 6`. -/
theorem two_rpow_le_leafBase_pow_budget {volume : ℝ} (hvolume : volume ≤ volumeCeiling) :
    (2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) * volume) ≤
      ((leafBase ^ leafExponentBudget : ℕ) : ℝ) := by
  have hsum : 3 * ((strideValue : ℕ) : ℝ) * volume ≤
      ((xExponentBudget + yExponentBudget + zExponentBudget : ℕ) : ℝ) := by
    rw [strideValue_cast]
    have hvol : volume ≤ 6 := by simpa [volumeCeiling] using hvolume
    push_cast [xExponentBudget, yExponentBudget, zExponentBudget]
    linarith
  have hbound := two_rpow_le_leafDimensionProduct hsum
  rwa [leafExponentBudget_eq] at hbound

/-- **The `volume_growth` field, discharged.**  Side lengths `2 ^ (a · r)`, `2 ^ (b · r)`,
`2 ^ (c · r)` realize the base-two volume base of every mean exponent whose stride-block bit cost
`3 · 38 · volume` fits inside `a + b + c`, at every repetition. -/
theorem volume_growth_of_leafExponents {volume : ℝ} {xExponent yExponent zExponent : ℕ}
    (hvolume : 3 * ((strideValue : ℕ) : ℝ) * volume ≤
      ((xExponent + yExponent + zExponent : ℕ) : ℝ)) (r : ℕ) :
    ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) * volume)) ^ r ≤
      ((leafBase ^ (xExponent * r) * leafBase ^ (yExponent * r) *
        leafBase ^ (zExponent * r) : ℕ) : ℝ) := by
  have hsplit : (leafBase : ℕ) ^ (xExponent * r) * leafBase ^ (yExponent * r) *
      leafBase ^ (zExponent * r) = (leafBase ^ (xExponent + yExponent + zExponent)) ^ r := by
    rw [← pow_add, ← pow_add, ← pow_mul]
    congr 1
    ring
  rw [hsplit, Nat.cast_pow]
  exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
    (two_rpow_le_leafDimensionProduct hvolume) r

/-! ## The remaining interface

The three propositions below are what the certificate's counting cone and compatibility cleanup
still owe.  Their arguments follow the counting cone's positional convention: numerical data
first, then the finite counting data, then the repetition index. -/

/-- **The remaining counting interface.**  At every positive repetition the cleanup retains at
least one constituent, and from the cutoff on the retained count is at least the stride's retained
copy base `2 ^ (38 · E)` raised to that repetition.

Only an *eventual* bound is asked for: the finite prefix is absorbed by
`Growth.finitePrefixPowerLoss` in `subexponentialLaserVolumeSequence`, so a counting theorem never
has to produce a loss sequence. -/
def RetainedCountValid (retained : ℝ) (cutoff : ℕ) (count : ℕ → ℕ) : Prop :=
  (∀ r, 0 < r → 0 < count r) ∧
    ∀ r, cutoff ≤ r → 0 < r →
      ((2 : ℝ) ^ (((strideValue : ℕ) : ℝ) * retained)) ^ r ≤ (count r : ℝ)

/-- **The remaining leaf-dimension interface** (the A5 stride-realizability datum), stated **per
leg**.  One stride block's three rectangular side lengths are `2 ^ xExponent`, `2 ^ yExponent`,
`2 ^ zExponent`, and each leg separately meets its own bit budget.

The budgets are arguments, not constants: E1 fixed `(225, 227, 232)` per **leg** for the `e7987`
total-weight certificate (its own publication order is the certificate volume-coordinate triple
`(232, 225, 227)` — see "The two leg conventions"), and a re-tuned certificate re-instantiates this
predicate without touching a lemma.  A *sum* budget is deliberately avoided — E1 showed a sum bound
is not an achievable budget, which is exactly how the base-five predecessor (`304 ≤ x + y + z`)
came to constrain the wrong object.

**This predicate is the one place where the leg convention is load-bearing.**  It is stated per
leg, so it is *false* on the unrotated triple: `budget_le` and everything downstream of it see only
the rotation-invariant sum, but the three conjuncts themselves do not commute with the rotation.

No positivity conjunct is needed: at leaf base `2` every side length `2 ^ (e · r)` is positive
whatever the exponent. -/
def LeafExponentsValid (xBudget yBudget zBudget xExponent yExponent zExponent : ℕ) : Prop :=
  xBudget ≤ xExponent ∧ yBudget ≤ yExponent ∧ zBudget ≤ zExponent

/-- Per-leg budgets add, so a leg-wise budget always implies the sum bound the volume growth
consumes.  (The converse is false, and that asymmetry is FINDING V's error.) -/
theorem LeafExponentsValid.budget_le
    {xBudget yBudget zBudget xExponent yExponent zExponent : ℕ}
    (hleaf : LeafExponentsValid xBudget yBudget zBudget xExponent yExponent zExponent) :
    xBudget + yBudget + zBudget ≤ xExponent + yExponent + zExponent :=
  Nat.add_le_add (Nat.add_le_add hleaf.1 hleaf.2.1) hleaf.2.2

/-- At the committed budgets a valid leaf triple carries the full `volumeCeiling = 6`. -/
theorem LeafExponentsValid.volumeCeiling_le {xExponent yExponent zExponent : ℕ}
    (hleaf : LeafExponentsValid xExponentBudget yExponentBudget zExponentBudget
      xExponent yExponent zExponent) :
    3 * ((strideValue : ℕ) : ℝ) * volumeCeiling ≤
      ((xExponent + yExponent + zExponent : ℕ) : ℝ) := by
  have hnat : leafExponentBudget ≤ xExponent + yExponent + zExponent := by
    rw [← leafExponentBudget_eq]
    exact hleaf.budget_le
  have hcast : ((leafExponentBudget : ℕ) : ℝ) ≤ ((xExponent + yExponent + zExponent : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [volumeCeiling_eq]
  exact hcast

/-- **The remaining extraction interface.**  Every repetition of the stride block degenerates onto
`count r` equal rectangular matrix-multiplication tensors of side lengths `2 ^ (· · r)`.

This is verbatim the `extract` field of the target sequence, so no adapter stands between a
cleanup theorem and this module.  Use `RetainedExtractionValid.of_stageFamily` to supply it from
the `WholeConstituentLaserVolumeStage` form the compatibility-cleanup constructors produce. -/
def RetainedExtractionValid (K : Type u) [Field K] (count : ℕ → ℕ)
    (xExponent yExponent zExponent : ℕ) : Prop :=
  ∀ r, 0 < r →
    PolynomialDegenerates
      (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (strideValue * r))
      (matrixMultiplicationDirectSum (ι := Fin (count r)) K
        (fun _ ↦ leafBase ^ (xExponent * r)) (fun _ ↦ leafBase ^ (yExponent * r))
        (fun _ ↦ leafBase ^ (zExponent * r)))

/-- A family of whole-constituent finite stages, in any index universe, supplies the extraction
interface.  The reindexing to `Fin (count r)` is
`WholeConstituentLaserVolumeStage.polynomialDegenerates`. -/
theorem RetainedExtractionValid.of_stageFamily {K : Type u} [Field K] {count : ℕ → ℕ}
    {xExponent yExponent zExponent : ℕ}
    (stage : ∀ r, 0 < r →
      WholeConstituentLaserVolumeStage.{u, u, z} K
        (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (strideValue * r))
        (count r) (leafBase ^ (xExponent * r)) (leafBase ^ (yExponent * r))
        (leafBase ^ (zExponent * r))) :
    RetainedExtractionValid K count xExponent yExponent zExponent :=
  fun r hr ↦ (stage r hr).polynomialDegenerates

/-- **The full remaining obligation of the volume-only milestone's tensor side**, as one
proposition: a cutoff, a retained count, three leaf side exponents, and the three interfaces
above, at the committed per-leg bit budgets `(225, 227, 232)` — that is `(X, Y, Z)` in **CW leg
order**, E1's certificate volume-coordinate triple `(232, 225, 227)` rotated by
`legOfCertificateCoordinate`.

`xExponent`, `yExponent` and `zExponent` are the same three legs, in the same order, as the
`xSize`/`ySize`/`zSize` of `RetainedExtractionValid`'s `matrixMultiplicationDirectSum`; a witness
must not permute them between the two conjuncts.

The volume no longer appears: the leaf budgets *realize* mean volume `6`. -/
def TotalWeightTrackResidual (K : Type u) [Field K] (retained : ℝ) : Prop :=
  ∃ (cutoff : ℕ) (count : ℕ → ℕ) (xExponent yExponent zExponent : ℕ),
    RetainedCountValid retained cutoff count ∧
      LeafExponentsValid xExponentBudget yExponentBudget zExponentBudget
        xExponent yExponent zExponent ∧
        RetainedExtractionValid K count xExponent yExponent zExponent

/-- The retained floor this module composes at: the committed four-family stage-floor sum
`8.241973` of `Generated/TotalQuotientExponentStageFloors.lean`.  It is *not*
`TotalWeightVolumeEndpoint.acceptanceRetainedFloor = 411/50`, which is unusable at volume `6`. -/
noncomputable def retainedFloor : ℝ :=
  MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.coarseFourFamilyFloor

theorem retainedFloor_eq : retainedFloor = (8_241_973 / 1_000_000 : ℝ) :=
  MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.coarseFourFamilyFloor_eq

/-! ## The packaging theorem -/

/-- **The packaging theorem.**  The counting and extraction interfaces, together with a leaf
exponent sum that pays for the mean rectangular-volume exponent, are a
`SubexponentialLaserVolumeSequence` in exactly the base-two coordinates the milestone endpoint
consumes.

Nothing analytic is assumed: the loss is `Growth.finitePrefixPowerLoss`, whose positivity and
subexponentiality are proved, and the volume growth is `volume_growth_of_leafExponents`. -/
noncomputable def subexponentialLaserVolumeSequence (K : Type u) [Field K]
    {retained volume : ℝ} {cutoff : ℕ} {count : ℕ → ℕ}
    {xExponent yExponent zExponent : ℕ}
    (hcount : RetainedCountValid retained cutoff count)
    (hextract : RetainedExtractionValid K count xExponent yExponent zExponent)
    (hvolume : 3 * ((strideValue : ℕ) : ℝ) * volume ≤
      ((xExponent + yExponent + zExponent : ℕ) : ℝ)) :
    SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) strideValue
      ((2 : ℝ) ^ (((strideValue : ℕ) : ℝ) * retained))
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) * volume)) where
  stride_pos := strideValue_pos
  copyBase_pos := Real.rpow_pos_of_pos (by norm_num) _
  volumeBase_pos := Real.rpow_pos_of_pos (by norm_num) _
  loss := Growth.finitePrefixPowerLoss
    ((2 : ℝ) ^ (((strideValue : ℕ) : ℝ) * retained)) cutoff
  count := count
  xSize := fun r ↦ leafBase ^ (xExponent * r)
  ySize := fun r ↦ leafBase ^ (yExponent * r)
  zSize := fun r ↦ leafBase ^ (zExponent * r)
  loss_subexponential :=
    Growth.finitePrefixPowerLoss_subexponential
      (Real.rpow_nonneg (by norm_num) _) cutoff
  loss_pos := fun r _ ↦
    Growth.finitePrefixPowerLoss_pos (Real.rpow_pos_of_pos (by norm_num) _) cutoff r
  count_pos := hcount.1
  xSize_pos := fun _ _ ↦ pow_pos (by norm_num [leafBase]) _
  ySize_pos := fun _ _ ↦ pow_pos (by norm_num [leafBase]) _
  zSize_pos := fun _ _ ↦ pow_pos (by norm_num [leafBase]) _
  extract := hextract
  copy_growth :=
    Growth.pow_le_finitePrefixPowerLoss_mul_count
      (Real.rpow_pos_of_pos (by norm_num) _) hcount.1 hcount.2
  volume_growth := fun r _ ↦ volume_growth_of_leafExponents hvolume r

/-- The packaged sequence, from the bundled residual, at the realized mean volume `6`. -/
theorem nonempty_subexponentialLaserVolumeSequence_of_residual (K : Type u) [Field K]
    {retained : ℝ} (hresidual : TotalWeightTrackResidual K retained) :
    Nonempty (SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) strideValue
      ((2 : ℝ) ^ (((strideValue : ℕ) : ℝ) * retained))
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) * volumeCeiling))) := by
  obtain ⟨cutoff, count, xExponent, yExponent, zExponent, hcount, hleaf, hextract⟩ := hresidual
  exact ⟨subexponentialLaserVolumeSequence K hcount hextract hleaf.volumeCeiling_le⟩

/-! ## The endpoint bridge and the milestone -/

/-- **The exact acceptance margin at the realized volume.**  `8.241973 + 2.36999 · 6` exceeds the
directed source-rank enclosure `22.45883937646084` by

  `76840588479 / 25000000000000 = 3.073624e-3 > 0`.

Two neighbouring constants, for the record (E1, `better_bound/finding_v_e1/ANALYSIS.md` §4): the
tight aggregate floor `8.2419803` clears by `77023088479/25000000000000 = 3.080924e-3`, while
`TotalWeightVolumeEndpoint.acceptanceRetainedFloor = 411/50 = 8.22` **fails** by
`−472484411521/25000000000000 = −1.889938e-2`.  Volume `6` demands retained
`≥ 205972484411521/25000000000000 = 8.23889937646084`. -/
theorem rankBudgetUpper_lt_endpoint_margin :
    MatrixMultiplication.LogBounds.rankBudgetUpper <
      retainedFloor + TotalWeightVolumeEndpoint.acceptanceTarget * volumeCeiling := by
  rw [retainedFloor_eq]
  norm_num [MatrixMultiplication.LogBounds.rankBudgetUpper,
    TotalWeightVolumeEndpoint.acceptanceTarget, volumeCeiling]

/-- **The endpoint bridge at the committed stage-floor constant.**  A total-weight extraction
sequence whose retained exponent clears `8.241973` and whose mean rectangular-volume exponent
clears `6` proves the requested milestone.

This is the composition `TotalWeightVolumeEndpoint` does not provide:
`omega_lt_236999_of_subexponentialVolumeSequence_acceptanceFloors` is pinned to
`acceptanceRetainedFloor = 411/50` *and* to `volumeFloor = 6.0091024`, and at the realized volume
`6` neither hypothesis is available.  Only committed theorems are consumed here — the generic
`omega_lt_of_cwPower_volumeSequence_lowerBounds`, `sourceRankBudget_lt_upper`, and
`TotalQuotientExponentStageFloors.coarseFourFamilyFloor_eq`; `TotalWeightVolumeEndpoint.lean` is
not edited. -/
theorem omega_lt_236999_of_sequence_at_stageFloor (K : Type u) [Field K]
    {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hretained : retainedFloor ≤ retained)
    (hvolume : volumeCeiling ≤ volume) :
    omega K < TotalWeightVolumeEndpoint.acceptanceTarget := by
  refine omega_lt_of_cwPower_volumeSequence_lowerBounds K 5 8
    (retainedLower := retainedFloor) (volumeLower := volumeCeiling)
    volumeCeiling_pos hretained hvolume
    TotalWeightVolumeEndpoint.acceptanceTarget_nonneg hextractions ?_
  calc
    (8 : ℝ) * Real.log ((5 : ℕ) + 2) / Real.log 2 = sourceRankBudget := by
      norm_num [sourceRankBudget]
      ring
    _ < MatrixMultiplication.LogBounds.rankBudgetUpper := sourceRankBudget_lt_upper
    _ < retainedFloor + TotalWeightVolumeEndpoint.acceptanceTarget * volumeCeiling :=
      rankBudgetUpper_lt_endpoint_margin

/-- **The volume-only `2.36999` milestone from the total-weight residual.**

Two named inputs, and the volume is not one of them:

1. `hresidual` — the certificate's counting cone and compatibility cleanup, bundled as
   `TotalWeightTrackResidual`;
2. `hretained` — the retained exponent clears the committed stage-floor sum `8.241973`.

No other hypothesis appears: Schönhage's inequality, the regularization bridge, the border-rank
certificate of `CW₅⁸` and the rational margin arithmetic are all proved upstream, and the mean
rectangular-volume exponent `6` is *realized* by the leaf budgets rather than assumed. -/
theorem omega_lt_236999_of_totalWeightTrackResidual (K : Type u) [Field K]
    {retained : ℝ}
    (hresidual : TotalWeightTrackResidual K retained)
    (hretained : retainedFloor ≤ retained) :
    omega K < TotalWeightVolumeEndpoint.acceptanceTarget := by
  obtain ⟨sequence⟩ := nonempty_subexponentialLaserVolumeSequence_of_residual K hresidual
  exact omega_lt_236999_of_sequence_at_stageFloor K sequence hretained le_rfl

/-- The milestone with the retained exponent pinned at the committed stage-floor sum, so that the
counting residual is the **only** remaining hypothesis.  This is the codex-facing target. -/
theorem omega_lt_236999_of_totalWeightTrackResidual_at_floor (K : Type u) [Field K]
    (hresidual : TotalWeightTrackResidual K retainedFloor) :
    omega K < TotalWeightVolumeEndpoint.acceptanceTarget :=
  omega_lt_236999_of_totalWeightTrackResidual K hresidual le_rfl

/-! ## The value-certificate reading (B2) -/

/-- **The packaged sequence as a family of CW90 value certificates.**  For every `τ ≥ 0` and every
`ε > 0` the residual supplies a finite value certificate of `CW₅⁸` whose weight at `τ` is within
`ε` of `2 ^ (E + 3τ·6)`.

This is the B2 regularization theorem applied to the total-weight track: it is the `happrox`
hypothesis shape of `omega_lt_three_mul_of_approximate_certificates`, and it makes the certificate
value available without going through the rate interface. -/
theorem exists_tauValueCertificate_term_ge_of_residual (K : Type u) [Field K]
    {retained τ ε : ℝ}
    (hresidual : TotalWeightTrackResidual K retained)
    (hτ : 0 ≤ τ) (hε : 0 < ε) :
    ∃ certificate : TauValueCertificate K (Tensor.power (coppersmithWinograd K 5) 8),
      (2 : ℝ) ^ (retained + 3 * τ * volumeCeiling) - ε ≤ certificate.term τ := by
  obtain ⟨sequence⟩ := nonempty_subexponentialLaserVolumeSequence_of_residual K hresidual
  obtain ⟨certificate, hterm⟩ := sequence.exists_tauValueCertificate_term_ge K hτ hε
  refine ⟨certificate, ?_⟩
  rwa [laserVolumeValue_bits strideValue_pos retained volumeCeiling τ] at hterm

end MatrixMultiplication.SimplifiedSequencePackaging
