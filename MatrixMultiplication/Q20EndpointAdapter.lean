/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradEventualVolumeLossEndpoint
import AlgebraicComplexity.Examples.CoppersmithWinogradCyclicVolumeEndpoint
import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeEndpointValue
import AlgebraicComplexity.MatrixMultiplication.CyclicLaserVolume
import MatrixMultiplication.LogBounds

set_option autoImplicit false

/-!
# The q20 endpoint adapter: `omega < 2.36999` from one tail-native stage datum

**Status: conditional.  Nothing in this file proves `omega K < 2.36999`.**  Every endpoint
below carries the finite-stage datum as an explicit hypothesis.  That datum is an open
obligation (stages S1 to S9 of the Total-Weight proof breakdown); it is not constructed anywhere
in this repository, and the q20 legal-hybrid candidate is a conditional numerical program, not a
certificate.

What this module does is fix the *top* of the proof so the stage lanes have a named target.
Everything above the finite datum -- the value normalization at `tau = target/3`, the
regularization, Schoenhage soundness, the source border-rank budget of `CW_5^(x8)`, and the
strict rational margin -- is discharged here by exact arithmetic, once.  This is stage S10
("value normalization and asymptotic tail") plus stage S12 ("final scalar endpoint").

## The interface is tail-native, following the paper

The primary endpoint asks a construction for exactly what `prop:tail-native-cw-endpoint`
asks for and no more: exact whole-constituent stages **from some cutoff on** (not at every
positive repetition), with **two separate subexponential losses**, one in the copy count and
one in the integral rectangular volume.  Its Lean carrier is the committed
`AlgebraicComplexity.EventualWholeConstituentLaserVolumeLossData`
(`AlgebraicComplexity/MatrixMultiplication/EventualWholeConstituentLaserVolumeLoss.lean:39`),
consumed through
`AlgebraicComplexity.Examples.omega_lt_of_cwPower_eventualWholeConstituentVolumeLoss`
(`AlgebraicComplexity/Examples/CoppersmithWinogradEventualVolumeLossEndpoint.lean:46`).

The paper's proof backs off to a strictly smaller mean-volume exponent `0 < m < M` in order
to absorb the volume loss.  Here that backoff is *derived from the q20 margin itself*, with
no new numerics: with `E, M, C, T, delta` the five frozen q20 rationals below and

```text
m := M - delta / (2 * T),
```

one has `0 < m < M` and, exactly, `E + T * m - C = delta / 2 > 0`
(`q20_backedOff_margin_eq`).  So keeping the paper's volume-loss allowance costs the target
nothing.  The exact-sequence form is retained as a clearly-labelled convenience corollary
only.

`Q20StageBases` is the **numerical** half of the datum and nothing more.  Satisfying it does
not establish any semantic sequence; the semantic half is the
`EventualWholeConstituentLaserVolumeLossData` hypothesis of the endpoint.

## Which paper statements this transcribes

From `better_bound/paper.tex`:

* `prop:tail-native-cw-endpoint` (lines 2199-2231), *CW endpoint from a stage family*: given,
  for every **sufficiently large** `r`, a degeneration of the `sr`-th power of `(CW_q)^(xp)`
  into `c_r` copies of `<x_r,y_r,z_r>` with `2^(srE) <= L_c(r) c_r` and
  `2^(3srM) <= L_v(r) x_r y_r z_r` for positive subexponential `L_c, L_v`, one gets
  `E + omega(K) m <= p log2(q+2)` for every `0 < m < M`, and hence `omega(K) < Omega`
  whenever `E_0 <= E` and `p log2(q+2) < E_0 + Omega m`.  Lines 2241-2244 add that the stride
  is deliberately left open: the proposition holds for every positive `s`.
* `cor:repeated-volume` (lines 2255-2266), *Final assembly with repeated orientations*: a
  feasible point satisfying `E_total + Omega M_vol >= 2^(l*-1) log2(q+2)` proves
  `omega <= Omega`, the right-hand side being `8 log2 7` for the level-4, `q = 5` program.
  The strict form at the backed-off exponent is `sourceBudget_lt_q20_backedOff_endpoint`.
* `sec:verification`, *The final inequality* (lines 2501-2529): the shape of the closing
  arithmetic -- a directed source-rank enclosure, a retained floor, a mean-volume floor, and
  one exact rational margin.  **The constants printed there belong to the rejected 90df
  candidate and are deliberately not reused**; this module carries the q20 constants instead.
  The directed source-rank enclosure `8 log2 7 < 2245883937646084/10^14` of line 2503 is the
  one item shared, and it is already committed as
  `MatrixMultiplication.LogBounds.rankBudgetUpper`.

Bib keys: `[coppersmith1990matrix]` (the `CW_q` construction and the tau-value calculus),
`[schonhage1981partial]` (the asymptotic sum inequality behind the endpoint),
`[duan2023faster]` and `[alman2025more]` (the laser / total-weight lineage the manuscript
extends).  The manuscript itself is `better_bound/paper.tex`.

## The q20 numbers of record

All are the *exact* rationals of the frozen directed record
`better_bound/legal_hybrid/directed_result.json` (SHA-256
`9ad86e7a945337f88cdbe6f4dfc443e9f6388a3039a8fa5449180c79ad12d1be`), scored by
`better_bound/legal_hybrid/SLACK.md:22-31`:

* `q20RetainedFloor` = `909388958396016619774220503076397233/110680464442257309696000000000000000`,
  from `directed_result.json:871`, field `retained_exponent_interval.lower_exact`;
* `q20VolumeFloor` = `43304568303933479968686691703821/7205759403792793600000000000000`,
  from `directed_result.json:864`, field `rectangular_volume_interval.lower_exact`;
* `q20SourceCostUpper` = `1403677461403797/62500000000000`,
  from `directed_result.json:789`, field `eight_log2_seven_interval.upper_exact`;
* `q20Target` = `236999/100000`, from `directed_result.json:927`, field `target_exact`;
* `q20TargetMargin` =
  `32746257038135160749062752522975809/69175290276410818560000000000000000000`,
  from `directed_result.json:929`, field `target_margin_directed_lower_exact`.

`q20BackedOffVolume` is the only derived constant, and it is derived from those five alone.
`q20TargetMargin_eq` re-derives the record's margin identity
`E_lower + Omega M_lower - C_upper = margin` in Lean, so the module cannot silently drift
from the scored image; `q20_directed_ratio_lt_target` re-derives the record's headline ratio
bound `(C_upper - E_lower)/M_lower <= 2.369911230748277369 < 2.36999`.

## What is deliberately absent

* No `TotalWeightLeanEndpoint` and no `TotalWeightEventualVolumeLossEndpoint` constant.
  Neither `8.22`, nor `8.241973`
  (`MatrixMultiplication/TotalWeightVolumeLossEndpoint.lean:52`), nor `8.241241067995057`
  (paper line 2487) appears here; the retained floor used is q20's own
  `8.216345702727426890`.
* No `decide`, no `native_decide`, no heartbeat raise, no generated data import.  Every
  numerical step is `norm_num` on exact rationals, and the only transcendental input is the
  committed atanh enclosure
  `MatrixMultiplication.LogBounds.eight_logTwo_seven_lt_rankBudgetUpper`.
* **No cyclic construction, and no normalization obligation.**  The exact-cyclic corollary
  needs no source conversion.  The committed
  `SubexponentialCyclicLaserVolumeSequence.hasCyclicLaserExtractionRate`
  (`AlgebraicComplexity/MatrixMultiplication/CyclicLaserVolume.lean:107`) normalizes by the
  `3 * stride` source copies, and `HasCyclicLaserExtractionRate.le_log_borderRank`
  (`AlgebraicComplexity/MatrixMultiplication/CyclicLaserRateSoundness.lean:226`) bounds that
  rate by the border rank of the **source**, because the cyclic power product's border rank is
  at most `R(T)^(3k)` and the two factors `3k` cancel.  The three source copies are therefore
  already charged: this is the three-source argument of `lem:volume`
  (`better_bound/paper.tex:2160-2181`), packaged as
  `Examples.retained_add_omega_mul_volume_le_cwPowerBudget_of_cyclicSequence`
  (`AlgebraicComplexity/Examples/CoppersmithWinogradCyclicVolumeEndpoint.lean`).  What is open
  in the cyclic route is `hcyclic` itself, the Mode-B construction of row TW-27, and nothing
  else.  The route was found by Codex CW and reviewed by Codex 2.36x and Codex C2; it replaces
  an earlier draft of this module that carried a source-normalization hypothesis it did not
  need.
-/

namespace MatrixMultiplication.Q20EndpointAdapter

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor

universe u

/-! ## The exact q20 constants -/

/-- Directed retained-exponent floor `E_lower` of the frozen q20 record
(`better_bound/legal_hybrid/directed_result.json:871`), decimal `8.216345702727426890`. -/
noncomputable def q20RetainedFloor : ℝ :=
  909388958396016619774220503076397233 / 110680464442257309696000000000000000

/-- Directed *nominal* mean rectangular side-exponent floor `M_vol,lower`
(`better_bound/legal_hybrid/directed_result.json:864`), decimal `6.009716100309964166`. -/
noncomputable def q20VolumeFloor : ℝ :=
  43304568303933479968686691703821 / 7205759403792793600000000000000

/-- Directed upper enclosure of the source cost `8 log2 7` used by the q20 record
(`better_bound/legal_hybrid/directed_result.json:789`), decimal `22.458839382460752`. -/
noncomputable def q20SourceCostUpper : ℝ := 1403677461403797 / 62500000000000

/-- The q20 acceptance target `2.36999`
(`better_bound/legal_hybrid/directed_result.json:927`). -/
noncomputable def q20Target : ℝ := 236999 / 100000

/-- The record's directed lower margin at the target
(`better_bound/legal_hybrid/directed_result.json:929`), decimal `0.000473380840286865`. -/
noncomputable def q20TargetMargin : ℝ :=
  32746257038135160749062752522975809 / 69175290276410818560000000000000000000

/-- **The strictly backed-off mean-volume exponent** `m = M - delta/(2T)`, which is what
absorbs the paper's subexponential volume loss.  It is derived from the five frozen constants
alone: no reoptimization, no empirical estimate and no old candidate floor enters it.  Its
decimal is `6.009616230512985...`. -/
noncomputable def q20BackedOffVolume : ℝ :=
  q20VolumeFloor - q20TargetMargin / (2 * q20Target)

/-- The target constant is the decimal `2.36999` the programme is named after. -/
theorem q20Target_eq_decimal : q20Target = 2.36999 := by
  norm_num [q20Target]

/-- The target is nonnegative, as the endpoint's `0 ≤ target` binder requires. -/
theorem q20Target_nonneg : 0 ≤ q20Target := by
  norm_num [q20Target]

/-- The directed retained floor is positive. -/
theorem q20RetainedFloor_pos : 0 < q20RetainedFloor := by
  norm_num [q20RetainedFloor]

/-- The directed nominal mean-volume floor is positive, which is what makes the endpoint's
division by the volume exponent informative. -/
theorem q20VolumeFloor_pos : 0 < q20VolumeFloor := by
  norm_num [q20VolumeFloor]

/-- The record's directed margin at the target is strictly positive: this is the whole content
of `strict_numerical_feasibility` for `236999/100000` in the frozen score. -/
theorem q20TargetMargin_pos : 0 < q20TargetMargin := by
  norm_num [q20TargetMargin]

/-- **The record's margin identity, re-derived exactly.**  This is `score_slack.py`'s
`frozen_margin = elo + target * mlo - chi` (`better_bound/legal_hybrid/score_slack.py:39`)
checked in Lean over the rationals, so the constants above cannot drift from the scored
image. -/
theorem q20TargetMargin_eq :
    q20RetainedFloor + q20Target * q20VolumeFloor - q20SourceCostUpper = q20TargetMargin := by
  norm_num [q20RetainedFloor, q20Target, q20VolumeFloor, q20SourceCostUpper, q20TargetMargin]

/-- The record's headline directed ratio `(C_upper - E_lower)/M_lower` lies below the target.
Its decimal display is `2.369911230748277369` (`better_bound/legal_hybrid/SLACK.md:29`). -/
theorem q20_directed_ratio_lt_target :
    (q20SourceCostUpper - q20RetainedFloor) / q20VolumeFloor < q20Target := by
  rw [div_lt_iff₀ q20VolumeFloor_pos]
  norm_num [q20SourceCostUpper, q20RetainedFloor, q20VolumeFloor, q20Target]

/-! ## The backed-off exponent, and why it costs nothing

These three lemmas are the exact arithmetic of C2's endpoint fidelity review (board entry
2026-09-05 20:17:57 UTC), re-proved here rather than quoted. -/

/-- `0 < m`. -/
theorem q20BackedOffVolume_pos : 0 < q20BackedOffVolume := by
  norm_num [q20BackedOffVolume, q20VolumeFloor, q20TargetMargin, q20Target]

/-- `m < M`: the backoff is strict, which is what the volume-loss absorption needs. -/
theorem q20BackedOffVolume_lt_q20VolumeFloor : q20BackedOffVolume < q20VolumeFloor := by
  norm_num [q20BackedOffVolume, q20VolumeFloor, q20TargetMargin, q20Target]

/-- **`E + T * m - C = delta / 2`, exactly.**  Half the record's directed margin survives the
backoff, so keeping the paper's subexponential volume-loss allowance does not cost the
`2.36999` target anything. -/
theorem q20_backedOff_margin_eq :
    q20RetainedFloor + q20Target * q20BackedOffVolume - q20SourceCostUpper =
      q20TargetMargin / 2 := by
  norm_num [q20BackedOffVolume, q20RetainedFloor, q20Target, q20VolumeFloor,
    q20SourceCostUpper, q20TargetMargin]

/-- The repository's certified atanh enclosure for `8 log2 7` is inside the q20 record's
directed upper endpoint, so every endpoint below is proved against the record's own source
cost. -/
theorem rankBudgetUpper_lt_q20SourceCostUpper :
    MatrixMultiplication.LogBounds.rankBudgetUpper < q20SourceCostUpper := by
  norm_num [MatrixMultiplication.LogBounds.rankBudgetUpper, q20SourceCostUpper]

/-! ## The q20 numerical stage record

`Q20StageBases` records **only numbers**: a repetition unit and the two base-two exponents
whose bases a stage family is stated at.  It says nothing about tensors, and satisfying it
establishes no semantic object.  The semantic half is the
`EventualWholeConstituentLaserVolumeLossData` hypothesis of the endpoints below. -/

/-- **The q20 numerical stage record.**  A stride together with retained and *nominal*
mean-volume exponents that clear the two directed q20 floors.  S8 and S9 lanes should target
this record by name rather than restating decimals; it is the numerical half of their
obligation, not the whole of it. -/
structure Q20StageBases where
  /-- Repetition unit of the stage family, in unsymmetrized `CW_5^(x8)` units. -/
  stride : ℕ
  /-- Base-two retained exponent per stride: the copy base is `2^(stride * retained)`. -/
  retained : ℝ
  /-- Base-two *nominal* mean rectangular side exponent per stride: the volume base is
  `2^(3 * stride * volume)`.  The endpoint consumes it only after the strict backoff to
  `q20BackedOffVolume`, which is where the volume loss is absorbed. -/
  volume : ℝ
  /-- A stage family repeats a positive number of source units. -/
  stride_pos : 0 < stride
  /-- The stage clears the q20 directed retained floor. -/
  retained_floor : q20RetainedFloor ≤ retained
  /-- The stage clears the q20 directed nominal mean-volume floor. -/
  volume_floor : q20VolumeFloor ≤ volume

/-- The copy base `2^(stride * retained)` the stage family is stated at. -/
noncomputable def Q20StageBases.copyBase (b : Q20StageBases) : ℝ :=
  (2 : ℝ) ^ ((b.stride : ℝ) * b.retained)

/-- The nominal volume base `2^(3 * stride * volume)` the stage family is stated at. -/
noncomputable def Q20StageBases.volumeBase (b : Q20StageBases) : ℝ :=
  (2 : ℝ) ^ (3 * (b.stride : ℝ) * b.volume)

/-- **The q20 point of record itself**, at any positive stride.  The stride is left free on
purpose: the frozen record fixes no repetition unit (the historical stride 38 is not a q20
certificate), the bases already absorb it, and the paper's own proposition holds for every
positive `s` (`better_bound/paper.tex:2241-2244`). -/
noncomputable def q20StageBases (stride : ℕ) (hstride : 0 < stride) : Q20StageBases where
  stride := stride
  retained := q20RetainedFloor
  volume := q20VolumeFloor
  stride_pos := hstride
  retained_floor := le_rfl
  volume_floor := le_rfl

/-- The binders of `Q20StageBases` are satisfiable at the intended q20 parameters: the record
built by `q20StageBases` has exactly the stride it is given and the two floors as its
exponents, so the hypotheses are satisfiable. -/
theorem q20StageBases_spec (stride : ℕ) (hstride : 0 < stride) :
    (q20StageBases stride hstride).stride = stride ∧
      (q20StageBases stride hstride).retained = q20RetainedFloor ∧
        (q20StageBases stride hstride).volume = q20VolumeFloor :=
  ⟨rfl, rfl, rfl⟩

/-- The copy base at the q20 point is the base-two retained floor per stride. -/
theorem q20StageBases_copyBase (stride : ℕ) (hstride : 0 < stride) :
    (q20StageBases stride hstride).copyBase =
      (2 : ℝ) ^ ((stride : ℝ) * q20RetainedFloor) := rfl

/-- The nominal volume base at the q20 point is the base-two mean-volume floor per stride. -/
theorem q20StageBases_volumeBase (stride : ℕ) (hstride : 0 < stride) :
    (q20StageBases stride hstride).volumeBase =
      (2 : ℝ) ^ (3 * (stride : ℝ) * q20VolumeFloor) := rfl

/-! ## The scalar margin at the backed-off exponent -/

/-- **The strict scalar margin of `cor:repeated-volume` at the q20 constants and the
backed-off mean-volume exponent.**

The exact source cost `8 log2 7` of `CW_5^(x8)` lies strictly below `E + 2.36999 * m`.  The
chain is: the committed atanh enclosure of `8 log2 7`, then the record's own directed
source-cost endpoint, then the surviving half-margin `delta/2` of
`q20_backedOff_margin_eq`. -/
theorem sourceBudget_lt_q20_backedOff_endpoint :
    (8 : ℝ) * Real.log ((5 : ℕ) + 2) / Real.log 2 <
      q20RetainedFloor + q20Target * q20BackedOffVolume := by
  have hmargin :
      q20SourceCostUpper < q20RetainedFloor + q20Target * q20BackedOffVolume := by
    have heq := q20_backedOff_margin_eq
    have hpos := q20TargetMargin_pos
    linarith
  calc
    (8 : ℝ) * Real.log ((5 : ℕ) + 2) / Real.log 2 =
        8 * (Real.log 7 / Real.log 2) := by norm_num; ring
    _ < MatrixMultiplication.LogBounds.rankBudgetUpper :=
      MatrixMultiplication.LogBounds.eight_logTwo_seven_lt_rankBudgetUpper
    _ < q20SourceCostUpper := rankBudgetUpper_lt_q20SourceCostUpper
    _ < q20RetainedFloor + q20Target * q20BackedOffVolume := hmargin

/-! ## The primary, tail-native endpoint -/

/-- **The q20 endpoint, conditional on the S8 to S10 tail-native stage datum.**

If exact whole-constituent stages of `CW_5^(x8)` exist from some cutoff on, with separate
subexponential losses in copy count and integral rectangular volume, at the q20 copy and
nominal volume bases, then `omega K < 2.36999` over every field.

This is `prop:tail-native-cw-endpoint` (`better_bound/paper.tex:2199-2231`) at `q = 5`,
`p = 8`, with the paper's own backoff `0 < m < M` instantiated at `m = q20BackedOffVolume`,
composed with the strict margin of `cor:repeated-volume`
(`better_bound/paper.tex:2255-2266`).

Its single data hypothesis is precisely the object rows TW-17 to TW-20 must build; **it is
not proved anywhere in this repository**, so this theorem is a conditional endpoint and must
never be reported as `omega K < 2.36999` on its own.  Satisfying `Q20StageBases` alone
establishes nothing: the record is only the numerical half. -/
theorem omega_lt_236999_of_q20EventualStages
    (K : Type u) [Field K] (b : Q20StageBases)
    (data : EventualWholeConstituentLaserVolumeLossData K
      (Tensor.power (coppersmithWinograd K 5) 8) b.stride b.copyBase b.volumeBase) :
    omega K < q20Target :=
  omega_lt_of_cwPower_eventualWholeConstituentVolumeLoss K 5 8 data
    q20BackedOffVolume_pos
    (lt_of_lt_of_le q20BackedOffVolume_lt_q20VolumeFloor b.volume_floor)
    b.retained_floor sourceBudget_lt_q20_backedOff_endpoint

/-- Exact-floor specialization of the tail-native endpoint: a family delivered at the two q20
directed floors themselves leaves no numerical hypothesis at all. -/
theorem omega_lt_236999_of_q20EventualStages_at_floor
    (K : Type u) [Field K] {stride : ℕ} (hstride : 0 < stride)
    (data : EventualWholeConstituentLaserVolumeLossData K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * q20RetainedFloor))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * q20VolumeFloor))) :
    omega K < q20Target :=
  omega_lt_236999_of_q20EventualStages K (q20StageBases stride hstride) data

/-! ## Convenience corollary: the stronger exact-sequence form

The two theorems below are **not** the interface S8 to S10 should build against.  They assume
a `SubexponentialLaserVolumeSequence`, which is strictly stronger than the paper asks: it
demands a stage at *every* positive repetition and exact nominal volume growth with *no*
volume loss.  They are kept only so that a lane which happens to hold the stronger object
does not have to weaken it by hand. -/

/-- Convenience corollary at the stronger exact-sequence hypothesis.  Prefer
`omega_lt_236999_of_q20EventualStages`. -/
theorem omega_lt_236999_of_q20VolumeSequence
    (K : Type u) [Field K] (b : Q20StageBases)
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) b.stride b.copyBase b.volumeBase) :
    omega K < q20Target := by
  refine omega_lt_of_cwPower_borderRankBudget K 5 8 q20Target_nonneg hextractions ?_
  have hvolume :=
    mul_le_mul_of_nonneg_left
      (q20BackedOffVolume_lt_q20VolumeFloor.le.trans b.volume_floor) q20Target_nonneg
  have hmargin := sourceBudget_lt_q20_backedOff_endpoint
  linarith [b.retained_floor]

/-- Exact-floor specialization of the convenience corollary. -/
theorem omega_lt_236999_of_q20VolumeSequence_at_floor
    (K : Type u) [Field K] {stride : ℕ} (hstride : 0 < stride)
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * q20RetainedFloor))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * q20VolumeFloor))) :
    omega K < q20Target :=
  omega_lt_236999_of_q20VolumeSequence K (q20StageBases stride hstride) hextractions

/-! ## The cyclic (Mode-B) variant

A Mode-B stage degenerates the three cyclic orientations jointly.  No conversion to an ordinary
sequence on one unsymmetrized `CW_5^(x8)` is owed: the committed cyclic rate already normalizes
by the `3 * stride` source copies, and cyclic soundness bounds that rate by the border rank of
the source itself.  The generic budget theorem lives with its non-cyclic twin in
`AlgebraicComplexity/Examples/CoppersmithWinogradCyclicVolumeEndpoint.lean`; only the q20
corollary is here.  Route found by Codex CW; reviewed by Codex 2.36x and Codex C2. -/

/-- **The cyclic q20 endpoint.**  A Mode-B stage producing the three cyclic orientations at three
times the q20 exponents per `sym3` unit proves `omega K < 2.36999`.  `hcyclic` is its only
hypothesis: stride positivity is already a field of the sequence, and no source normalization is
owed.

`hcyclic` is an open obligation, the Mode-B construction of row TW-27; it is not discharged in
this repository, so this is a conditional endpoint like the others. -/
theorem omega_lt_236999_of_q20CyclicStages
    (K : Type u) [Field K] {s : ℕ}
    (hcyclic : SubexponentialCyclicLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) s
      ((2 : ℝ) ^ ((s : ℝ) * (3 * q20RetainedFloor)))
      ((2 : ℝ) ^ (3 * (s : ℝ) * (3 * q20VolumeFloor)))) :
    omega K < q20Target := by
  have hbudget :=
    retained_add_omega_mul_volume_le_cwPowerBudget_of_cyclicSequence K 5 8 hcyclic
  have hmargin := sourceBudget_lt_q20_backedOff_endpoint
  have hvolume := mul_le_mul_of_nonneg_left
    q20BackedOffVolume_lt_q20VolumeFloor.le q20Target_nonneg
  have hpos := q20VolumeFloor_pos
  norm_num only [Nat.cast_ofNat] at hbudget
  nlinarith

end MatrixMultiplication.Q20EndpointAdapter
