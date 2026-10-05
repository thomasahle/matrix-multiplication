/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightPointMassLeaf
import MatrixMultiplication.TotalWeightAcceptanceAssembly

set_option autoImplicit false

/-!
# The depth-one (paper level-two) total-weight acceptance assembly

This module re-assembles the volume-only `2.36999` interface of
`MatrixMultiplication/TotalWeightAcceptanceAssembly.lean` at Lean **depth one** instead of depth
four.  It is the implementation of items 1–4 of the redirect specification recorded in
`better_bound/PAPER_AUDIT.md` §"Obligation-fidelity review 2026-08-28" §3.

## STATUS — DORMANT.  Refuted *for the published certificate's constants*, not structurally dead

**This file is not a live route — but the scope of its retirement is narrower than it first
read.**  Like its depth-four predecessor it is retained as a regression test for the generic
composition plumbing, and must not be cited as evidence for an unconditional endpoint.  The exact
status, corrected 2026-08-28:

> **Refuted for the published certificate's constants** — the `C′` split
> `(811/125, 433/250, 15021/2500)` and the total-weight candidate that realizes it — by the
> kernel-anchored chain below.  That part stands.
> **The constraint *system* is satisfiable by re-optimized certificates**: see
> `better_bound/flat_route_feasibility/VERDICT.md` (float-level evidence, unconverged,
> uncertified).  So the route is **dormant pending a certified new certificate**, not structurally
> dead.  **Depth ≥ 2 remains dead unconditionally** — that is the capacity obstruction
> `xWordCapacity_lt_outerBase_of_two_le_depth`, proved in this file.
> **`h3` itself is now uninhabitable at every depth**, by the outer `X`-word ceiling of
> `MatrixMultiplication/TotalWeightOuterCeiling.lean`
> (`TotalWeightAcceptanceAssembly.isEmpty_levelTwoOuterCountInput`, from
> `CWTotalWeightOuterCoarseCleanup.card_survivors_le_one`), so
> `omega_lt_236999_of_named_inputs_levelTwo` below is vacuous.  That theorem binds the *record* —
> isolating against the unrestricted coarse power — and **not** the flat frame: a hash-first
> cleanup faces `xWordCapacityBase` instead, which `outerBase_le_xWordCapacity_levelTwo` clears at
> depth one.  Scope: `better_bound/flat_route_feasibility/CONSTRUCTION_SCOPE.md`.

The depth-one obstruction is *not* the depth-four capacity one — that is proved not to apply here
(`outerBase_le_xWordCapacity_levelTwo`) — but a second, independent obstruction on the *inner*
side, discovered after this module was written.  At the published constants:

> A depth-one leaf that carries *the published certificate's* `C′` volume floor cannot carry *its*
> `C′` inner rate.  At those constants the two demands are in direct opposition.

Concretely, `h1.oneTypeLetters_ge` and `h1.volume_ge` cap the profile mass of corner-containing
chunk letters at `9 / 152`, and on that corner budget
`AlgebraicComplexity.Examples.exists_leg_depthOne_rateResidual_lt_433_div_1000` (landed,
kernel-checked, ten `#assert_axioms`) produces a tensor leg whose double-coarse rate residual is
below `433/1000` — while `h1.rate` with the certified level-two bottleneck demands that *every*
leg exceed `433/1000`.  `38 · (433/250) / 152 = 433/1000` on the nose, so the barrier is calibrated
to exactly this record.

**What the refutation does not say.**  It does not say that no depth-one leaf can satisfy the
system.  The barrier `inner ≤ 4 (H₂(β) + β)` is an *upper* bound on a leaf's inner rate: it firing
refutes a candidate, it not firing only means this obstruction is silent.  Re-optimizing inside the
certificate's own distribution space raises the outer stage from the published `6.499146` to
`≈ 6.746598` — the barrier-constrained study computes `≥ 6.554756` as what is needed, and the
capacity ceiling is `4 log₂ 5 = 9.287712` — and the resulting point sits *inside* the barrier cap
(`inner ≈ 1.696800` under cap `≈ 1.717810`) with endpoint slack `≈ +0.155475` at `ω = 2.36999`,
i.e. `ω ≈ 2.343988`.  Restricted to the published certificate's own nonzero support the result
survives at `≈ +0.138408`.  Those are floating-point candidate-generator numbers from runs that
were stopped before convergence: **no interval certificate, no exact exporter, no Lean**.  They are
enough to refute the *universal* reading of this retirement and not enough to claim an endpoint.
Full note and caveats: `better_bound/flat_route_feasibility/VERDICT.md`.

The refutation is *verified mathematics, not yet a kernel theorem*: converting it into `False`
needs three connectors that are deliberately unwritten — see the retirement note in
`MatrixMultiplication/TotalWeightAcceptanceAssemblyLevelTwoEndpoint.lean`, which lists them
exactly.  The project's live route is the paper's nested/conditional-laws construction, not this
flat one, and a connector on a dormant flat route is not worth the proof effort.

Everything below this line is the original module documentation, kept as written.

## Why depth one

In `better_bound/paper.tex` a level-`ℓ` shape sums to `2 ^ ℓ` and one CW support letter contributes
`2`, so a level-`ℓ` node is a block of `2 ^ (ℓ − 1)` CW letters.  In this tree `depth` is
`log₂ (#CW letters per chunk)`.  Hence **Lean depth `d` = paper level `d + 1`**, and the paper's
hashing quotient — the level-two shape, `2` CW letters, coarse alphabet `CWCoarseDigit 1` with
`coarseTotal 1 = 4`, five values — is `cwTotalWeightChunkCoarsening 1`, i.e. `depth = 1`.

The depth-four instantiation used by the superseded assembly is a paper "level five", which does
not exist in the recursion.  It is not merely unfaithful, it is *infeasible*: the `X`-word capacity
per `CW₅⁸` of a depth-`d` total-weight quotient is `(8 / 2 ^ d) · log₂ (2 ^ (d+1) + 1)`, which is
`2.5222` at `d = 4`, below the `C′` outer floor `6.488`.  That contradiction is
`TotalWeightAcceptanceNoGo.false_of_named_outer_inputs`.  At `d = 1` the same capacity is `9.2877`,
**above** the outer floor with `2.7997` bits of headroom per stride unit, and `d = 1` is the only
depth at which the `C′` split `(6.488, 1.732)` fits: `d = 0` has no conditional fibre, and `d = 2`
already misses by `0.148` bits.  Both halves of that statement are proved below
(`outerBase_le_xWordCapacity_levelTwo`, `xWordCapacity_lt_outerBase_of_two_le_depth`), so the
choice of depth is a theorem of this file and not a comment.

## What changes relative to the depth-four assembly

| item | depth four | depth one |
| --- | --- | --- |
| chunk | `16` CW letters | `2` CW letters (the paper's level-2 node) |
| coarse alphabet | `CWCoarseDigit 4` | `CWCoarseDigit 1`, five values |
| alignment | `8 · 38 · r = 2 ^ 4 · (19 r)` | `8 · 38 · r = 2 ^ 1 · (152 r)` |
| outer exponent | `levelFourOuterExponent r = 19 r − 1` | `levelTwoOuterExponent r = 152 r − 1` |
| profile mass | `19` | `152` |
| `X`-capacity per `CW₅⁸` | `2.5222` (infeasible) | `9.2877` (feasible) |

Everything else is *literally* reused.  `OuterFloorInput`, `OuterCountInput`,
`LevelTwoTableInput`, `innerRetainedFloor_le_innerRate`, `two_rpow_le_five_pow_295`,
`two_rpow_lt_of_floor_le`, `embeddedProfileMass_pos` and `trivialCoarseCleanup` of the depth-four
module are already parametric in `(q, depth, n)` and are imported unchanged; the `C′` floors of
`MatrixMultiplication/TotalWeightAcceptanceFloors.lean` are unchanged; `xSupport_injOn` is kept
(it is `lem:mapped-coarse-leaf`'s legwise disjointness, i.e. the paper's own hypothesis); and the
generic S3/S4/S6 constructors are applied at `depth := 1` with no de-pinning, exactly as the S3
handoff certifies.

## The volume floor still forces a *sparse* leaf — the one place the review's spec needs amending

The review's item 1 says the volume-floor letter count "carries over verbatim", and it does: the
`C′` floor needs `295` of the `8 · 38 = 304` `CW₅` letters of a stride block to carry a volume-`5`
block (`two_rpow_le_five_pow_295`, and `five_pow_294_lt_two_rpow` shows `294` is too few).  What
does *not* carry over is the suggestion (item 5) that the inner side may now be a leaf over the
**full** depth-one chunk support through the original
`exists_cwTotalWeightCanonicalInnerSequenceData`.  That constructor does typecheck at `depth = 1`
with no change — but its hypotheses are unsatisfiable at the `C′` volume floor:

* a `RationalTypedLeaf` over the full support spends at least one unit of mass on each of the
  `6 ^ 2 ^ 1 = 36` chunk letters (`card_cwChunkSupport_levelTwo`), and the alignment forces total
  mass `152`;
* a depth-one chunk letter is a pair of CW blocks, of which `w ∈ {0, 1, 2}` are volume-`5`; summed
  over the `36` letters, `∑ w = 36`;
* hence the number of volume-`5` letters in a stride block is
  `∑ count · w ≤ 2 · (152 − 36) + 36 = 268 < 295` (`fullSupport_volumeLetters_le`).

So the depth-one endpoint uses the **same sparse/embedded leaf shape as the depth-four one** — a
leaf on its own alphabet with an embedding into the chunk support — and the inner family is still
delivered as a `CanonicalInnerSequenceData` (that is what
`exists_cwTotalWeightEmbeddedCanonicalInnerSequenceData_ofDepth` returns), which is the interface
codex-2.36x's inner-family work plugs into.  The natural sparse alphabet here is the `9` chunk
letters both of whose blocks lie in `{cw011, cw101, cw110}`: they have volume `25` each, so a
mass-`152` profile on them realizes all `304` letters as volume-`5` ones, with `9` letters of slack
against the floor.  This removes the depth-four point-mass trap (there, mass `19` on the single
all-`cw011` chunk letter was forced), because `152` units spread over `9` letters is not a point
mass.

## The theorem

`omega_lt_236999_of_named_inputs_levelTwo` reads

```
(h1 : LevelTwoSparseInnerInput K letters dims)   -- the sparse depth-one leaf and its inner rate
(h2 : OuterFloorInput 1)                         -- the outer copy-base identity
(h3 : OuterCountInput K 5 1 levelTwoOuterExponent Part h2 (levelTwoCoarseReference h1))
(h4 : LevelTwoTableInput h1.innerRate)           -- the level-two table instantiation
⊢ omega K < TotalWeightAcceptanceFloors.acceptanceTarget
```

with the same discharge pattern as the depth-four assembly: the outer sequence datum (including
`source_restricts`, now through `8 · (38 · r) = 2 · (152 · r)`), the depth-one inner growth datum
with `ambient_upper` proved, the embedded marked-hashing extraction and its Behrend copy count, the
`hn` and `hfine` alignment premises, the base-two composition and the rectangular volume floor are
all discharged *inside*.

## Residual inputs and their owners

The residual list differs from the depth-four one in exactly two places: `h1.mass_eq` is `152`
rather than `19`, and the capacity side condition that made the depth-four residuals *jointly
inconsistent* is now proved to hold.  No residual was removed and none was added.

| input | statement | owner |
| --- | --- | --- |
| `h1.maximumEntropy` | conditional maximum entropy of the zero-extended sparse profile | codex-2.36x (rigidity / relativized criterion, handoff §S4.7.1) |
| `h1.rate`, `h4.realizes` | the realized inner rate at the level-two family exponent | codex-2.36x (segmented occurrence family) |
| `h1.volume_ge`, `h1.oneTypeLetters_ge` | `295` volume-`5` letters per stride block | here / S4 (discharged outright for the `9`-letter alphabet above) |
| `h2.base` | `2 ^ (38 · 811/125) = targetBase / combinedFieldBase …` | S1 numeric prep |
| `h3.*` | S6's residual table at `depth = 1`: the cleanup certificate, the four rate exports, `fullBucket`, `coarseWord_type` | S6 / codex-2.36x |
| `h4.certificate` | `BranchFloorCertified` over the emitted level-two tables | S1 emission |

Still open after the redirect, unchanged and *not* addressed here: `hyp:quotient-count`'s
obligations (i) exact coarse-type-class membership, (ii) uniform finite competitor/incidence
bounds, (iii) the copywise lift across the 126 level-3 nodes × 6 regions.  `h1`–`h3` still name no
certificate node.

## Elaboration note

The residual records are the depth-four module's, instantiated at `depth = 1`; the outer datum's
fields are read through S6's `ofChunkAlignedCoarseCleanup_spec` rather than by `rfl`.  Both
precautions are inherited from the depth-four assembly, where they were forced by the `3 ^ 16`
letter alphabet.  At `depth = 1` the alphabet has `9` labels and the precautions are free.
-/

namespace MatrixMultiplication.TotalWeightAcceptanceAssemblyLevelTwo

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.TotalWeightAcceptanceFloors
open MatrixMultiplication.TotalWeightAcceptanceAssembly

universe u v w x z

/-! ## The depth-one index convention -/

/-- The positive-power exponent forced by `8 · 38 · r = 2 · (152 · r)`.

This is the depth-one analogue of
`CWTotalWeightLocalizedOuterSequenceData.levelFourOuterExponent`, and the name records the paper
level: a depth-one chunk is a **level-two** node, a pair of CW letters. -/
def levelTwoOuterExponent (r : ℕ) : ℕ := 152 * r - 1

/-- The chunk-alignment identity of the depth-one route: a stride block of `8 · 38 = 304` `CW₅`
letters is exactly `152` chunks of `2 ^ 1 = 2` letters. -/
theorem levelTwo_align (r : ℕ) (hr : 0 < r) :
    8 * (38 * r) = 2 ^ 1 * (levelTwoOuterExponent r + 1) := by
  unfold levelTwoOuterExponent
  omega

/-- The mass identity behind the alignment, stated on its own: `8 · 38 = 2 · 152`. -/
theorem levelTwo_massIdentity : 8 * 38 = 2 ^ 1 * 152 := by norm_num

/-! ## The capacity side condition

For a total-weight quotient at Lean depth `d` the `X`-label alphabet has `2 ^ (d+1) + 1` elements
(the level-`(d+1)` shapes of a `2 ^ d`-letter block), and a stride-`38` block contributes
`8 · 38 / 2 ^ d = 304 / 2 ^ d` labels per repetition.  So the number of `X`-isolated coarse words
available per repetition is `(2 ^ (d+1) + 1) ^ (304 / 2 ^ d)`, and the outer stage can only request
`2 ^ (38 · outerRetainedFloor)` copies if that capacity is at least as large.

This section proves the request is met at `d = 1` and violated at every `d ≥ 2`; `d = 0` is the
trivial quotient, which has no conditional fibre at all and therefore no level-two stage `E₂`.
-/

/-- Exponential `X`-word capacity of a depth-`depth` total-weight quotient, per repetition of a
stride-`38` block of `CW₅⁸`. -/
noncomputable def xWordCapacityBase (depth : ℕ) : ℝ :=
  ((2 ^ (depth + 1) + 1 : ℕ) : ℝ) ^ ((304 : ℝ) / (2 : ℝ) ^ depth)

/-- At depth one the capacity base is exactly `5 ^ 152`: five level-two shapes, `152` chunks per
stride block. -/
theorem xWordCapacityBase_one : xWordCapacityBase 1 = ((5 : ℕ) ^ (152 : ℕ) : ℝ) := by
  have hbase : ((2 ^ (1 + 1) + 1 : ℕ) : ℝ) = (5 : ℝ) := by norm_num
  have hexp : (304 : ℝ) / (2 : ℝ) ^ (1 : ℕ) = ((152 : ℕ) : ℝ) := by norm_num
  rw [xWordCapacityBase, hbase, hexp, Real.rpow_natCast]
  norm_num

set_option exponentiation.threshold 512 in
/-- **The positive capacity side condition at depth one.**

`2 ^ (38 · 811/125) ≤ 5 ^ 152`: the `C′` outer copy base fits inside the depth-one `X`-word
capacity.  Numerically `38 · 6.488 = 246.544` bits are requested against `152 · log₂ 5 = 352.933`
available, a headroom of `106.39` bits per repetition (`2.7997` per stride unit).

This is the proved side condition that the review asks for: it is the reason the depth-one
instantiation is not vacuous, and together with `xWordCapacity_lt_outerBase_of_two_le_depth` it
makes the choice `depth = 1` forced rather than conventional. -/
theorem outerBase_le_xWordCapacity_levelTwo :
    (2 : ℝ) ^ ((38 : ℝ) * outerRetainedFloor) ≤ xWordCapacityBase 1 := by
  rw [xWordCapacityBase_one]
  have hrpow : (2 : ℝ) ^ ((38 : ℝ) * outerRetainedFloor) =
      Real.exp (Real.log 2 * ((38 : ℝ) * outerRetainedFloor)) :=
    Real.rpow_def_of_pos (by norm_num) _
  have hpow : ((5 : ℕ) ^ (152 : ℕ) : ℝ) = Real.exp (((152 : ℕ) : ℝ) * Real.log 5) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
    push_cast
    ring
  rw [hrpow, hpow]
  refine Real.exp_le_exp.mpr ?_
  have hlogTwo := Analysis.log_two_le_sharp
  have hlogFive := Analysis.log_five_ge_sharp
  simp only [outerRetainedFloor]
  push_cast
  nlinarith [hlogTwo, hlogFive]

/-- Auxiliary decay bound: `304 · (d + 2) ≤ 190 · 2 ^ d` for every `d ≥ 3`, with equality at
`d = 3`.  This is the monotone half of the capacity guard. -/
theorem capacity_decay (d : ℕ) (hd : 3 ≤ d) : 304 * (d + 2) ≤ 190 * 2 ^ d := by
  induction d with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge n 3 with hn | hn
      · have hn2 : n = 2 := by omega
        subst hn2
        norm_num
      · have hstep := ih (by omega)
        have h8 : (8 : ℕ) ≤ 2 ^ n := by
          calc (8 : ℕ) = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        have hsplit : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
        rw [hsplit]
        generalize (2 : ℕ) ^ n = p at hstep h8 ⊢
        omega

set_option exponentiation.threshold 512 in
/-- **The negative capacity guard.**  For every Lean depth `d ≥ 2` the available `X`-word capacity
is strictly below the `C′` outer copy base, so a re-instantiation of this chain at any coarser
quotient fails outright instead of going vacuous.

Only finitely many depths are of independent interest, and the statement is honest about which:
the capacity `(304 / 2 ^ d) · log₂ (2 ^ (d+1) + 1)` is decreasing in `d`, so the two cases `d = 2`
(exactly `9 ^ 76 = 3 ^ 152 < 2 ^ 241`, missing the request by `5.6` bits per repetition) and
`d ≥ 3` (crudely `(2 ^ (d+2)) ^ (304 / 2 ^ d) ≤ 2 ^ 190`) exhaust it.  Depth `0` is excluded
deliberately: it is the trivial quotient, whose conditional fibre is empty, so it has no level-two
stage to carry `E₂` at all.  Depth `1` is the positive case
`outerBase_le_xWordCapacity_levelTwo`. -/
theorem xWordCapacity_lt_outerBase_of_two_le_depth (d : ℕ) (hd : 2 ≤ d) :
    xWordCapacityBase d < (2 : ℝ) ^ ((38 : ℝ) * outerRetainedFloor) := by
  have htarget : (2 : ℝ) ^ (241 : ℝ) < (2 : ℝ) ^ ((38 : ℝ) * outerRetainedFloor) := by
    refine Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ?_
    simp only [outerRetainedFloor]
    norm_num
  rcases Nat.lt_or_ge d 3 with hlt | hge
  · -- `d = 2`: the exact comparison `9 ^ 76 = 3 ^ 152 < 2 ^ 241`.
    have hd2 : d = 2 := by omega
    subst hd2
    have hbase : ((2 ^ (2 + 1) + 1 : ℕ) : ℝ) = (9 : ℝ) := by norm_num
    have hexp : (304 : ℝ) / (2 : ℝ) ^ (2 : ℕ) = ((76 : ℕ) : ℝ) := by norm_num
    have hnat : (9 : ℕ) ^ (76 : ℕ) < 2 ^ (241 : ℕ) := by norm_num
    have hcap : xWordCapacityBase 2 < (2 : ℝ) ^ (241 : ℕ) := by
      rw [xWordCapacityBase, hbase, hexp, Real.rpow_natCast]
      exact_mod_cast hnat
    refine lt_trans hcap ?_
    rw [← Real.rpow_natCast (2 : ℝ) 241]
    exact_mod_cast htarget
  · -- `d ≥ 3`: the crude bound `2 ^ (d+1) + 1 ≤ 2 ^ (d+2)` and the decay lemma.
    have hbaseLe : ((2 ^ (d + 1) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) + 2) := by
      have hnat : (2 ^ (d + 1) + 1 : ℕ) ≤ 2 ^ (d + 2) := by
        have : (1 : ℕ) ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
        have hd2 : (2 : ℕ) ^ (d + 2) = 2 ^ (d + 1) + 2 ^ (d + 1) := by ring
        omega
      have hcast : ((2 ^ (d + 2) : ℕ) : ℝ) = (2 : ℝ) ^ ((d : ℝ) + 2) := by
        rw [show ((d : ℝ) + 2) = ((d + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
        push_cast
        ring
      calc ((2 ^ (d + 1) + 1 : ℕ) : ℝ) ≤ ((2 ^ (d + 2) : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (2 : ℝ) ^ ((d : ℝ) + 2) := hcast
    have hexpPos : (0 : ℝ) < (304 : ℝ) / (2 : ℝ) ^ d := by positivity
    have hmono : xWordCapacityBase d ≤
        ((2 : ℝ) ^ ((d : ℝ) + 2)) ^ ((304 : ℝ) / (2 : ℝ) ^ d) := by
      refine Real.rpow_le_rpow (by positivity) hbaseLe hexpPos.le
    have hcollapse : ((2 : ℝ) ^ ((d : ℝ) + 2)) ^ ((304 : ℝ) / (2 : ℝ) ^ d) =
        (2 : ℝ) ^ (((d : ℝ) + 2) * ((304 : ℝ) / (2 : ℝ) ^ d)) := by
      rw [← Real.rpow_natCast (2 : ℝ) d]
      rw [← Real.rpow_mul (by norm_num)]
    have hdecay : ((d : ℝ) + 2) * ((304 : ℝ) / (2 : ℝ) ^ d) ≤ (190 : ℝ) := by
      have hnat := capacity_decay d hge
      have hpow : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
      rw [mul_div_assoc', div_le_iff₀ hpow]
      have hcast : ((304 * (d + 2) : ℕ) : ℝ) ≤ ((190 * 2 ^ d : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast at hcast
      nlinarith
    calc xWordCapacityBase d ≤ (2 : ℝ) ^ (((d : ℝ) + 2) * ((304 : ℝ) / (2 : ℝ) ^ d)) := by
          rw [← hcollapse]; exact hmono
      _ ≤ (2 : ℝ) ^ (190 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hdecay
      _ < (2 : ℝ) ^ (241 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
      _ < (2 : ℝ) ^ ((38 : ℝ) * outerRetainedFloor) := htarget

/-! ## `h1`: the sparse depth-one inner leaf and its rate -/

/-- **Residual `h1` at depth one.**  Identical to the depth-four `SparseInnerInput` except that the
letter embedding lands in the depth-*one* chunk support and the chunk-alignment handshake is
`8 · 38 = 2 · 152` instead of `8 · 38 = 16 · 19`.

The mass `152` is what makes the depth-one route feasible where the depth-four one was not: a
mass-`152` profile on the nine all-one-type chunk letters realizes all `304` volume-`5` letters of
a stride block and is nowhere near a point mass, whereas mass `19` at depth four forced the entire
mass onto the single all-`cw011` chunk letter. -/
structure LevelTwoSparseInnerInput (K : Type u) [CommRing K]
    (letters : Type) [Fintype letters] [Nonempty letters]
    (dims : Leg → Type) [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)] where
  /-- The sparse rational typed leaf. -/
  leaf : RationalTypedLeaf letters dims
  /-- Its letters, as an embedding into the depth-one chunk support. -/
  embed : letters ↪ (cwChunkPartitionedTensor K 5 1).support
  /-- The leaf carries the canonical chunk constituent dimensions. -/
  dimension_eq : ∀ i c,
    leaf.dimension i c = cwChunkConstituentDimension K 5 1 (embed i) c
  /-- Chunk-alignment handshake: a stride block of `8 · 38 = 304` `CW₅` letters is `152` chunks of
  `2 ^ 1 = 2`, so the profile mass must be `152`. -/
  mass_eq : leaf.profile.mass = 152
  /-- Number of volume-`5` `CW₅` letters in one stride block of the leaf. -/
  oneTypeLetters : ℕ
  /-- The `C′` volume floor in letter-count form. -/
  oneTypeLetters_ge : 295 ≤ oneTypeLetters
  /-- Each volume-`5` letter contributes a factor `5` to the rectangular volume. -/
  volume_ge : (5 : ℕ) ^ oneTypeLetters ≤
    leaf.dimensionProduct .X * leaf.dimensionProduct .Y * leaf.dimensionProduct .Z
  /-- Conditional maximum-entropy certificate for the zero-extended profile. -/
  maximumEntropy : WordType.IsMaximumEntropyInMappedFiber (cwChunkCoordinate K 5 1)
    (WordType.normalizedProfileProbability (cwEmbeddedChunkProfile leaf embed)
      (embeddedProfileMass_pos leaf embed))
  /-- The competitor slack `δ` of the marked hashing argument. -/
  slack : ℝ
  one_lt_slack : 1 < slack
  /-- The inner retained rate this leaf realizes, per stride block. -/
  innerRate : ℝ
  /-- The realized rate, in the exact shape the embedded inner constructor consumes. -/
  rate : (2 : ℝ) ^ (((38 : ℕ) : ℝ) * innerRate) <
    cwTotalWeightInnerTargetBase K 5 1 (cwEmbeddedChunkProfile leaf embed) /
      (slack * cwTotalWeightInnerCompetitorBase K 5 1 (cwEmbeddedChunkProfile leaf embed)
        (cwChunkAmbientEntropyBase (cwEmbeddedChunkProfile leaf embed)))

namespace LevelTwoSparseInnerInput

variable {K : Type u} [CommRing K]
variable {letters : Type} [Fintype letters] [Nonempty letters]
variable {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]

/-- The zero-extended profile of the sparse leaf has mass exactly `152`. -/
theorem embeddedMass (data : LevelTwoSparseInnerInput K letters dims) :
    WordType.profileMass (cwEmbeddedChunkProfile data.leaf data.embed) = 152 := by
  rw [profileMass_cwEmbeddedChunkProfile]
  exact data.mass_eq

end LevelTwoSparseInnerInput

/-- The depth-one inner growth datum of a sparse leaf: S4's zero-safe maximum-entropy constructor,
applied at `depth = 1`, to the zero-extended profile.  Its `ambient_upper` field is proved, not
assumed. -/
noncomputable def levelTwoGrowthDatum {K : Type u} [CommRing K]
    {letters : Type} [Fintype letters] [Nonempty letters]
    {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]
    (data : LevelTwoSparseInnerInput K letters dims) :
    CWTotalWeightInnerGrowthDataAtDepth K 5 1
      (cwEmbeddedChunkProfile data.leaf data.embed)
      (cwChunkAmbientEntropyBase (cwEmbeddedChunkProfile data.leaf data.embed))
      (cwChunkAmbientTypeLoss (cwEmbeddedChunkProfile data.leaf data.embed)) :=
  cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe K 5 1
    (cwEmbeddedChunkProfile data.leaf data.embed)
    (embeddedProfileMass_pos data.leaf data.embed) data.maximumEntropy

/-- **The `hn` handshake at depth one, discharged.**  The growth datum's positive-power exponent is
exactly the outer datum's `152 · r − 1`. -/
theorem levelTwoGrowthDatum_exponent {K : Type u} [CommRing K]
    {letters : Type} [Fintype letters] [Nonempty letters]
    {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]
    (data : LevelTwoSparseInnerInput K letters dims) (r : ℕ) :
    (levelTwoGrowthDatum data).exponent r = levelTwoOuterExponent r := by
  simp only [levelTwoGrowthDatum, cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe_exponent,
    data.embeddedMass, levelTwoOuterExponent]

/-- The growth datum's canonical coarse representative, transported to the outer index length. -/
noncomputable def levelTwoCoarseReference {K : Type u} [CommRing K]
    {letters : Type} [Fintype letters] [Nonempty letters]
    {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]
    (data : LevelTwoSparseInnerInput K letters dims) (r : ℕ) :
    PositiveWord (CWTotalWeightCoarseSupport K 5 1) (levelTwoOuterExponent r) :=
  positiveWordCast (levelTwoGrowthDatum_exponent data r)
    ((levelTwoGrowthDatum data).coarseWord r)

/-! ## The assembled depth-one outer datum -/

/-- The depth-one outer total-weight sequence at stride `38`, built from `h2` and `h3` through
S6's depth-generic `ofChunkAlignedCoarseCleanup` at `depth := 1`.  The `fineType` family is
*chosen* to be the one the inner constructor reads back, which is what discharges `hfine`. -/
noncomputable def outerData {K : Type u} [CommRing K]
    {letters : Type} [Fintype letters] [Nonempty letters]
    {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]
    {Part : Type} [Fintype Part]
    (h1 : LevelTwoSparseInnerInput K letters dims) (h2 : OuterFloorInput 1)
    (h3 : OuterCountInput K 5 1 levelTwoOuterExponent Part h2 (levelTwoCoarseReference h1)) :
    CWTotalWeightLocalizedOuterSequenceData K 5 1
      (Tensor.power (coppersmithWinograd K 5) 8) 38
      ((2 : ℝ) ^ (((38 : ℕ) : ℝ) * outerRetainedFloor)) :=
  CWTotalWeightLocalizedOuterSequenceData.ofChunkAlignedCoarseCleanup K 5 1 8 38
    h2.targetBase h2.xFieldBase _ (by norm_num) h2.targetBase_pos h2.xFieldBase_nonneg
    h2.ySourceProfile h2.zSourceProfile
    h2.yJointExponentPerRepetition h2.zJointExponentPerRepetition h2.base
    h3.characteristicFloor h3.targetLoss h3.xFieldLoss h3.targetCount
    h3.xRequirement h3.visibleRequirement levelTwoOuterExponent
    (fun r ↦ cwTotalWeightFineMarginalType K 5 1
      (WordType.proportionalCounts (cwEmbeddedChunkProfile h1.leaf h1.embed) r))
    h3.cleanup levelTwo_align h3.targetLoss_subexponential h3.xFieldLoss_subexponential
    h3.targetLoss_pos h3.xFieldLoss_pos h3.count_pos h3.targetGrowth
    h3.xRequirement_le h3.visibleRequirement_le h3.fullBucket

/-- The four fields of `outerData` that the inner constructor reads back, obtained from S6's
`ofChunkAlignedCoarseCleanup_spec`. -/
theorem outerData_spec {K : Type u} [CommRing K]
    {letters : Type} [Fintype letters] [Nonempty letters]
    {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]
    {Part : Type} [Fintype Part]
    (h1 : LevelTwoSparseInnerInput K letters dims) (h2 : OuterFloorInput 1)
    (h3 : OuterCountInput K 5 1 levelTwoOuterExponent Part h2 (levelTwoCoarseReference h1)) :
    (outerData h1 h2 h3).n = levelTwoOuterExponent ∧
      (outerData h1 h2 h3).fineType =
        (fun r ↦ cwTotalWeightFineMarginalType K 5 1
          (WordType.proportionalCounts (cwEmbeddedChunkProfile h1.leaf h1.embed) r)) ∧
      (∀ r, (outerData h1 h2 h3).count r = (h3.cleanup.survivors r).card) ∧
      HEq (outerData h1 h2 h3).coarseWord h3.cleanup.coarseWord :=
  CWTotalWeightLocalizedOuterSequenceData.ofChunkAlignedCoarseCleanup_spec K 5 1 8 38
    h2.targetBase h2.xFieldBase _ (by norm_num) h2.targetBase_pos h2.xFieldBase_nonneg
    h2.ySourceProfile h2.zSourceProfile h2.yJointExponentPerRepetition
    h2.zJointExponentPerRepetition h2.base h3.characteristicFloor h3.targetLoss h3.xFieldLoss
    h3.targetCount h3.xRequirement h3.visibleRequirement levelTwoOuterExponent
    (fun r ↦ cwTotalWeightFineMarginalType K 5 1
      (WordType.proportionalCounts (cwEmbeddedChunkProfile h1.leaf h1.embed) r))
    h3.cleanup levelTwo_align
    h3.targetLoss_subexponential h3.xFieldLoss_subexponential h3.targetLoss_pos
    h3.xFieldLoss_pos h3.count_pos h3.targetGrowth h3.xRequirement_le h3.visibleRequirement_le
    h3.fullBucket rfl

/-! ## The depth-one embedded endpoint -/

set_option exponentiation.threshold 512 in
/-- The depth-one analogue of
`TotalWeightLeanEndpoint.omega_lt_236999_of_levelFourEmbeddedCanonicalInner`: a sparse embedded
depth-one leaf meeting the `C′` inner-rate and volume floors, combined with the `C′` outer sequence
at any fixed stride, proves `omega < 2.36999`.

Only the depth changes; the inner constructor
(`exists_cwTotalWeightEmbeddedCanonicalInnerSequenceData_ofDepth`), the additive retained
composition and the acceptance endpoint are all depth-free and are reused verbatim. -/
theorem omega_lt_236999_of_levelTwoEmbeddedCanonicalInner
    (K : Type u) [Field K]
    {stride : ℕ}
    (outer : CWTotalWeightLocalizedOuterSequenceData.{u, u, w}
      K 5 1 (Tensor.power (coppersmithWinograd K 5) 8) stride
        ((2 : ℝ) ^ ((stride : ℝ) * outerRetainedFloor)))
    {I : Type z} [Fintype I] [Nonempty I]
    {C : Leg → Type x} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K 5 1).support)
    (hdimension : ∀ i c,
      leaf.dimension i c = cwChunkConstituentDimension K 5 1 (letter i) c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (growth : CWTotalWeightInnerGrowthDataAtDepth K 5 1
      (cwEmbeddedChunkProfile leaf letter) ambientBase ambientLoss)
    (hn : ∀ r, outer.n r = growth.exponent r)
    (hfine : ∀ r, outer.fineType r =
      cwTotalWeightFineMarginalType K 5 1
        (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) r))
    (hcoarseWordType : ∀ r i,
      WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K 5 1) (outer.n r)
            (outer.coarseWord r i)) =
        WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K 5 1) (outer.n r)
            (positiveWordCast (hn r).symm (growth.coarseWord r))))
    {δ : ℝ} (hδ : 1 < δ)
    (hWrate :
      (2 : ℝ) ^ ((stride : ℝ) * innerRetainedFloor) <
        cwTotalWeightInnerTargetBase K 5 1 (cwEmbeddedChunkProfile leaf letter) /
          (δ * cwTotalWeightInnerCompetitorBase K 5 1
            (cwEmbeddedChunkProfile leaf letter) ambientBase))
    (hvolume : (2 : ℝ) ^ (3 * (stride : ℝ) * volumeFloor) ≤
      ((leaf.dimensionProduct .X * leaf.dimensionProduct .Y *
        leaf.dimensionProduct .Z : ℕ) : ℝ)) :
    omega K < acceptanceTarget := by
  obtain ⟨inner⟩ :=
    exists_cwTotalWeightEmbeddedCanonicalInnerSequenceData_ofDepth
      outer leaf letter hdimension growth hn hfine hcoarseWordType hδ
      (Real.rpow_pos_of_pos (by norm_num) _) hWrate
  have hsequence := inner.toSubexponentialLaserVolumeSequence_addRetained
  have hcopy :
      (2 : ℝ) ^ ((stride : ℝ) * retainedFloor) ≤
        (2 : ℝ) ^ ((stride : ℝ) * (outerRetainedFloor + innerRetainedFloor)) := by
    rw [retainedFloor_eq_outer_add_inner]
  exact TotalWeightLeanEndpoint.omega_lt_236999_of_subexponentialVolumeSequence_acceptance_anyStride
    K (hsequence.mono (by positivity) hcopy (by positivity) hvolume)

/-! ## The depth-one assembly theorem -/

set_option exponentiation.threshold 512 in
/-- **The depth-one (paper level-two) assembly.**

Everything structural is discharged inside:

* the depth-one outer sequence datum, including the derived `source_restricts` chain
  `8 · (38 · r) = 2 · (152 · r)` (S6, at `depth := 1`);
* the depth-one inner growth datum with `ambient_upper` proved (S4, at `depth := 1`);
* the embedded marked-hashing inner extraction and its Behrend copy count (S3 + the embedded
  route), delivered as a `CanonicalInnerSequenceData`;
* the `hn` and `hfine` alignment premises;
* the base-two composition `2 ^ (38 · outer) · 2 ^ (38 · inner) = 2 ^ (38 · 8.22)` and the
  rectangular volume base;
* the volume floor, from the letter count of `h1`.

**Superseded, for the published certificate's constants.**  When this was written the four
residuals were not known to be jointly inconsistent — the capacity obstruction that refutes the
depth-four interface is indeed proved *not* to apply here (`outerBase_le_xWordCapacity_levelTwo`),
with `106.39` bits of headroom per repetition.  A second, independent obstruction on the inner side
was found afterwards and it does refute them **at the published `C′` constants**:
`h1.volume_ge` + `h1.oneTypeLetters_ge` cap the corner mass at `9/152`, and
`AlgebraicComplexity.Examples.exists_leg_depthOne_rateResidual_lt_433_div_1000` then contradicts
`h1.rate` at any inner rate the certified level-two bottleneck permits.

Scope, corrected 2026-08-28: that refutation is **certificate-conditional**.  The constraint
*system* is satisfiable by re-optimized certificates — a re-optimized outer stage reaching
`≈ 6.746598` (needed `≥ 6.554756`, capacity `9.287712`) clears the barrier with positive endpoint
slack — per `better_bound/flat_route_feasibility/VERDICT.md`, which is float-level, unconverged and
uncertified evidence.  So this interface is **dormant pending a certified new certificate, not
structurally dead**; depth `≥ 2` is dead unconditionally by capacity
(`xWordCapacity_lt_outerBase_of_two_le_depth`).  See the module header and
`MatrixMultiplication/TotalWeightAcceptanceAssemblyLevelTwoEndpoint.lean`.  This theorem is
retained as a regression test for the generic composition plumbing, not as an endpoint. -/
theorem omega_lt_236999_of_named_inputs_levelTwo
    (K : Type u) [Field K]
    {letters : Type} [Fintype letters] [Nonempty letters]
    {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]
    {Part : Type} [Fintype Part]
    (h1 : LevelTwoSparseInnerInput K letters dims)
    (h2 : OuterFloorInput 1)
    (h3 : OuterCountInput K 5 1 levelTwoOuterExponent Part h2 (levelTwoCoarseReference h1))
    (h4 : LevelTwoTableInput h1.innerRate) :
    omega K < acceptanceTarget := by
  have hWrate : (2 : ℝ) ^ (((38 : ℕ) : ℝ) * innerRetainedFloor) <
      cwTotalWeightInnerTargetBase K 5 1 (cwEmbeddedChunkProfile h1.leaf h1.embed) /
        (h1.slack * cwTotalWeightInnerCompetitorBase K 5 1
          (cwEmbeddedChunkProfile h1.leaf h1.embed)
          (cwChunkAmbientEntropyBase (cwEmbeddedChunkProfile h1.leaf h1.embed))) :=
    two_rpow_lt_of_floor_le (by positivity) (innerRetainedFloor_le_innerRate h4) h1.rate
  have hvolume : (2 : ℝ) ^ (3 * (((38 : ℕ) : ℝ)) * volumeFloor) ≤
      ((h1.leaf.dimensionProduct .X * h1.leaf.dimensionProduct .Y *
        h1.leaf.dimensionProduct .Z : ℕ) : ℝ) := by
    refine two_rpow_le_five_pow_295.trans ?_
    have hstep : (5 : ℕ) ^ (295 : ℕ) ≤ (5 : ℕ) ^ h1.oneTypeLetters :=
      Nat.pow_le_pow_right (by norm_num) h1.oneTypeLetters_ge
    exact_mod_cast hstep.trans h1.volume_ge
  exact omega_lt_236999_of_levelTwoEmbeddedCanonicalInner
    K (outerData h1 h2 h3)
    h1.leaf h1.embed h1.dimension_eq (levelTwoGrowthDatum h1)
    (fun r ↦ (levelTwoGrowthDatum_exponent h1 r).symm)
    (fun r ↦ congrFun (outerData_spec h1 h2 h3).2.1 r)
    (fun r i ↦ h3.coarseWord_type r i)
    h1.one_lt_slack hWrate hvolume

/-! ## Feasibility of the depth-one residuals -/

/-- The `295` volume-`5` letters demanded by the `C′` volume floor fit inside the `8 · 38 = 304`
`CW₅` letters of a mass-`152` stride block of depth-one chunks, with `9` letters left free.

This is the depth-one analogue of `TotalWeightAcceptanceAssembly.levelFour_letterBudget`, and it is
the arithmetic that makes `LevelTwoSparseInnerInput` satisfiable at all. -/
theorem levelTwo_letterBudget : 295 ≤ 152 * 2 ^ 1 ∧ 152 * 2 ^ 1 = 8 * 38 := by
  constructor <;> norm_num

/-- The depth-one chunk support has `36` letters. -/
theorem card_cwChunkSupport_levelTwo (K : Type u) [CommRing K] :
    Fintype.card (cwChunkPartitionedTensor K 5 1).support = 36 := by
  rw [card_cwChunkPartitionedTensor_support]
  norm_num

/-- **The depth-four cardinality obstruction has no depth-one analogue.**

`no_levelFour_leaf_growthData_matches_outerExponent` rules out the depth-four index convention for
every leaf over the full chunk support, because `6 ^ 2 ^ 4 = 2 821 109 907 456` letters cannot fit
in mass `19`.  At depth one the corresponding count is `6 ^ 2 ^ 1 = 36 ≤ 152`, so that argument
does not apply and the mass-`152` profiles form a genuinely large family. -/
theorem card_cwChunkSupport_levelTwo_le_mass (K : Type u) [CommRing K] :
    Fintype.card (cwChunkPartitionedTensor K 5 1).support ≤ 152 := by
  rw [card_cwChunkSupport_levelTwo]
  norm_num

/-- The depth-one chunk support is inhabited, so a sparse letter embedding exists. -/
theorem nonempty_cwChunkSupport_levelTwo (K : Type u) [CommRing K] :
    Nonempty ((cwChunkPartitionedTensor K 5 1).support) :=
  ⟨cwChunkSupportWitness K 5 1⟩

/-- `OuterFloorInput 1` is inhabited in isolation, by the same definitional argument as at depth
four: the copy-base identity *defines* the target base once the field bases are fixed. -/
noncomputable def witnessOuterFloorLevelTwo : OuterFloorInput 1 where
  targetBase := (2 : ℝ) ^ (((38 : ℕ) : ℝ) * outerRetainedFloor) *
    CWTotalWeightLocalizedOuterSequenceData.combinedFieldBase 0
      (cwTotalWeightVisibleFeatureFieldBase (depth := 1) (fun _ ↦ 0) (fun _ ↦ 0) 0 0)
  xFieldBase := 0
  targetBase_pos :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (CWTotalWeightLocalizedOuterSequenceData.combinedFieldBase_pos _ _)
  xFieldBase_nonneg := le_rfl
  ySourceProfile := fun _ ↦ 0
  zSourceProfile := fun _ ↦ 0
  yJointExponentPerRepetition := 0
  zJointExponentPerRepetition := 0
  base := by
    rw [eq_div_iff
      (CWTotalWeightLocalizedOuterSequenceData.combinedFieldBase_pos 0
        (cwTotalWeightVisibleFeatureFieldBase (depth := 1) (fun _ ↦ 0) (fun _ ↦ 0) 0 0)).ne']

/-! ### The index convention is realized: the depth-four no-go has no depth-one analogue -/

/-- The zero-extended profile of the canonical depth-one feasibility leaf: mass `152` on the
maximal-volume (all-`cw011`) chunk letter, zero elsewhere. -/
noncomputable def levelTwoPointProfile (K : Type u) [CommRing K] :
    (cwChunkPartitionedTensor K 5 1).support → ℕ :=
  cwEmbeddedChunkProfile
    (cwChunkPointLeaf K 5 1 (by norm_num) (cwChunkOneTypeWitness K 5 1) 152 (by norm_num))
    (cwChunkPointEmbedding K 5 1 (cwChunkOneTypeWitness K 5 1))

/-- **The depth-four alignment obstruction is false at depth one.**

`no_levelFour_leaf_growthData_matches_outerExponent` says that at depth four *no* growth datum over
a leaf of the chunk support can have the outer index convention `19 · r − 1`.  Its depth-one
analogue fails: the growth datum below has exponent exactly `levelTwoOuterExponent r = 152 · r − 1`,
with both quantitative fields proved — `ambient_upper` by S4's zero-safe bound and the
maximum-entropy input by rigidity of the point mass
(`Examples.cwChunkPointLeaf_maximumEntropy`).

The witness is deliberately the extreme one: a point mass carries no conditional entropy, so it
cannot also discharge the rate premise `h1.rate`.  What it establishes is that nothing *structural*
— no cardinality and no alignment argument — rules out the depth-one index convention, which is
exactly what failed at depth four. -/
theorem exists_growthDatum_matching_levelTwoOuterExponent (K : Type u) [CommRing K] :
    ∃ (ambientBase : ℝ) (ambientLoss : ℕ → ℝ)
      (growth : CWTotalWeightInnerGrowthDataAtDepth K 5 1 (levelTwoPointProfile K)
        ambientBase ambientLoss),
      ∀ r, growth.exponent r = levelTwoOuterExponent r :=
  ⟨_, _,
    cwChunkPointGrowthDatum K 5 1 (by norm_num) (cwChunkOneTypeWitness K 5 1) 152 (by norm_num),
    fun r ↦ by
      rw [cwChunkPointGrowthDatum_exponent]
      rfl⟩

set_option exponentiation.threshold 512 in
/-- The same witness clears the `C′` volume floor outright: all `2 · 152 = 304` `CW₅` letters of
its stride block carry a volume-`5` block, against the `295` the floor demands. -/
theorem levelTwoPointLeaf_volume_ge (K : Type u) [CommRing K] :
    (5 : ℕ) ^ (295 : ℕ) ≤
      (cwChunkPointLeaf K 5 1 (by norm_num) (cwChunkOneTypeWitness K 5 1) 152
          (by norm_num)).dimensionProduct .X *
        (cwChunkPointLeaf K 5 1 (by norm_num) (cwChunkOneTypeWitness K 5 1) 152
          (by norm_num)).dimensionProduct .Y *
        (cwChunkPointLeaf K 5 1 (by norm_num) (cwChunkOneTypeWitness K 5 1) 152
          (by norm_num)).dimensionProduct .Z := by
  have hvolume := cwChunkPointLeaf_oneTypeWitness_volume K 5 1 (by norm_num) 152 (by norm_num)
  have h304 : ((5 : ℕ) ^ 2 ^ 1) ^ (152 : ℕ) = 5 ^ (304 : ℕ) := by
    rw [← pow_mul]
    congr 1
  rw [hvolume, h304]
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- **Why the depth-one inner leaf must still be sparse.**

Arithmetic core of the volume obstruction for a leaf over the *full* depth-one chunk support.  With
`c i ≥ 1` on each of the `36` chunk letters, total mass `152`, and `w i ≤ 2` the number of
volume-`5` blocks of letter `i` with `∑ w = 36` (each of the two positions of a chunk letter ranges
over the six CW blocks, three of which have volume `5`), the number of volume-`5` `CW₅` letters in
a stride block is at most `2 · (152 − 36) + 36 = 268`, short of the `295` demanded by the `C′`
volume floor (`two_rpow_le_five_pow_295`, `five_pow_294_lt_two_rpow`).

The three combinatorial inputs (`36 ≤ #letters`, `∑ w ≤ 36` and `w i ≤ 2`) are stated as
hypotheses rather than proved from the chunk support: they are the only facts this statement takes
on trust, and they are what makes the full-support route — the shape suggested by item 5 of the
redirect spec — unusable at the `C′` floor.  The assembly above therefore keeps the sparse/embedded
leaf. -/
theorem fullSupport_volumeLetters_le
    {ι : Type*} [Fintype ι] (c w : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hmass : ∑ i, c i = 152) (hcard : 36 ≤ Fintype.card ι)
    (hw : ∀ i, w i ≤ 2) (hwsum : ∑ i, w i ≤ 36) :
    ∑ i, c i * w i ≤ 268 := by
  classical
  set d : ι → ℕ := fun i ↦ c i - 1 with hd
  have hcd : ∀ i, c i = 1 + d i := by
    intro i
    have := hc i
    simp only [hd]
    omega
  have hstep : ∀ i, c i * w i ≤ w i + 2 * d i := by
    intro i
    have hmul : d i * w i ≤ d i * 2 := Nat.mul_le_mul_left _ (hw i)
    calc c i * w i = w i + d i * w i := by rw [hcd i]; ring
      _ ≤ w i + d i * 2 := Nat.add_le_add_left hmul _
      _ = w i + 2 * d i := by ring
  have hdsum : ∑ i, d i + Fintype.card ι = 152 := by
    have hsum : ∑ i, c i = ∑ i, d i + ∑ _i : ι, 1 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hcd i]; ring
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
    omega
  calc ∑ i, c i * w i ≤ ∑ i, (w i + 2 * d i) := Finset.sum_le_sum fun i _ ↦ hstep i
    _ = ∑ i, w i + 2 * ∑ i, d i := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 268 := by omega

end MatrixMultiplication.TotalWeightAcceptanceAssemblyLevelTwo
