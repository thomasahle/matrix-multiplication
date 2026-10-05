/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.TotalWeightAcceptanceAssemblyLevelTwo
import MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedCertificate

set_option autoImplicit false

/-!
# The depth-one `2.36999` endpoint with `h2` and `h4.certificate` discharged

`MatrixMultiplication/TotalWeightAcceptanceAssemblyLevelTwo.lean` proves

```
omega_lt_236999_of_named_inputs_levelTwo (h1) (h2 : OuterFloorInput 1) (h3) (h4) :
  omega K < acceptanceTarget
```

and lists four residual inputs with their owners.  Two of them were owned here.  This module
removes both from the statement.

## STATUS — DORMANT.  `omega_lt_236999_of_inner_inputs` is refuted *at the published constants*

**Scope, and it is narrower than the first version of this note claimed.**

* **Refuted for the published certificate's constants.**  `LevelTwoSparseInnerInput` together with
  `hrate` — where `hrate` is read against the *published* level-two certificate `e7987d7f…` and the
  `C′` split `(811/125, 433/250, 15021/2500)` — is uninhabitable.  That is the kernel-anchored
  chain below (steps 1 and 4 are Lean theorems; steps 2 and 3 are verified, not kernel-checked),
  and it stands.
* **The constraint *system* is satisfiable by re-optimized certificates.**  Re-optimizing inside
  the certificate's own distribution space produces points that satisfy the whole system —
  including the depth-one rate barrier — with **positive slack**.  See
  `better_bound/flat_route_feasibility/VERDICT.md`: float-level evidence, runs stopped before
  convergence, **uncertified** (no interval arithmetic, no exact exporter, no Lean).
* **Therefore: dormant, not dead.**  This interface is dormant pending a *certified* new
  certificate; it is not structurally closed.  What would have to be produced is an outer stage of
  `≥ 6.554756` (published: `6.499146`; re-optimization reaches `≈ 6.746598`; capacity ceiling
  `4 log₂ 5 = 9.287712`) together with an inner rate under the barrier cap at its own volume.
* **Depth `≥ 2` remains dead unconditionally**, by the capacity theorem
  `TotalWeightAcceptanceAssemblyLevelTwo.xWordCapacity_lt_outerBase_of_two_le_depth`.  Nothing in
  the re-optimization study touches that.
* **The separate outer-side argument against `h3` is now a theorem, and it binds the record only.**
  The residual analysis carried a second, certificate-independent argument: the
  `X`-word ceiling forces `(cleanup.survivors r).card ≤ 1`, against any exponential
  `targetGrowth`.  That is proved — `MatrixMultiplication/TotalWeightOuterCeiling.lean`,
  `AlgebraicComplexity.Examples.CWTotalWeightOuterCoarseCleanup.card_survivors_le_one` (every
  cleanup, every `r`, every depth) and
  `TotalWeightAcceptanceAssembly.isEmpty_levelTwoOuterCountInput` — so `h3` as typed is
  uninhabitable and the endpoint below is unconditionally vacuous, not merely refuted at the
  published constants.  **This does not close the flat frame.**  What it kills is the record's
  ISOLATE-AGAINST-UNRESTRICTED shape, i.e. `CWTotalWeightOuterCoarseCleanup.soundX`'s ambient being
  the *unrestricted* coarse power; a hash-first cleanup faces the post-hash `X`-word capacity
  `4 log₂ 5 = 9.287712` instead, which the numbers above clear.  Scope and revival cost:
  `better_bound/flat_route_feasibility/CONSTRUCTION_SCOPE.md`.

It is kept — not deleted — as a negative artifact for the published constants and as a regression
test for the generic composition plumbing, exactly as
`MatrixMultiplication/TotalWeightAcceptanceAssembly.lean` keeps its depth-four predecessor.  Per
the leaderboard rules it must not be cited as a record.

### The refutation at the published constants, arrow by arrow

Write `P` for `cwEmbeddedChunkProfile h1.leaf h1.embed`, `M = 152` for its mass (`h1.mass_eq`),
`C` for the total-weight coarse shape of a depth-one chunk letter and `L_c` for the ordered fine
block word on leg `c`.  Entropies `H₂` are in bits.

1. **`hrate` forces the rate floor.**  `innerRetainedFloor_le_innerRate_ofRate` below gives
   `433/250 ≤ h1.innerRate` from `hrate` alone.
2. **`h1.rate` is a bits budget on the double-coarse residual.**  Unfolding the committed
   definitions — `cwTotalWeightInnerTargetBase = exp(M(H_fine − H(C)))`
   (`WordType.pushedTypeFiberEntropyBase_eq_exp_entropyDifference`),
   `cwChunkAmbientEntropyBase = exp(M · H_fine)`,
   `cwTotalWeightConditionalLegEntropyBase … c = exp(M · H(C,L_c) − M · H(C))`
   (`WordType.conditionalProfileEntropyBase`), and
   `cwTotalWeightInnerCompetitorBase ≥ ambientBase / conditionalLegBase c`
   (`div_conditionalLegEntropyBase_le_innerCompetitorBase`, the only half needed; the `max 1`
   branch is never strict but is not load-bearing) — gives, for **every** leg `c`,
   `2 ^ (38 · h1.innerRate) < exp(152 · (H(C,L_c) − 2 H(C)))`.  With `1 < h1.slack` and step 1, and
   since `38 · (433/250) / 152 = 433/1000` exactly, this says
   `min_c (H₂(C,L_c) − 2 H₂(C)) > 433/1000`, strictly.
3. **The volume floor caps the corner mass at `9/152`.**  `h1.oneTypeLetters_ge` (`295 ≤`) with
   `h1.volume_ge` forces at least `295` of the `2 · 152 = 304` `CW₅` letters of a stride block to
   be one-type, so at most `9` positions are corner (`cw200`/`cw020`/`cw002`), so the profile mass
   carried by corner-containing chunk letters is at most `9`, i.e. probability `≤ 9/152`.  Same
   arithmetic style as `TotalWeightAcceptanceAssemblyLevelTwo.fullSupport_volumeLetters_le`.
4. **The landed barrier closes it.**
   `AlgebraicComplexity.Examples.exists_leg_depthOne_rateResidual_lt_433_div_1000`
   (kernel-checked, audited by `AxiomAudit/CoppersmithWinogradDepthOneRateBarrier.lean`, ten
   assertions): corner mass `≤ 9/152` produces **some** leg with `H₂(C,L_c) − 2 H₂(C) < 433/1000`.
   Direct contradiction with the `∀ c` of step 2.  The constant is not a coincidence: the barrier
   was calibrated to exactly this record.

### What is, and is not, kernel-checked

Step 1 and step 4 are Lean theorems.  Steps 2 and 3, and the identification of this file's coarse/
leg objects with the barrier's `cwDepthOneCoarseShape` / `cwDepthOneLegWord` over
`cwBlockSupport × cwBlockSupport`, are **verified mathematics but not Lean theorems**.  Turning the
refutation into a `False` would need exactly three connectors:

* **C1** — the identification: an equivalence
  `(cwChunkPartitionedTensor K 5 1).support ≃ cwBlockSupport × cwBlockSupport` carrying
  `coarseningSupportMap (cwTotalWeightChunkCoarsening 1)` to `cwDepthOneCoarseShape` (injectively,
  via `cwTotalWeightSupportedShape_injective`) and `s.1 c` to `cwDepthOneLegWord c`, plus
  `normalizedProfileProbability (mappedType f ·) = (normalizedProfileProbability ·).pushforward f`
  to move `profileEntropyNats` to `ProbabilityVector.entropyBits`.
* **C2** — the log-algebra of step 2.  The likely hard one, though only the `le_max` half of the
  competitor bound is needed.
* **C3** — the volume floor `→` corner mass `≤ 9/152` of step 3.

They are **deliberately unwritten**.  The project has pivoted to formalizing the paper's actual
nested/conditional-laws route; a connector on a dormant flat route is not a publishable deliverable
and does not earn its proof cost.  Note also that they would prove *`False` from the published
certificate's constants*, not a universal barrier: the connectors close the chain below, and the
chain is certificate-conditional throughout.  This section is the record so that nobody re-treads
the shortcut.

### The `ω ≈ 2.3793` figure is about the published `C′`, not about the frame

The earlier version of this note read: "the barrier's bound `4 · (H₂(β) + β)` on the level-two
stage at corner mass `β` is *attained*, so relaxing `oneTypeLetters_ge` only trades volume for rate
along a curve whose optimum, at `β ≈ 0.06995`, is `ω ≈ 2.3793`", i.e. worse than the classical
`2.375477` already in the tree, with endpoint slack at `2.36999` negative (best `≈ −0.0559`) for
every `β`.

**Attainment stands** — SLSQP over the whole 36-letter depth-one simplex reproduces the closed form
to `≈ 3·10⁻⁸` for every `β ≤ 0.22`, so codex-cw's Lean bound is tight, not conservative (above
`β ≈ 0.2271` the attained value saturates at `1` bit per chunk and the Lean form over-estimates).
**The `2.3793` conclusion does not**: that sweep holds the outer stage *fixed* at the published
`6.499146`.  With the outer stage free up to the capacity `4 log₂ 5 = 9.287712`, the barrier plus
capacity give only `ω ≥ 1.551914` (Lean closed form) / `ω ≥ 1.678633` (attained functional) — both
vacuous.  So `2.3793` is a statement about the published constants, **not** a flat-route barrier.
Re-optimized points reach `ω ≈ 2.343988` (widest space) and `ω ≈ 2.346819` (certificate's own
support) with the barrier *satisfied*; float-level and uncertified, per
`better_bound/flat_route_feasibility/VERDICT.md` §3.

Unchanged and still true at fixed published outer: at the stride-38 integer points the best is
`m = 293` one-type letters with `ω ≈ 2.3823`; the volume-maximal leaf `m = 304` has inner rate
exactly zero (`exists_leg_entropyBits_pair_sub_two_mul_coarse_le_zero_of_noCorner`).

## `h2` — the outer copy-base identity

`OuterFloorInput 1` is not a hypothesis at all: `witnessOuterFloorLevelTwo` already inhabits it in
the depth-one module, by the same definitional argument as the depth-four `witnessOuterFloor` —
once the two field bases are fixed to `0`, the copy-base equation *defines* the target base, so the
record is inhabited by construction.  This is why the obligation-fidelity review classified `h2` as
"WEAKER — base is a definition of `targetBase`".  It is simply supplied below.

Note what this does *not* do.  Inhabiting `OuterFloorInput 1` in isolation says nothing about
whether the same target base can simultaneously satisfy `h3.targetGrowth` and the finite survivor
capacity; that joint question is `h3`'s, and `h3` is untouched.  The depth-one capacity theorem
`outerBase_le_xWordCapacity_levelTwo` is the reason it is not already refuted, as it is at depth
four.

## `h4.certificate` — the level-two branch-floor certificate

`MatrixMultiplication/TotalQuotientExponentLevelTwoGroupedCertificate.lean` proves
`BranchFloorCertified certifiedTables certifiedMassThree` outright from the landed generated
payload of certificate `e7987d7f…`.  What is left of `h4` is exactly its `realizes` field: the
comparison of two real numbers

```
TotalQuotientExponentLevelTwoRecurrence.retainedExponent certifiedTables certifiedMassThree
  ≤ h1.innerRate
```

which is codex-2.36x's segmented-occurrence-family transfer.  `levelTwoTableInput_ofRate` is the
requested `LevelTwoTableInput`-minus-`realizes` constructor: it takes that bound and nothing else.

## The residual list after this module

Superseded by the STATUS section above, **with the published certificate's constants fixed**:
`h1.rate` is not open there, it is **false** on any leaf that also satisfies `h1.volume_ge` and
`h1.oneTypeLetters_ge`, and `hrate` — read against the published certificate — is one of the two
hypotheses doing the killing rather than a blocker.  **Do not attempt these residuals with the
published certificate**: nobody should instantiate `h1.maximumEntropy`, search for `h1.rate`,
construct an `OuterCountInput` at depth one, or bound `retainedExponent` from above *for it*.  A
re-optimized, certified certificate would reopen every row of this table, and none of the "moot"
verdicts survives such a certificate — see `better_bound/flat_route_feasibility/VERDICT.md`.  The
table is kept for provenance, and the statuses below are read at the published constants.

| input | statement | owner | status (published certificate) |
| --- | --- | --- | --- |
| `h1.maximumEntropy` | conditional maximum entropy of the zero-extended sparse profile | codex-2.36x | moot |
| `h1.rate` | the realized inner rate at the level-two family exponent | codex-2.36x | **refuted** |
| `hrate` (was `h4.realizes`) | `retainedExponent certifiedTables certifiedMassThree ≤ h1.innerRate` | codex-2.36x | satisfiable, and one of the two killers |
| `h3.*` | S6's residual table at `depth = 1` | S6 / codex-2.36x | moot |

`h1.volume_ge` and `h1.oneTypeLetters_ge` remain fields of `h1`, but they are discharged outright
for the maximal-volume alphabet by `levelTwoPointLeaf_volume_ge`; `h2` and `h4.certificate` are
gone.  Nothing that was open before is closed by weakening: the corollary below is the same
conclusion with strictly fewer hypotheses.
-/

namespace MatrixMultiplication.TotalWeightAcceptanceAssemblyLevelTwoEndpoint

open AlgebraicComplexity
open AlgebraicComplexity.Tensor
open MatrixMultiplication.TotalWeightAcceptanceFloors
open MatrixMultiplication.TotalWeightAcceptanceAssembly
open MatrixMultiplication.TotalWeightAcceptanceAssemblyLevelTwo

universe u

/-! ## `h4` minus `realizes` -/

/-- **`LevelTwoTableInput` minus its `realizes` field.**

The certified table pair of the total-weight candidate, packaged for any inner rate that dominates
its exact level-two bottleneck.  The `certificate` field is proved, not assumed; the rate bound is
the only argument. -/
noncomputable def levelTwoTableInput_ofRate {innerRate : ℝ}
    (hrate :
      TotalQuotientExponentLevelTwoRecurrence.retainedExponent
          TotalQuotientExponentLevelTwoGroupedProvenance.certifiedTables
          TotalQuotientExponentLevelTwoGroupedProvenance.certifiedMassThree ≤ innerRate) :
    LevelTwoTableInput innerRate where
  tables := TotalQuotientExponentLevelTwoGroupedProvenance.certifiedTables
  massThree := TotalQuotientExponentLevelTwoGroupedProvenance.certifiedMassThree
  certificate := TotalQuotientExponentLevelTwoGroupedCertificate.branchFloorCertified
  realizes := hrate

/-- The `C′` inner acceptance floor `433/250` is below the certified level-two bottleneck, so the
constructor above is never vacuous: any `innerRate` it accepts already clears the inner floor. -/
theorem innerRetainedFloor_le_innerRate_ofRate {innerRate : ℝ}
    (hrate :
      TotalQuotientExponentLevelTwoRecurrence.retainedExponent
          TotalQuotientExponentLevelTwoGroupedProvenance.certifiedTables
          TotalQuotientExponentLevelTwoGroupedProvenance.certifiedMassThree ≤ innerRate) :
    innerRetainedFloor ≤ innerRate :=
  le_trans
    TotalQuotientExponentLevelTwoGroupedCertificate.innerRetainedFloor_le_retainedExponent hrate

/-! ## The endpoint -/

set_option exponentiation.threshold 512 in
/-- **DORMANT: the depth-one (paper level-two) `2.36999` endpoint, over hypotheses that are jointly
unsatisfiable *at the published certificate's constants*.**

⚠ With `hrate` read against the *published* level-two certificate, `h1` and `hrate` cannot both
hold.  `hrate` forces `433/250 ≤ h1.innerRate`, which turns `h1.rate` into the demand that *every*
tensor leg have double-coarse rate residual above `433/1000`; but `h1.volume_ge` with
`h1.oneTypeLetters_ge` caps the corner mass at `9/152`, and
`AlgebraicComplexity.Examples.exists_leg_depthOne_rateResidual_lt_433_div_1000` then exhibits a leg
below `433/1000`.  See the module header for the chain, for the three connectors (C1–C3) that would
turn this into a kernel-checked `False`, and for why they are deliberately unwritten.

**Scope (corrected 2026-08-28).**  That refutation is certificate-conditional.  The constraint
*system* is satisfiable by re-optimized certificates: a re-optimized outer stage of `≈ 6.746598`
(needed `≥ 6.554756`, published `6.499146`, capacity `9.287712`) satisfies the depth-one rate
barrier with positive endpoint slack — float-level, unconverged, **uncertified**, per
`better_bound/flat_route_feasibility/VERDICT.md`.  So this endpoint is **dormant pending a
certified new certificate, not structurally dead**.  Depth `≥ 2` is dead unconditionally by
capacity (`xWordCapacity_lt_outerBase_of_two_le_depth`).

**Do not cite this theorem as a record, and do not attempt these residuals with the published
certificate.**  It is retained as a negative artifact for those constants and as a regression test
for the generic composition plumbing.

Historically: same conclusion as `omega_lt_236999_of_named_inputs_levelTwo`, with the outer
copy-base record supplied by `witnessOuterFloorLevelTwo` and the level-two branch-floor certificate
supplied by `TotalQuotientExponentLevelTwoGroupedCertificate.branchFloorCertified`.  What was left was
exactly the codex-2.36x-owned items: the sparse inner leaf `h1` (its maximum-entropy and rate
fields), S6's outer count table `h3`, and the single numeric transfer `hrate`. -/
theorem omega_lt_236999_of_inner_inputs
    (K : Type u) [Field K]
    {letters : Type} [Fintype letters] [Nonempty letters]
    {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]
    {Part : Type} [Fintype Part]
    (h1 : LevelTwoSparseInnerInput K letters dims)
    (h3 : OuterCountInput K 5 1 levelTwoOuterExponent Part witnessOuterFloorLevelTwo
      (levelTwoCoarseReference h1))
    (hrate :
      TotalQuotientExponentLevelTwoRecurrence.retainedExponent
          TotalQuotientExponentLevelTwoGroupedProvenance.certifiedTables
          TotalQuotientExponentLevelTwoGroupedProvenance.certifiedMassThree ≤ h1.innerRate) :
    omega K < acceptanceTarget :=
  omega_lt_236999_of_named_inputs_levelTwo K h1 witnessOuterFloorLevelTwo h3
    (levelTwoTableInput_ofRate hrate)

end MatrixMultiplication.TotalWeightAcceptanceAssemblyLevelTwoEndpoint
