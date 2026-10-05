import AlgebraicComplexity.Examples.CoppersmithWinograd
import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeEndpointValue
import AlgebraicComplexity.MatrixMultiplication.LaserVolume
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolume
import AlgebraicComplexity.Probability.ParentConsistency
import MatrixMultiplication.FeasibilitySlack
import MatrixMultiplication.LogBounds
import MatrixMultiplication.ParentGainCertificate

/-!
# Proof obligations for the Total-Weight bound

This module records the exact trust boundary between the proved reusable library and the
certificate-specific work needed for the Total-Weight construction.  The canonical certificate
has SHA-256 `90dfb5ea1f9560845093afcf88dc12d11af836d3b34983886f0e915729bbfb8d` and contains
225 active rows.  Its current target is the exact rational `2365815 / 10^6`.

The recursive counting source is [alman2025more], Claim 6.18
(`papers/sources/2404.16349/constituent.tex:376-440`).  The manuscript states the remaining
quotient-count hypothesis at `better_bound/paper.tex:1729-1761`, the canonical rational endpoint
at `better_bound/paper.tex:2195-2212`, and its Lean-facing proof boundary at
`better_bound/paper.tex:2240-2254`.  All three locations use the same `90dfb5ea...` certificate and
target recorded here.

Four concrete tasks remain on the canonical route:

1. reconstruct the frozen primary tables, rows, directed numerical floors, and recurrences;
2. identify every frozen row with its actual ordered Total-Weight competitor and typed leaf;
3. construct the finite whole-fiber hashing, compatibility cleanup, and repair degeneration; and
4. package those stages into a subexponential extraction sequence with the certified rates.

The final theorem below consumes the mathematical outputs of those tasks directly: an actual
`WholeConstituentLaserVolumeSequenceData`, positive volume, and the certified combined endpoint
inequality.  It does not accept an assumed aggregate tensor restriction.  This combined interface
matches `better_bound/PAIRED_TOTAL_WEIGHT_FORMALIZATION_PLAN.md`: the external checker proves the
new regional row floors, but labels the unchanged-stage and volume floors as inputs whose
recurrence semantics still require separate Lean proofs.  The componentwise constants below are
therefore arithmetic waypoints, not assumptions made by the endpoint.

The older `Counted` boundary and its parent-consistency and two-letter adapters are retained below
for source compatibility with archived experiments.  They are not proof obligations for the
Total-Weight theorem.  In particular, the canonical route uses neither correction and requires
only the certificate's fixed `XZY` orientation, not an arbitrary-orientation strengthening.

The archived abstract predicate `Counted E M` means that a concrete global and recursive
constituent family has retained exponent `E` and rectangular-volume exponent `M`, before cleanup
is converted into a genuine direct sum.  Its legacy endpoint consumes four hypotheses:

1. `ConcreteGlobalConstituentTypeCounting Counted E M`;
2. `CompatibilityZeroingAndHoleRepair K Counted`;
3. `CertifiedParentConsistencyInstantiation Counted E gain M`;
4. `ExactLevelFourReconstruction E M`.

Schönhage's asymptotic sum inequality is not an obligation: it enters through
`HasLaserExtractionRate.le_log_borderRank` and is already proved in the reusable library.

## Where the endpoint arithmetic lives

None of the `omega_lt_*` theorems below contains a solve-for-`omega` step.  The three that consume
the abstract `Counted` adapter reach `omega` along the rate route and finish with the shared
ordered-field bridge `FeasibilitySlack.strict_of_feasibility_with_slack`
(`MatrixMultiplication/FeasibilitySlack.lean`), which is where the private restatement this module
used to carry now lives.  The fully concrete `omega_lt_236999_of_subexponentialVolumeSequence` goes
one step further and is a single application of the regularization bridge's client idiom
`Examples.omega_lt_of_cwPower_borderRankBudget`
(`AlgebraicComplexity/MatrixMultiplication/LaserVolumeRegularization.lean`), so the sequence
plumbing, the `τ = target/3` normalization and Schönhage soundness are all upstream of this file.
What remains here is exactly the rational margin arithmetic against the four decimal targets.

The archived correlated two-letter endpoint consumes one additional, separately named adapter:
`CertifiedTwoLetterInstantiation`.  This proposition states exactly the fixed-interface local
gain that must be connected to the twenty rational transportation tables; it does not hide an
unproved theorem or enter the reusable probability layer.
-/

namespace MatrixMultiplication.CurrentProofObligations

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor

universe u

/-! ## Canonical Total-Weight endpoint -/

/-- Exact rational target represented by the decimal `2.365815`. -/
noncomputable def totalWeightOmegaTarget : ℝ := 2365815 / 1000000

/-- Directed retained-exponent floor reconstructed from the 90df certificate. -/
noncomputable def totalWeightRetainedFloor : ℝ :=
  8241241067995057 / 1000000000000000

/-- Directed mean rectangular-volume floor reconstructed from the 90df certificate. -/
noncomputable def totalWeightVolumeFloor : ℝ := 3756 / 625

/-- The canonical Total-Weight target is positive. -/
theorem totalWeightOmegaTarget_pos : 0 < totalWeightOmegaTarget := by
  norm_num [totalWeightOmegaTarget]

/-- The reconstructed mean-volume floor is positive. -/
theorem totalWeightVolumeFloor_pos : 0 < totalWeightVolumeFloor := by
  norm_num [totalWeightVolumeFloor]

/-- Exact endpoint arithmetic for the replacement certificate.

The rational margin over the directed source-rank upper endpoint is
`3515534217 / 10^15`.  This theorem checks only that final arithmetic; it does not reconstruct
the certificate or assert the existence of a tensor extraction. -/
theorem certified_totalWeight_endpoint_slack :
    LogBounds.rankBudgetUpper <
      totalWeightRetainedFloor + totalWeightOmegaTarget * totalWeightVolumeFloor := by
  norm_num [LogBounds.rankBudgetUpper, totalWeightRetainedFloor,
    totalWeightOmegaTarget, totalWeightVolumeFloor]

/-- Certificate-specific numerical boundary for the canonical Total-Weight construction.

A proof must derive the combined inequality from the same 90df finite construction used to build
the extraction sequence.  The positivity conjunct is needed by the strict endpoint bridge.
Merely checking the scalar arithmetic, or importing componentwise floors from an older
certificate, does not establish this proposition. -/
def TotalWeightCertificateReconstruction (retained volume : ℝ) : Prop :=
  0 < volume ∧
    LogBounds.rankBudgetUpper < retained + totalWeightOmegaTarget * volume

/-- Directed retained and volume floors imply the combined certificate boundary.

This is the monotone transport used after the two semantic recurrence bounds in
`better_bound/paper.tex:2171-2212`; it introduces no additional numerical assumption. -/
theorem totalWeightCertificateReconstruction_of_floor_bounds
    {retained volume : ℝ}
    (hretained : totalWeightRetainedFloor ≤ retained)
    (hvolume : totalWeightVolumeFloor ≤ volume) :
    TotalWeightCertificateReconstruction retained volume := by
  refine ⟨totalWeightVolumeFloor_pos.trans_le hvolume, ?_⟩
  exact certified_totalWeight_endpoint_slack.trans_le
    (add_le_add hretained
      (mul_le_mul_of_nonneg_left hvolume totalWeightOmegaTarget_pos.le))

/-- Exact rational target represented by the decimal `2.369661`. -/
noncomputable def omegaTarget : ℝ := 2369661 / 1000000

/-- Volume-only milestone target represented by the decimal `2.36999`.

This deliberately leaves out parent consistency and correlated two-letter extraction.  Its much
larger rational margin makes it the shortest route to closing a conditional endpoint once the
certificate-faithful extraction sequence is supplied; the definition itself does not assert that
the sequence or its paper-specific counting proof has already been constructed. -/
noncomputable def volumeOnlyOmegaTarget : ℝ := 236999 / 100000

/-- Exact rational target represented by the decimal `2.36965963`. -/
noncomputable def twoLetterOmegaTarget : ℝ := 236965963 / 100000000

/-- Certified lower endpoint for the volume-only retained exponent. -/
def baseRetainedLower : ℝ := 8.200979373915867

/-- Coarse retained-exponent floor sufficient for the `2.36999` milestone.  Using four decimal
digits substantially simplifies the eventual interval checker. -/
def volumeOnlyRetainedLower : ℝ := 8.2

/-- Certified lower endpoint for the one-sweep parent-consistency gain. -/
noncomputable def parentGainLower : ℝ := ParentGainCertificate.certifiedGainFloor

/-- Exact weighted sum of the twenty directed local two-letter gain floors. -/
noncomputable def twoLetterGainLower : ℝ :=
  85297556531647594849 / 46116860184273879040000000

/-- Certified lower endpoint for the rectangular-volume exponent. -/
def volumeLower : ℝ := 6.016830849632222

/-- Coarse rectangular-volume floor sufficient for the `2.36999` milestone. -/
def volumeOnlyVolumeLower : ℝ := 6.0165

/-- Source rank budget for the eighth power of `CW_5`, measured in bits. -/
noncomputable def sourceRankBudget : ℝ := 8 * (Real.log 7 / Real.log 2)

/-- The numerical endpoints have positive matrix volume. -/
theorem volumeLower_pos : 0 < volumeLower := by
  norm_num [volumeLower]

/-- The coarse volume-only matrix exponent is positive. -/
theorem volumeOnlyVolumeLower_pos : 0 < volumeOnlyVolumeLower := by
  norm_num [volumeOnlyVolumeLower]

/-- The target exponent is positive. -/
theorem omegaTarget_pos : 0 < omegaTarget := by
  norm_num [omegaTarget]

/-- The volume-only milestone target is positive. -/
theorem volumeOnlyOmegaTarget_pos : 0 < volumeOnlyOmegaTarget := by
  norm_num [volumeOnlyOmegaTarget]

/-- The correlated two-letter target exponent is positive. -/
theorem twoLetterOmegaTarget_pos : 0 < twoLetterOmegaTarget := by
  norm_num [twoLetterOmegaTarget]

/-- Pure rational arithmetic for the final parent-corrected margin.  The exact gap over the
printed rank-budget upper endpoint is
`3202712683908371 / 500000000000000000000`.-/
theorem certified_endpoint_slack :
    LogBounds.rankBudgetUpper <
      baseRetainedLower + parentGainLower + omegaTarget * volumeLower := by
  norm_num [LogBounds.rankBudgetUpper, baseRetainedLower, parentGainLower,
    ParentGainCertificate.certifiedGainFloor, omegaTarget, volumeLower]

/-- Pure rational arithmetic for the volume-only milestone.  No parent-consistency or two-letter
gain enters this inequality.  The exact gap over the printed rank-budget upper endpoint is
`5136463479 / 25000000000000`. -/
theorem certified_volumeOnly_endpoint_slack :
    LogBounds.rankBudgetUpper <
      volumeOnlyRetainedLower + volumeOnlyOmegaTarget * volumeOnlyVolumeLower := by
  norm_num [LogBounds.rankBudgetUpper, volumeOnlyRetainedLower,
    volumeOnlyOmegaTarget, volumeOnlyVolumeLower]

/-- Pure rational arithmetic for the endpoint containing both conservative corrections. -/
theorem certified_twoLetter_endpoint_slack :
    LogBounds.rankBudgetUpper <
      baseRetainedLower + parentGainLower + twoLetterGainLower +
        twoLetterOmegaTarget * volumeLower := by
  norm_num [LogBounds.rankBudgetUpper, baseRetainedLower, parentGainLower,
    ParentGainCertificate.certifiedGainFloor, twoLetterGainLower,
    twoLetterOmegaTarget, volumeLower]

/-- The proved logarithm enclosure puts the exact source budget below the rational endpoint used
by `certified_endpoint_slack`. -/
theorem sourceRankBudget_lt_upper :
    sourceRankBudget < LogBounds.rankBudgetUpper := by
  exact LogBounds.eight_logTwo_seven_lt_rankBudgetUpper

/-- Semantic endpoint of compatibility zeroing and hole repair: the eighth power of `CW_5`
achieves the corrected count-and-volume rate as actual finite direct-sum degenerations. -/
def CurrentLaserExtraction (K : Type u) [Field K] (retained volume : ℝ) : Prop :=
  HasLaserExtractionRate K (Tensor.power (coppersmithWinograd K 5) 8)
    (Real.log 2 * (retained + omega K * volume))

/-- A concrete finite extraction sequence with subexponential counting/repair loss supplies the
semantic current-paper extraction.  This is the preferred endpoint for the paper-specific
hashing, compatibility cleanup, leaf assembly, and hole-repair development: unlike the older
`Counted` adapter below, every field of the sequence is finite data or a proved finite tensor
degeneration. -/
theorem CurrentLaserExtraction.of_subexponentialVolumeSequence
    (K : Type u) [Field K] {stride : ℕ} {retained volume : ℝ}
    (h : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume))) :
    CurrentLaserExtraction K retained volume := by
  exact h.hasLaserExtractionRate_bits

/-- The paper's concrete global and recursive constituent type-counting theorem, at the adapter
boundary before compatibility cleanup.  A future certificate schema supplies the meaning of
`Counted`; proving this proposition means constructing the paper's actual counted family. -/
def ConcreteGlobalConstituentTypeCounting
    (Counted : ℝ → ℝ → Prop) (retained volume : ℝ) : Prop :=
  Counted retained volume

/-- Compatibility zeroing and hole repair must turn every concrete counted family into the
semantic laser extraction consumed by Schönhage's inequality.  This statement includes the
legwise-independence and unbroken-interface conclusions, not just the validity of individual
zero-out maps. -/
def CompatibilityZeroingAndHoleRepair
    (K : Type u) [Field K] (Counted : ℝ → ℝ → Prop) : Prop :=
  ∀ retained volume, Counted retained volume → CurrentLaserExtraction K retained volume

/-- Instantiation of the proved parent-consistency theorem on every relevant node of the concrete
level-4 certificate, followed by active-branch rebalancing.  The reusable local inequality is
`CompatibilityPoolingModel.conditionalEntropyBits_le_sub_prescribedParentQuadratic`; this remaining
paper-layer proposition records only its certificate-specific hypotheses, aggregation, and the
directed numerical gain. -/
def CertifiedParentConsistencyInstantiation
    (Counted : ℝ → ℝ → Prop) (retained gain volume : ℝ) : Prop :=
  ∃ certificate : ParentGainCertificate.Data,
    certificate.certifiedGain ≤ gain ∧
      (Counted retained volume → Counted (retained + gain) volume)

/-- Certificate-specific instantiation of correlated two-letter fixed-interface extraction.
The reusable probability theorem supplies exact coupling marginals, deterministic-interface
pushforwards, maximum-entropy tensorization, and the independent-product no-regression result.
This adapter additionally identifies the product partition and twenty exact rational couplings
with the concrete active level-3 nodes, proves that the parent-symbol mutual-information costs fit
inside the two compatibility-branch slacks, and records their directed aggregate gain. -/
def CertifiedTwoLetterInstantiation
    (Counted : ℝ → ℝ → Prop) (retained gain volume : ℝ) : Prop :=
  twoLetterGainLower ≤ gain ∧
    (Counted retained volume → Counted (retained + gain) volume)

/-- Exact reconstruction of the dyadic level-4 certificate must establish these directed
enclosures for the exact recurrence outputs.  The certificate currently carrying these values has
SHA-256 `7a255f50ab903cb7f3da56d93ceccfff3acf39061463115655d7f3f63e746481`.
The definition deliberately states only the semantic enclosure consumed by the proof; an
executable NPZ decoder and recurrence evaluator must prove it for the concrete data. -/
def ExactLevelFourReconstruction (retained volume : ℝ) : Prop :=
  baseRetainedLower ≤ retained ∧ volumeLower ≤ volume

/-- Coarse reconstruction interface used by the shortest `2.36999` proof.  It asks the exact
certificate evaluator for only four decimal digits of each lower bound. -/
def VolumeOnlyLevelFourReconstruction (retained volume : ℝ) : Prop :=
  volumeOnlyRetainedLower ≤ retained ∧ volumeOnlyVolumeLower ≤ volume

/-- The tighter reconstruction already used by the experimental endpoints implies the coarse
volume-only interface. -/
theorem ExactLevelFourReconstruction.toVolumeOnly
    {retained volume : ℝ} (h : ExactLevelFourReconstruction retained volume) :
    VolumeOnlyLevelFourReconstruction retained volume := by
  rcases h with ⟨hretained, hvolume⟩
  constructor
  · exact (by norm_num [volumeOnlyRetainedLower, baseRetainedLower] :
      volumeOnlyRetainedLower ≤ baseRetainedLower).trans hretained
  · exact (by norm_num [volumeOnlyVolumeLower, volumeLower] :
      volumeOnlyVolumeLower ≤ volumeLower).trans hvolume

/-- The explicit `CW_5` border-rank certificate bounds the logarithmic border rank of its eighth
power by `8 * log 7`. -/
theorem log_borderRank_currentSource_le (K : Type u) [Field K] :
    Real.log (borderRank (Tensor.power (coppersmithWinograd K 5) 8)) ≤
      8 * Real.log 7 := by
  have hborder :
      borderRank (Tensor.power (coppersmithWinograd K 5) 8) ≤ 7 ^ 8 := by
    exact borderRank_le_iff.mpr ((coppersmithWinograd_borderRankLE K 5).power 8)
  have hlog :
      Real.log (borderRank (Tensor.power (coppersmithWinograd K 5) 8)) ≤
        Real.log ((7 : ℕ) ^ 8) := by
    by_cases hzero : borderRank (Tensor.power (coppersmithWinograd K 5) 8) = 0
    · rw [hzero]
      simpa using Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 7)
    · apply Real.log_le_log
      · exact_mod_cast Nat.pos_of_ne_zero hzero
      · exact_mod_cast hborder
  simpa [Real.log_pow] using hlog

/-- Schönhage's proved asymptotic sum inequality converts a completed current-paper extraction
into its scalar feasibility inequality. -/
theorem retained_add_omega_mul_volume_le_sourceRankBudget
    (K : Type u) [Field K] {retained volume : ℝ}
    (hextract : CurrentLaserExtraction K retained volume) :
    retained + omega K * volume ≤ sourceRankBudget := by
  have hrate := hextract.le_log_borderRank K
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsource := log_borderRank_currentSource_le K
  have hscaled :
      Real.log 2 * (retained + omega K * volume) ≤ 8 * Real.log 7 :=
    hrate.trans hsource
  rw [sourceRankBudget]
  calc
    retained + omega K * volume ≤ (8 * Real.log 7) / Real.log 2 := by
      apply (le_div_iff₀ hlogTwo).2
      simpa [mul_comm] using hscaled
    _ = 8 * (Real.log 7 / Real.log 2) := by ring

/-- Feasibility form used by the final decimal argument. -/
theorem omega_le_of_currentLaserExtraction
    (K : Type u) [Field K] {retained volume Ω : ℝ}
    (hvolume : 0 < volume)
    (hextract : CurrentLaserExtraction K retained volume)
    (hbudget : sourceRankBudget ≤ retained + Ω * volume) :
    omega K ≤ Ω := by
  have hsource := retained_add_omega_mul_volume_le_sourceRankBudget K hextract
  nlinarith

/-- Canonical Total-Weight endpoint from an actual subexponential extraction sequence and the
90df certificate's directed combined endpoint inequality.

All tensor semantics are carried by `hextractions`; all certificate-specific numerical semantics
are carried by `hreconstruct`.  The remaining proof is the already-proved CW border-rank bound,
Schönhage soundness, and exact rational endpoint arithmetic. -/
theorem omega_lt_2365815_of_subexponentialVolumeSequence
    (K : Type u) [Field K]
    {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hreconstruct : TotalWeightCertificateReconstruction retained volume) :
    omega K < totalWeightOmegaTarget := by
  rcases hreconstruct with ⟨hvolumePos, hcombined⟩
  have hextract : CurrentLaserExtraction K retained volume :=
    CurrentLaserExtraction.of_subexponentialVolumeSequence K hextractions
  have hslack :
      sourceRankBudget < retained + totalWeightOmegaTarget * volume :=
    sourceRankBudget_lt_upper.trans hcombined
  apply FeasibilitySlack.strict_of_feasibility_with_slack hvolumePos hslack
  intro Ω hbudget
  exact omega_le_of_currentLaserExtraction K hvolumePos hextract hbudget

/-- Canonical endpoint from the no-hidden-restriction whole-constituent sequence interface. -/
theorem omega_lt_2365815_of_wholeConstituentSequenceData
    (K : Type u) [Field K]
    {stride : ℕ} {retained volume : ℝ}
    (data : WholeConstituentLaserVolumeSequenceData K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hreconstruct : TotalWeightCertificateReconstruction retained volume) :
    omega K < totalWeightOmegaTarget :=
  omega_lt_2365815_of_subexponentialVolumeSequence K
    data.toSubexponentialLaserVolumeSequence hreconstruct

/-- Archived conditional endpoint with every legacy paper-specific result exposed as a named
hypothesis.  No hypothesis is required for Schönhage's asymptotic sum inequality.

This theorem is retained for source compatibility and is not part of the canonical Total-Weight
proof route. -/
theorem omega_lt_2369661_of_proof_obligations
    (K : Type u) [Field K]
    (Counted : ℝ → ℝ → Prop)
    {retained gain volume : ℝ}
    (htypes : ConcreteGlobalConstituentTypeCounting Counted retained volume)
    (hcleanup : CompatibilityZeroingAndHoleRepair K Counted)
    (hparent : CertifiedParentConsistencyInstantiation Counted retained gain volume)
    (hreconstruct : ExactLevelFourReconstruction retained volume) :
    omega K < omegaTarget := by
  rcases hparent with ⟨parentCertificate, hgainCertificate, hcorrect⟩
  have hgain : parentGainLower ≤ gain :=
    (ParentGainCertificate.certifiedGainFloor_le parentCertificate).trans hgainCertificate
  rcases hreconstruct with ⟨hretained, hvolume⟩
  have hvolumePos : 0 < volume := volumeLower_pos.trans_le hvolume
  have hextract : CurrentLaserExtraction K (retained + gain) volume :=
    hcleanup (retained + gain) volume (hcorrect htypes)
  have hnumericLower :
      baseRetainedLower + parentGainLower + omegaTarget * volumeLower ≤
        (retained + gain) + omegaTarget * volume := by
    have htargetNonneg : 0 ≤ omegaTarget := omegaTarget_pos.le
    have hvolumeTerm := mul_le_mul_of_nonneg_left hvolume htargetNonneg
    nlinarith
  have hslack :
      sourceRankBudget < (retained + gain) + omegaTarget * volume :=
    (sourceRankBudget_lt_upper.trans certified_endpoint_slack).trans_le hnumericLower
  apply FeasibilitySlack.strict_of_feasibility_with_slack hvolumePos hslack
  intro Ω hbudget
  exact omega_le_of_currentLaserExtraction K hvolumePos hextract hbudget

/-- Volume-only conditional endpoint.  Compared with the sharper experimental endpoints, this
statement removes both correction adapters: only the concrete one-letter type family, its legal
compatibility cleanup, and exact reconstruction of the retained/volume lower bounds remain.

Discharging these three hypotheses gives the shortest current kernel-checked route to
`omega K < 2.36999`.  The hypotheses are intentionally an adapter boundary: they are not yet
the certificate-specific ordinary fine-profile counting and recursive extraction proof, and this
theorem must not be cited as an unconditional bound until that proof is provided.  In particular,
this milestone uses neither the total-weight quotient nor the sorted-pair quotient studied by the
stronger conditional extensions. -/
theorem omega_lt_236999_of_volumeOnly_proof_obligations
    (K : Type u) [Field K]
    (Counted : ℝ → ℝ → Prop)
    {retained volume : ℝ}
    (htypes : ConcreteGlobalConstituentTypeCounting Counted retained volume)
    (hcleanup : CompatibilityZeroingAndHoleRepair K Counted)
    (hreconstruct : VolumeOnlyLevelFourReconstruction retained volume) :
    omega K < volumeOnlyOmegaTarget := by
  rcases hreconstruct with ⟨hretained, hvolume⟩
  have hvolumePos : 0 < volume := volumeOnlyVolumeLower_pos.trans_le hvolume
  have hextract : CurrentLaserExtraction K retained volume :=
    hcleanup retained volume htypes
  have hnumericLower :
      volumeOnlyRetainedLower + volumeOnlyOmegaTarget * volumeOnlyVolumeLower ≤
        retained + volumeOnlyOmegaTarget * volume := by
    have htargetNonneg : 0 ≤ volumeOnlyOmegaTarget := volumeOnlyOmegaTarget_pos.le
    have hvolumeTerm := mul_le_mul_of_nonneg_left hvolume htargetNonneg
    linarith
  have hslack :
      sourceRankBudget < retained + volumeOnlyOmegaTarget * volume :=
    (sourceRankBudget_lt_upper.trans certified_volumeOnly_endpoint_slack).trans_le
      hnumericLower
  apply FeasibilitySlack.strict_of_feasibility_with_slack hvolumePos hslack
  intro Ω hbudget
  exact omega_le_of_currentLaserExtraction K hvolumePos hextract hbudget

/-- Short concrete endpoint for the volume-only result.

Once the paper-specific finite construction is packaged as a
`SubexponentialLaserVolumeSequence`, no abstract counted-family or cleanup proposition remains:
the sequence itself contains every finite degeneration, its exact rectangular volumes, and its
certified subexponential loss.  The only other input is the exact reconstruction of the two
numerical exponents from the level-4 tables.

Since the B2 regularization bridge landed, the whole tensor-side argument is one application of
`Examples.omega_lt_of_cwPower_borderRankBudget` at `q = 5`, `power = 8`; what is left in this file
is rational — read the source budget `sourceRankBudget = 8·log₂ 7` in the bit coordinates the
bridge expects and raise the two coarse floors to the hypothesized exponents. -/
theorem omega_lt_236999_of_subexponentialVolumeSequence
    (K : Type u) [Field K]
    {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hreconstruct : VolumeOnlyLevelFourReconstruction retained volume) :
    omega K < volumeOnlyOmegaTarget := by
  obtain ⟨hretained, hvolume⟩ := hreconstruct
  refine omega_lt_of_cwPower_borderRankBudget K 5 8 volumeOnlyOmegaTarget_pos.le
    hextractions ?_
  have hbudget :
      ((8 : ℕ) : ℝ) * Real.log (((5 : ℕ) : ℝ) + 2) / Real.log 2 = sourceRankBudget := by
    rw [sourceRankBudget, show (((5 : ℕ) : ℝ) + 2) = 7 by norm_num]
    push_cast
    ring
  have hnumericLower :
      volumeOnlyRetainedLower + volumeOnlyOmegaTarget * volumeOnlyVolumeLower ≤
        retained + volumeOnlyOmegaTarget * volume := by
    have hvolumeTerm := mul_le_mul_of_nonneg_left hvolume volumeOnlyOmegaTarget_pos.le
    linarith
  exact hbudget.trans_lt
    ((sourceRankBudget_lt_upper.trans certified_volumeOnly_endpoint_slack).trans_le
      hnumericLower)

/-- Conditional end-to-end theorem for the parent-consistent and correlated two-letter endpoint.
Every non-generic step is visible in the five hypotheses; Schönhage's inequality and the source
border-rank bound are proved library theorems. -/
theorem omega_lt_236965963_of_proof_obligations
    (K : Type u) [Field K]
    (Counted : ℝ → ℝ → Prop)
    {retained parentGain pairedGain volume : ℝ}
    (htypes : ConcreteGlobalConstituentTypeCounting Counted retained volume)
    (hcleanup : CompatibilityZeroingAndHoleRepair K Counted)
    (hparent : CertifiedParentConsistencyInstantiation
      Counted retained parentGain volume)
    (htwoLetter : CertifiedTwoLetterInstantiation
      Counted (retained + parentGain) pairedGain volume)
    (hreconstruct : ExactLevelFourReconstruction retained volume) :
    omega K < twoLetterOmegaTarget := by
  rcases hparent with ⟨parentCertificate, hparentCertificate, hparentCorrect⟩
  have hparentGain : parentGainLower ≤ parentGain :=
    (ParentGainCertificate.certifiedGainFloor_le parentCertificate).trans
      hparentCertificate
  rcases htwoLetter with ⟨hpairedGain, hpairedCorrect⟩
  rcases hreconstruct with ⟨hretained, hvolume⟩
  have hvolumePos : 0 < volume := volumeLower_pos.trans_le hvolume
  have hextract :
      CurrentLaserExtraction K ((retained + parentGain) + pairedGain) volume :=
    hcleanup ((retained + parentGain) + pairedGain) volume
      (hpairedCorrect (hparentCorrect htypes))
  have hnumericLower :
      baseRetainedLower + parentGainLower + twoLetterGainLower +
          twoLetterOmegaTarget * volumeLower ≤
        ((retained + parentGain) + pairedGain) +
          twoLetterOmegaTarget * volume := by
    have htargetNonneg : 0 ≤ twoLetterOmegaTarget := twoLetterOmegaTarget_pos.le
    have hvolumeTerm := mul_le_mul_of_nonneg_left hvolume htargetNonneg
    nlinarith
  have hslack :
      sourceRankBudget < ((retained + parentGain) + pairedGain) +
        twoLetterOmegaTarget * volume :=
    (sourceRankBudget_lt_upper.trans certified_twoLetter_endpoint_slack).trans_le
      hnumericLower
  apply FeasibilitySlack.strict_of_feasibility_with_slack hvolumePos hslack
  intro Ω hbudget
  exact omega_le_of_currentLaserExtraction K hvolumePos hextract hbudget

theorem omegaTarget_eq_decimal : omegaTarget = 2.369661 := by
  norm_num [omegaTarget]

/-- Decimal rendering of the volume-only milestone target. -/
theorem volumeOnlyOmegaTarget_eq_decimal : volumeOnlyOmegaTarget = 2.36999 := by
  norm_num [volumeOnlyOmegaTarget]

theorem twoLetterOmegaTarget_eq_decimal : twoLetterOmegaTarget = 2.36965963 := by
  norm_num [twoLetterOmegaTarget]

end MatrixMultiplication.CurrentProofObligations
