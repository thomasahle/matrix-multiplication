/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.MaximumEntropyDualShift
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoTripleEntropyBound
import MatrixMultiplication.IntegerEntropyDual

set_option autoImplicit false

/-!
# Integer factors for the DWZ global maximum-entropy certificate

This certificate-layer client connects the positive integer-factor format to the committed
fifteen-state Gibbs witness for [duan2023faster], arXiv:2210.10173. The paper's fixed-marginal
maximum is the convex-program step in `second_power.tex:548-555` and
`global_value.tex:315-322`, used in `global_value.tex:292-303`; the literal global distribution is
Table 2, `global_value.tex:350-375`. The existing `DuanWuZhouLevelTwoTripleEntropyBound` proves
the corresponding Gibbs gap. This module changes its representation, not its mathematical bound.

Each coordinate factor is multiplied by `10^6`. Its logarithmic score therefore acquires the
constant `3 * log (10^6)`, which the shared constant-score cancellation theorem removes against
the unit-mass reference law. The resulting integer dual gap is exactly the committed
`dwz63GibbsDeficit / log 2`. Applying the existing integer-dual theorem and deficit certificate
recovers the same hash-loss budget without claiming that the witness is an optimizer.

The reference is the complete global law `dwz63Alpha / 10^8` on `Fin 15`, not the three-letter
022 split profile. All fifteen legal states remain in the partition. The Z factors are indexed
by physical Z, in the order of `dwz63GibbsZ`, not by the order of terms in the old partition sum.
No equality of finite logarithm-enclosure widths, finite-atom sign adapter, extraction theorem,
complete producing-rule checker, or new matrix-multiplication bound is asserted here.
-/

open scoped BigOperators

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity
open MatrixMultiplication.IntegerEntropyDual

noncomputable section

/-- The committed Gibbs X factors after clearing their common denominator `10^6`. -/
def dwz63IntegerGibbsX : Fin 5 → ℕ
  | 0 => 41762
  | 1 => 101843
  | 2 => 128169
  | 3 => 20099
  | 4 => 968

/-- The committed Gibbs Y factors after clearing their common denominator `10^6`. -/
def dwz63IntegerGibbsY : Fin 5 → ℕ
  | 0 => 542361
  | 1 => 1322632
  | 2 => 1664528
  | 3 => 261024
  | 4 => 12576

/-- The committed Gibbs factors indexed by physical Z, with denominator `10^6` cleared. -/
def dwz63IntegerGibbsZ : Fin 5 → ℕ
  | 0 => 470879
  | 1 => 1223123
  | 2 => 1491349
  | 3 => 219270
  | 4 => 9210

/-- Every coordinate factor in the three integer vectors is strictly positive. -/
theorem dwz63_integerGibbs_pos :
    (∀ x, 0 < dwz63IntegerGibbsX x) ∧
      (∀ y, 0 < dwz63IntegerGibbsY y) ∧ (∀ z, 0 < dwz63IntegerGibbsZ z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> norm_num [dwz63IntegerGibbsX]
  · intro y
    fin_cases y <;> norm_num [dwz63IntegerGibbsY]
  · intro z
    fin_cases z <;> norm_num [dwz63IntegerGibbsZ]

/-- Each integer vector is exactly `10^6` times its committed positive real Gibbs vector. -/
theorem dwz63_integerGibbs_scale :
    (∀ x, (dwz63IntegerGibbsX x : ℝ) = 1000000 * dwz63GibbsX x) ∧
      (∀ y, (dwz63IntegerGibbsY y : ℝ) = 1000000 * dwz63GibbsY y) ∧
      (∀ z, (dwz63IntegerGibbsZ z : ℝ) = 1000000 * dwz63GibbsZ z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> norm_num [dwz63IntegerGibbsX, dwz63GibbsX]
  · intro y
    fin_cases y <;> norm_num [dwz63IntegerGibbsY, dwz63GibbsY]
  · intro z
    fin_cases z <;> norm_num [dwz63IntegerGibbsZ, dwz63GibbsZ]

/-- The integer-factor natural-log score differs from the old score by one common constant.

Proof sketch: each of the three positive factors was multiplied by `10^6`; expand the three
product logarithms and collect the added logarithms without changing any coordinate map. -/
theorem dwz63_integerGibbs_score_eq (c : Fin 15) :
    MaximumEntropyDual.coordinateScore dwz63XIndex dwz63YIndex dwz63ZIndex
        (fun x => Real.log (dwz63IntegerGibbsX x : ℝ))
        (fun y => Real.log (dwz63IntegerGibbsY y : ℝ))
        (fun z => Real.log (dwz63IntegerGibbsZ z : ℝ)) c =
      dwz63GibbsScore c + 3 * Real.log (1000000 : ℝ) := by
  rw [MaximumEntropyDual.coordinateScore, dwz63_integerGibbs_scale.1,
    dwz63_integerGibbs_scale.2.1, dwz63_integerGibbs_scale.2.2]
  rw [Real.log_mul (by norm_num : (1000000 : ℝ) ≠ 0) (dwz63GibbsX_pos _).ne',
    Real.log_mul (by norm_num : (1000000 : ℝ) ≠ 0) (dwz63GibbsY_pos _).ne',
    Real.log_mul (by norm_num : (1000000 : ℝ) ≠ 0) (dwz63GibbsZ_pos _).ne']
  unfold dwz63GibbsScore MaximumEntropyDual.coordinateScore
  ring

/-- The literal global fifteen-state law has nonnegative entries and total mass one. -/
theorem dwz63_globalAlpha_isProbability :
    MaximumEntropyDual.IsProbability
      (fun c : Fin 15 => (dwz63Alpha c : ℝ) / 100000000) := by
  constructor
  · intro c
    positivity
  · rw [← Finset.sum_div]
    have hmass : ∑ c : Fin 15, dwz63Alpha c = 100000000 := profileMass_dwz63Alpha
    have hmassReal : (∑ c : Fin 15, (dwz63Alpha c : ℝ)) = 100000000 := by
      exact_mod_cast hmass
    rw [hmassReal]
    norm_num

/-- The entropy of the normalized global law is its committed integral-profile entropy. -/
theorem dwz63_globalAlpha_entropy_eq :
    MaximumEntropyDual.entropy (fun c : Fin 15 => (dwz63Alpha c : ℝ) / 100000000) =
      WordType.profileEntropyNats dwz63Alpha := by
  simp only [MaximumEntropyDual.entropy, WordType.profileEntropyNats,
    profileMass_dwz63Alpha, Nat.cast_ofNat]

/-- The integer partition sums over all fifteen legal global states, using physical Z. -/
theorem dwz63_integerPartition_eq :
    integerPartitionNumerator dwz63XIndex dwz63YIndex dwz63ZIndex
      dwz63IntegerGibbsX dwz63IntegerGibbsY dwz63IntegerGibbsZ =
      999999264240775404 := by
  norm_num [integerPartitionNumerator, dwz63XIndex, dwz63YIndex, dwz63ZIndex,
    dwz63IntegerGibbsX, dwz63IntegerGibbsY, dwz63IntegerGibbsZ, Fin.sum_univ_succ]

/-- The integer-coordinate dual gap is exactly the committed Gibbs deficit in bits.

Proof sketch: express the integer dual as the ordinary coordinate dual, convert its bits to
nats, and cancel the common score shift against the actual probability law. The existing
global Gibbs-gap identity then identifies the result, with one final division by `log 2`. -/
theorem dwz63_integerDualGap_eq :
    integerCoordinateDualBits dwz63XIndex dwz63YIndex dwz63ZIndex
        (fun c : Fin 15 => (dwz63Alpha c : ℝ) / 100000000)
        dwz63IntegerGibbsX dwz63IntegerGibbsY dwz63IntegerGibbsZ -
      MaximumEntropyDual.entropyBits (fun c : Fin 15 => (dwz63Alpha c : ℝ) / 100000000) =
      dwz63GibbsDeficit / Real.log 2 := by
  let p : Fin 15 → ℝ := fun c => (dwz63Alpha c : ℝ) / 100000000
  change integerCoordinateDualBits dwz63XIndex dwz63YIndex dwz63ZIndex p
      dwz63IntegerGibbsX dwz63IntegerGibbsY dwz63IntegerGibbsZ -
    MaximumEntropyDual.entropyBits p = dwz63GibbsDeficit / Real.log 2
  rw [← coordinateDualBits_logIntegerPotential_eq dwz63XIndex dwz63YIndex dwz63ZIndex p
    dwz63IntegerGibbsX dwz63IntegerGibbsY dwz63IntegerGibbsZ dwz63_integerGibbs_pos.1
    dwz63_integerGibbs_pos.2.1 dwz63_integerGibbs_pos.2.2]
  unfold logIntegerPotential
  rw [MaximumEntropyDual.coordinateDualBits_div_log_two]
  have hscore : MaximumEntropyDual.coordinateScore dwz63XIndex dwz63YIndex dwz63ZIndex
      (fun x => Real.log (dwz63IntegerGibbsX x : ℝ))
      (fun y => Real.log (dwz63IntegerGibbsY y : ℝ))
      (fun z => Real.log (dwz63IntegerGibbsZ z : ℝ)) =
      (fun c => dwz63GibbsScore c + 3 * Real.log (1000000 : ℝ)) :=
    funext dwz63_integerGibbs_score_eq
  rw [hscore, MaximumEntropyDual.logPartition_sub_expectation_add_const p dwz63GibbsScore
    (3 * Real.log (1000000 : ℝ)) dwz63_globalAlpha_isProbability.2]
  dsimp only [p]
  rw [dwz63_partition_dwz63GibbsScore, dwz63_logPartition_sub_alphaScore,
    MaximumEntropyDual.entropyBits, dwz63_globalAlpha_entropy_eq]
  ring

/-- The integer-format certificate recovers the committed hash-loss budget for global alpha.

Proof sketch: apply the existing integer-coordinate combination-loss upper bound at the
literal positive factors and probability law. Rewrite its gap by the exact identity above
and use the already certified natural-log hash-loss bound, divided by positive `log 2`. -/
theorem dwz63_combinationLossBits_le_log_hashLossMultiplier :
    MaximumEntropyDual.combinationLossBits dwz63XIndex dwz63YIndex dwz63ZIndex
        (fun c : Fin 15 => (dwz63Alpha c : ℝ) / 100000000) ≤
      Real.log dwz63HashLossMultiplier / Real.log 2 := by
  have hdual := combinationLossBits_le_integerDualGap dwz63XIndex dwz63YIndex dwz63ZIndex
    (fun c : Fin 15 => (dwz63Alpha c : ℝ) / 100000000)
    dwz63IntegerGibbsX dwz63IntegerGibbsY dwz63IntegerGibbsZ dwz63_globalAlpha_isProbability
    dwz63_integerGibbs_pos.1 dwz63_integerGibbs_pos.2.1 dwz63_integerGibbs_pos.2.2
  rw [dwz63_integerDualGap_eq] at hdual
  exact hdual.trans (div_le_div_of_nonneg_right dwz63_gibbsDeficit_le_log_hashLossMultiplier
    (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))))

end

end AlgebraicComplexity.Examples
