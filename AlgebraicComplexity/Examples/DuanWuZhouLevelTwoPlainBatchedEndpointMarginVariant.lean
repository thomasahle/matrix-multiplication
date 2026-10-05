/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoIsolatedSumRate
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpointMargin
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpoint

set_option autoImplicit false

/-!
# The section 6.3 endpoint at the leaf-value margin

Layer 4 (`AlgebraicComplexity/Examples/`).  The committed
`omega_lt_2374631_of_plainBatchedStageAndLeaf` asks for a leaf value at the base
`exp dwz63LogVal`, which no positive-deficit route can supply (`dwz63_regionProduct_lt_required`,
image 109).  This module is the same endpoint with that binder shifted by `dwz63LeafMargin`, and
nothing else changed.

## What makes the shift sound

`dwz63LogVal` reaches `omega` only through the declared `valRate` of the rate data, and the ω bound
needs only `64 ^ 6 < globalRate ^ 6`.  So the shift is paid for by declaring a **smaller rational
`valRate`**: `dwz63RateDataMargin` is `dwz63RateData` with `dwz63ValRateMargin` in place of
`dwz63ValRate`, and the two obligations were discharged in image 114 ---
`dwz63_rankBudget_lt_marginGlobalRate_pow` (the budget still clears at `64.0000024…`) and
`dwz63_valRateMargin_le_exp_sub` (the shifted value still dominates it).  The available slack is
`1.7246136 * 10 ^ (-7)` nats per letter and `dwz63LeafMargin = 10 ^ (-7)` claims `58%` of it.

## Structure

The three layers of the committed chain are re-issued at an arbitrary rate data rather than
`dwz63RateData`: `omega_lt_2374631_of_dwzLevelTwoAssembledStageData` takes the rank-budget
comparison as a hypothesis, `dwzLevelTwoAssembledStage_of_countingStageAtData` takes the strict gap
as one, and `omega_lt_2374631_of_plainSymSixStageMargin` reuses image 116's
`dwzLevelTwoCountingStage_of_isolatedSumAt`, which never mentions a rate data.  Every proof is the
committed one verbatim with the numeric input replaced by the hypothesis.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity AsymmetricGlobal Tensor

universe u v y

/-! ## The rate data at the margin -/

/-- **The section 6.3 rate data with the margin `valRate`.**  Identical to `dwz63RateData` except
that the declared leaf-value rate is `dwz63ValRateMargin`. -/
noncomputable def dwz63RateDataMargin (ambient : ℝ) (hambient : 0 < ambient) : GlobalRateData
  where
  ambientRate := ambient
  hashLossRate := ambient * dwz63HashLossMultiplier
  xRate := dwz63XRate
  zRate := dwz63ZRate
  compatRate := dwz63CompatRate
  valRate := dwz63ValRateMargin
  ambientRate_pos := hambient
  hashLossRate_pos := mul_pos hambient dwz63HashLossMultiplier_pos
  xRate_pos := dwz63XRate_pos
  zRate_pos := dwz63ZRate_pos
  compatRate_pos := dwz63CompatRate_pos
  valRate_pos := dwz63ValRateMargin_pos

theorem dwz63RateDataMargin_globalRate (ambient : ℝ) (hambient : 0 < ambient) :
    (dwz63RateDataMargin ambient hambient).globalRate =
      min (dwz63XRate / dwz63HashLossMultiplier) (dwz63ZRate / dwz63CompatRate) *
        dwz63ValRateMargin := by
  have hbranch : ambient * dwz63XRate / (ambient * dwz63HashLossMultiplier)
      = dwz63XRate / dwz63HashLossMultiplier := by
    rw [mul_div_mul_left _ _ hambient.ne']
  rw [GlobalRateData.globalRate_eq_min_mul]
  show min (ambient * dwz63XRate / (ambient * dwz63HashLossMultiplier))
      (dwz63ZRate / dwz63CompatRate) * dwz63ValRateMargin = _
  rw [hbranch]

/-- The rank budget clears at the margin rate data. -/
theorem dwz63_rankBudget_lt_globalRateMargin_pow (ambient : ℝ) (hambient : 0 < ambient) :
    (68719476736 : ℝ) < (dwz63RateDataMargin ambient hambient).globalRate ^ 6 := by
  rw [dwz63RateDataMargin_globalRate]
  exact dwz63_rankBudget_lt_marginGlobalRate_pow

/-- **The strict gap at the margin.**  The committed `dwz63_globalRate_lt_trueGlobalRate` with the
value step supplied by `dwz63_valRateMargin_le_exp_sub`. -/
theorem dwz63_globalRateMargin_lt_trueRateMargin (ambient : ℝ) (hambient : 0 < ambient) :
    (dwz63RateDataMargin ambient hambient).globalRate <
      dwz63TrueCopyRate * Real.exp (dwz63LogVal - dwz63LeafMargin) := by
  have hbranch1 : dwz63XRate / dwz63HashLossMultiplier <
      Real.exp dwz63EntropyX / dwz63HashLossMultiplier := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right dwz63_xRate_lt_exp (inv_pos.mpr dwz63HashLossMultiplier_pos)
  have hbranch2 : dwz63ZRate / dwz63CompatRate <
      Real.exp dwz63EntropyZ / Real.exp dwz63LogCompat := by
    rw [div_lt_div_iff₀ dwz63CompatRate_pos (Real.exp_pos _)]
    calc dwz63ZRate * Real.exp dwz63LogCompat
        < Real.exp dwz63EntropyZ * Real.exp dwz63LogCompat :=
          mul_lt_mul_of_pos_right dwz63_zRate_lt_exp (Real.exp_pos _)
      _ ≤ Real.exp dwz63EntropyZ * dwz63CompatRate :=
          mul_le_mul_of_nonneg_left dwz63_exp_le_compatRate (Real.exp_pos _).le
  have hmin : min (dwz63XRate / dwz63HashLossMultiplier) (dwz63ZRate / dwz63CompatRate) <
      min (Real.exp dwz63EntropyX / dwz63HashLossMultiplier)
        (Real.exp dwz63EntropyZ / Real.exp dwz63LogCompat) :=
    lt_min (lt_of_le_of_lt (min_le_left _ _) hbranch1)
      (lt_of_le_of_lt (min_le_right _ _) hbranch2)
  have hminPos : 0 < min (Real.exp dwz63EntropyX / dwz63HashLossMultiplier)
      (Real.exp dwz63EntropyZ / Real.exp dwz63LogCompat) := by
    refine lt_min ?_ ?_
    · exact div_pos (Real.exp_pos _) dwz63HashLossMultiplier_pos
    · exact div_pos (Real.exp_pos _) (Real.exp_pos _)
  rw [dwz63RateDataMargin_globalRate]
  unfold dwz63TrueCopyRate
  calc min (dwz63XRate / dwz63HashLossMultiplier) (dwz63ZRate / dwz63CompatRate)
        * dwz63ValRateMargin
      < min (Real.exp dwz63EntropyX / dwz63HashLossMultiplier)
          (Real.exp dwz63EntropyZ / Real.exp dwz63LogCompat) * dwz63ValRateMargin :=
        mul_lt_mul_of_pos_right hmin dwz63ValRateMargin_pos
    _ ≤ min (Real.exp dwz63EntropyX / dwz63HashLossMultiplier)
          (Real.exp dwz63EntropyZ / Real.exp dwz63LogCompat)
        * Real.exp (dwz63LogVal - dwz63LeafMargin) :=
        mul_le_mul_of_nonneg_left dwz63_valRateMargin_le_exp_sub hminPos.le

/-! ## The chain at an arbitrary rate data -/

section Data

variable {F : Type u} [Field F] {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)]

/-- The committed `omega_lt_2374631_of_dwzLevelTwoAssembledStage` with the rank-budget comparison
as a hypothesis, so it applies at any rate data. -/
theorem omega_lt_2374631_of_dwzLevelTwoAssembledStageData {T : Tensor3 F V} {d : GlobalRateData}
    (hbudget : (68719476736 : ℝ) < d.globalRate ^ 6)
    (hstage : DwzLevelTwoAssembledStage T d) :
    omega F < (2374631 / 1000000 : ℝ) := by
  obtain ⟨hrank, N, value, hN, hvaluePos, hweight, hgap⟩ := hstage
  have hglobalPos := d.globalRate_pos
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hroot : (d.globalRate ^ (6 * N)) ^ ((N : ℝ)⁻¹) = d.globalRate ^ 6 := by
    rw [← Real.rpow_natCast _ (6 * N), ← Real.rpow_mul hglobalPos.le, ← Real.rpow_natCast _ 6]
    congr 1
    push_cast
    field_simp
  have hkey : omega F < 3 * dwz63Tau := by
    refine omega_lt_three_mul_of_hasTauWeight hN hvaluePos hrank hweight ?_
    calc (68719476736 : ℝ) < d.globalRate ^ 6 := hbudget
      _ = (d.globalRate ^ (6 * N)) ^ ((N : ℝ)⁻¹) := hroot.symm
      _ ≤ value ^ ((N : ℝ)⁻¹) :=
          Real.rpow_le_rpow (pow_nonneg hglobalPos.le _) hgap (by positivity)
  rwa [dwz63_three_mul_tau] at hkey

/-- The count-side residual at rate `r` implies the assembled stage at any rate data with
`globalRate < r`. -/
theorem dwzLevelTwoAssembledStage_of_countingStageAtData {r : ℝ} {T : Tensor3 F V}
    {d : GlobalRateData} (hgap : d.globalRate < r)
    (hrank : Tensor.asymptoticRank (symSix F T) ≤ 68719476736)
    (hcount : DwzLevelTwoCountingStageAt r T) :
    DwzLevelTwoAssembledStage T d := by
  obtain ⟨loss, hloss, hstages⟩ := hcount
  have hglobalPos := d.globalRate_pos
  have hgap6 : d.globalRate ^ 6 < r ^ 6 :=
    pow_lt_pow_left₀ hgap hglobalPos.le (by norm_num)
  obtain ⟨cutoff, hcutoff⟩ :=
    exists_cutoff_pow_le_of_pow_le_subexponential_mul hloss (pow_pos hglobalPos 6) hgap6
  obtain ⟨n, hn, hnpos, value, hvaluePos, hweight, hbound⟩ := hstages cutoff
  refine ⟨hrank, n, value, hnpos, hvaluePos, hweight, ?_⟩
  have hpow : ∀ x : ℝ, x ^ (6 * n) = (x ^ 6) ^ n := by
    intro x
    rw [← pow_mul]
  rw [hpow] at hbound ⊢
  exact hcutoff n value hn hvaluePos.le hbound

/-- `omega < 2.374631` from a residual at rate `r`, at any rate data clearing the budget. -/
theorem omega_lt_2374631_of_countingStageAtData {r : ℝ} {T : Tensor3 F V} {d : GlobalRateData}
    (hbudget : (68719476736 : ℝ) < d.globalRate ^ 6) (hgap : d.globalRate < r)
    (hrank : Tensor.asymptoticRank (symSix F T) ≤ 68719476736)
    (hcount : DwzLevelTwoCountingStageAt r T) :
    omega F < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_dwzLevelTwoAssembledStageData hbudget
    (dwzLevelTwoAssembledStage_of_countingStageAtData hgap hrank hcount)

end Data

/-! ## The endpoint at the margin -/

/-- `omega < 2.374631` at the level-two source from a residual at the margin rate. -/
theorem omega_lt_2374631_of_dwz63CountingStageAtMargin {F : Type u} [Field F]
    (hcount : DwzLevelTwoCountingStageAt
      (dwz63TrueCopyRate * Real.exp (dwz63LogVal - dwz63LeafMargin)) (dwz63Source F)) :
    omega F < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_countingStageAtData
    (dwz63_rankBudget_lt_globalRateMargin_pow 1 one_pos)
    (dwz63_globalRateMargin_lt_trueRateMargin 1 one_pos)
    (dwz63_asymptoticRank_symSix_le F) hcount

/-- **The plain `sym₆` stage at the margin.**  The committed proof with the leaf-value base
shifted; the residual comes from image 116's `dwzLevelTwoCountingStage_of_isolatedSumAt`, which
mentions no rate data. -/
theorem omega_lt_2374631_of_plainSymSixStageMargin
    {K : Type u} [Field K]
    (len : ℕ → ℕ)
    (hcofinal : ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1)
    {β : ℕ → Type} [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)]
    {W : ℕ → Leg → Type y} [∀ j c, AddCommMonoid (W j c)] [∀ j c, Module K (W j c)]
    (leaf : ∀ j : ℕ, Tensor3 K (W j))
    (weight loss : ℕ → ℝ)
    (hloss : Growth.Subexponential loss)
    (hstage : ∀ j : ℕ,
      Restricts (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize) (len j + 1))
        (Tensor.indexedDirectSum
          (fun _ : dwz63SymSixIndex (β j) ↦ symSix K (leaf j))))
    (hleafWeight : ∀ j : ℕ, HasTauWeight K (symSix K (leaf j)) dwz63Tau (weight j))
    (hleafValue : ∀ j : ℕ,
      Real.exp (dwz63LogVal - dwz63LeafMargin) ^ (6 * (len j + 1)) ≤ weight j)
    (hweightPos : ∀ j : ℕ, 0 < weight j)
    (hcount : ∀ j : ℕ, dwz63TrueCopyRate ^ (6 * (len j + 1)) ≤
      loss (len j + 1) * ((Fintype.card (β j) : ℝ) ^ 6)) :
    omega K < (2374631 / 1000000 : ℝ) := by
  classical
  have hcount' : ∀ j : ℕ, dwz63TrueCopyRate ^ (6 * (len j + 1)) ≤
      loss (len j + 1) * ((Fintype.card (dwz63SymSixIndex (β j)) : ℝ)) := by
    intro j
    rw [dwz63_card_symSixIndex]
    push_cast
    exact hcount j
  have hcards : ∀ j : ℕ, 0 < Fintype.card (dwz63SymSixIndex (β j)) := by
    intro j
    rcases Nat.eq_zero_or_pos (Fintype.card (dwz63SymSixIndex (β j))) with h0 | hpos
    · exfalso
      have h1 := hcount' j
      rw [h0] at h1
      simp only [Nat.cast_zero, mul_zero] at h1
      exact absurd h1 (not_le.mpr (pow_pos dwz63TrueCopyRate_pos _))
    · exact hpos
  exact omega_lt_2374631_of_dwz63CountingStageAtMargin
    (dwzLevelTwoCountingStage_of_isolatedSumAt
      (Real.exp (dwz63LogVal - dwz63LeafMargin)) (Real.exp_pos _).le
      (Iso := fun j ↦ dwz63SymSixIndex (β j))
      (fun j ↦ len j + 1) (fun j _ ↦ symSix K (leaf j)) weight loss hloss
      (fun cutoff ↦ (hcofinal cutoff).imp fun _ hj ↦ ⟨hj, Nat.succ_pos _⟩)
      hstage (fun j _ ↦ hleafWeight j) hweightPos hcards hcount' hleafValue)

/-! ## The batched endpoint at the margin -/

theorem omega_lt_2374631_of_plainBatchedStageAndLeaf_margin
    {K : Type u} [Field K]
    (len scale : ℕ → ℕ)
    (hlen : ∀ j : ℕ, len j + 1 = 100000000 * scale j)
    (hcofinal : ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1)
    {β : ℕ → Type} [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)]
    {W : ℕ → Leg → Type y} [∀ j c, AddCommMonoid (W j c)] [∀ j c, Module K (W j c)]
    (leaf : ∀ j : ℕ, Tensor3 K (W j)) (weight : ℕ → ℝ)
    (batchLoss : ℕ → ℝ) (hbatchLoss : Growth.Subexponential batchLoss)
    (hstage : ∀ (j : ℕ)
        (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j))))
        (_seed : ProgressionHash.Seed
          (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j)))
          (Fin (len j + 1))),
        ThreeAPFree (B : Set (dwz63SharpHashField
          (dwz63PlainSharpDegree K (len j) (scale j)))) →
        Restricts
          (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize) (len j + 1))
          (Tensor.indexedDirectSum
            (fun _ : dwz63SymSixIndex (β j) ↦ symSix K (leaf j))))
    (hbatchCard : ∀ (j : ℕ)
        (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j))))
        (seed : ProgressionHash.Seed
          (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j)))
          (Fin (len j + 1))),
        ThreeAPFree (B : Set (dwz63SharpHashField
          (dwz63PlainSharpDegree K (len j) (scale j)))) →
        (((dwz63PlainJointRetainedSupport K
            (dwz63_cwSquareFieldValue_sharpHashField_injective
              (dwz63PlainSharpDegree K (len j) (scale j)))
            (len j) (scale j) (dwz63PlainMarginalWords K (len j) (scale j))
            B seed).card : ℝ)) ≤
          batchLoss (len j + 1) * (Fintype.card (β j) : ℝ))
    (hleafWeight : ∀ j : ℕ, HasTauWeight K (symSix K (leaf j)) dwz63Tau (weight j))
    (hleafValue : ∀ j : ℕ,
        Real.exp (dwz63LogVal - dwz63LeafMargin) ^ (6 * (len j + 1)) ≤ weight j) :
    omega K < (2374631 / 1000000 : ℝ) := by
  classical
  choose B hBfree hbr using fun j : ℕ ↦ exists_behrend_dwz63_plainHashBranch K (hlen j)
  choose seed hseed using fun j : ℕ ↦
    dwz63_exists_seed_plainCopyCount_at_sharpDegree K
      (dwz63_cwSquareFieldValue_sharpHashField_injective
        (dwz63PlainSharpDegree K (len j) (scale j)))
      (hlen j) (dwz63PlainMarginalWords K (len j) (scale j)) (Finset.Subset.refl _)
      (B j) (hBfree j)
      (by rw [card_dwz63SharpHashField]; exact dwz63SharpHashModulus_requirement _)
      (dwz63PlainMarkedLossHash_nonneg K (len j + 1)) (hbr j)
  refine omega_lt_2374631_of_plainSymSixStageMargin len hcofinal leaf weight
    (fun N ↦ (dwz63PlainMarkedLossHash K N * batchLoss N) ^ 6)
    (subexponential_pow_six ((subexponential_dwz63PlainMarkedLossHash K).mul hbatchLoss))
    (fun j ↦ hstage j (B j) (seed j) (hBfree j)) hleafWeight hleafValue
    (fun j ↦ lt_of_lt_of_le (pow_pos (Real.exp_pos _) _) (hleafValue j)) ?_
  intro j
  have hcard := hbatchCard j (B j) (seed j) (hBfree j)
  have hlossnn : (0 : ℝ) ≤ dwz63PlainMarkedLossHash K (len j + 1) ^ 6 :=
    pow_nonneg (dwz63PlainMarkedLossHash_nonneg K _) 6
  have h6 : ((Fintype.card (dwz63PlainJointRetainedSupport K
        (dwz63_cwSquareFieldValue_sharpHashField_injective
          (dwz63PlainSharpDegree K (len j) (scale j)))
        (len j) (scale j) (dwz63PlainMarginalWords K (len j) (scale j))
        (B j) (seed j)) : ℝ)) ^ 6 ≤
      batchLoss (len j + 1) ^ 6 * (Fintype.card (β j) : ℝ) ^ 6 := by
    rw [Fintype.card_coe, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 6
  calc dwz63TrueCopyRate ^ (6 * (len j + 1))
      ≤ dwz63PlainMarkedLossHash K (len j + 1) ^ 6 *
          ((Fintype.card (dwz63PlainJointRetainedSupport K
            (dwz63_cwSquareFieldValue_sharpHashField_injective
              (dwz63PlainSharpDegree K (len j) (scale j)))
            (len j) (scale j) (dwz63PlainMarginalWords K (len j) (scale j))
            (B j) (seed j)) : ℝ)) ^ 6 := hseed j
    _ ≤ dwz63PlainMarkedLossHash K (len j + 1) ^ 6 *
          (batchLoss (len j + 1) ^ 6 * (Fintype.card (β j) : ℝ) ^ 6) :=
        mul_le_mul_of_nonneg_left h6 hlossnn
    _ = (dwz63PlainMarkedLossHash K (len j + 1) * batchLoss (len j + 1)) ^ 6 *
          (Fintype.card (β j) : ℝ) ^ 6 := by
        rw [mul_pow]; ring

end AlgebraicComplexity.Examples
