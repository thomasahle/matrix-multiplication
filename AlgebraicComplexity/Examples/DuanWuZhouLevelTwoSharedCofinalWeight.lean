/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOmegaBound
import AlgebraicComplexity.MatrixMultiplication.AsymmetricGlobalCofinalWeight

/-!
# The paid-margin DWZ instance of the shared cofinal weight theorem

This transcribes [duan2023faster], section 6, `eq:value_before_nth_root` and
`eq:numeric_conclusion_g` (`papers/sources/2210.10173/global_value.tex:269-309`), at the
literal second-power parameters of section 6.3 (`global_value.tex:332-378`).

The committed common-seed supplier supplies the restriction, retained count, and batching bound
at the same period and reference word. The three orbit suppliers and reference-leaf assembly
give the leaf weight with the positive margin already paid. The actual period sequence makes
these stages cofinal and satisfies both leaf divisibilities. Six orientations appear in the
assembled source and the weight rate exactly once.

`DuanWuZhouLevelTwoOmegaBound` is imported for its period definitions and their suppliers;
no proof calls its numerical endpoint or any other numerical omega endpoint. This is the
DWZ second-power bound, not its higher-power headline or a Total-Weight/q20 theorem. Finite
certificate interpretation is separate from the cofinal semantic construction here.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open _root_.AlgebraicComplexity.AsymmetricGlobal _root_.AlgebraicComplexity.Tensor

universe u

variable (K : Type u) [Field K]

/-- The common-seed construction supplies finite positive weight at every admitted period.
Proof sketch: combine its retained-count and good-batch bounds, then apply the paid-margin
leaf estimate to its actual direct sum and restrict back to the six-orientation source.
The finite construction is checked separately from the cofinal choice of periods. -/
theorem dwz63_exists_weightedSeededPeriod :
    ∃ N₀ : ℕ, ∀ s : ℕ,
      40000000000000 ∣ s → 312500000000000000000 ∣ s → N₀ ≤ s →
      ∀ (n : ℕ) (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n),
        n + 1 = 20000000000000000 * s →
        (∀ t : Fin 15, WordType.multiplicity (dwz63Seg K n wRef) t
          = 200000000 * (dwz63Alpha t * s)) →
        wRef ∈ dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha (200000000 * s)) →
        HasTauWeight K
          (symSix K (dwz63ReferenceLeaf K n (dwz63JoinedAlphaTilde s) wRef).realize) dwz63Tau
          (Real.exp (((n : ℝ) + 1) * (dwz63LogVal - dwz63LeafMargin)) ^ 6) →
        ∃ value : ℝ, 0 < value ∧
          HasTauWeight K (Tensor.power (symSix K (dwz63Source K)) (n + 1)) dwz63Tau value ∧
          ((dwz63TrueCopyRate * Real.exp (dwz63LogVal - dwz63LeafMargin)) ^ 6) ^ (n + 1) ≤
            ((4 * dwz63PlainMarkedLossHashJoint K (n + 1)) *
              ((4 * dwz63GoodBatchSize n : ℕ) : ℝ)) ^ 6 * value := by
  classical
  obtain ⟨Nseed, hseedPeriod⟩ := dwz63_exists_seededPeriod K
  refine ⟨Nseed, fun s hdvd6 hdvd7 hsseed n wRef hn hmu hmark hleaf ↦ ?_⟩
  obtain ⟨B, seed, batches, _hBfree, hstage, hcopy, hcard⟩ :=
    hseedPeriod s hdvd6 hdvd7 hsseed n wRef hn hmu hmark
  rw [Fintype.card_coe] at hcopy
  have hcount0 := hcopy.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 6)
    (pow_nonneg (mul_nonneg (by norm_num)
      (dwz63PlainMarkedLossHashJoint_nonneg K (n + 1))) 6))
  let stageLoss := ((4 * dwz63PlainMarkedLossHashJoint K (n + 1)) *
    ((4 * dwz63GoodBatchSize n : ℕ) : ℝ)) ^ 6
  have hcount : dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      stageLoss * (Fintype.card (dwz63SymSixIndex (Fin batches)) : ℝ) := by
    refine hcount0.trans_eq ?_
    simp only [stageLoss, dwz63_card_symSixIndex, Nat.cast_pow, mul_pow]
    ring
  have hcards : 0 < Fintype.card (dwz63SymSixIndex (Fin batches)) := by
    rcases Nat.eq_zero_or_pos (Fintype.card (dwz63SymSixIndex (Fin batches))) with h0 | hpos
    · exfalso
      rw [h0, Nat.cast_zero, mul_zero] at hcount
      exact absurd hcount (not_le.mpr (pow_pos dwz63TrueCopyRate_pos _))
    · exact hpos
  have hcardPos : (0 : ℝ) < (Fintype.card (dwz63SymSixIndex (Fin batches)) : ℝ) := by
    exact_mod_cast hcards
  let leafValue := Real.exp (((n : ℝ) + 1) * (dwz63LogVal - dwz63LeafMargin)) ^ 6
  have hleafValue : 0 < leafValue := pow_pos (Real.exp_pos _) 6
  let value := (Fintype.card (dwz63SymSixIndex (Fin batches)) : ℝ) * leafValue
  refine ⟨value, mul_pos hcardPos hleafValue, ?_, ?_⟩
  · exact HasTauWeight.of_restricts hstage
      (HasTauWeight.indexedDirectSum_of_forall
        (fun _ : dwz63SymSixIndex (Fin batches) ↦ hleaf))
  · calc
      ((dwz63TrueCopyRate * Real.exp (dwz63LogVal - dwz63LeafMargin)) ^ 6) ^ (n + 1)
          = dwz63TrueCopyRate ^ (6 * (n + 1)) * leafValue := by
            rw [← pow_mul, mul_pow, ← dwz63_exp_pow_six_eq]
      _ ≤ (stageLoss * (Fintype.card (dwz63SymSixIndex (Fin batches)) : ℝ)) *
          leafValue := mul_le_mul_of_nonneg_right hcount hleafValue.le
      _ = stageLoss * value := by dsimp [value]; ring

/-- The three orbit suppliers and regional assembly give the paid-margin leaf weight.
Proof sketch: clear all three existing cutoffs along the same two divisibility periods,
then assemble the orbit estimates before choosing a reference word. -/
theorem dwz63_exists_paidMarginReferenceLeafPeriod :
    ∃ N₀ : ℕ, ∀ s : ℕ,
      40000000000000 ∣ s → 312500000000000000000 ∣ s → N₀ ≤ s →
      ∀ (n : ℕ) (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n),
        (∀ t : Fin 15, WordType.multiplicity (dwz63Seg K n wRef) t
          = 200000000 * (dwz63Alpha t * s)) →
        HasTauWeight K
          (symSix K (dwz63ReferenceLeaf K n (dwz63JoinedAlphaTilde s) wRef).realize) dwz63Tau
          (Real.exp (((n : ℝ) + 1) * (dwz63LogVal - dwz63LeafMargin)) ^ 6) := by
  classical
  obtain ⟨Nleaf, hleafPeriod⟩ :=
    dwz63_hasTauWeight_symSix_referenceLeaf K dwz63LeafMargin dwz63LeafMargin_pos
  obtain ⟨N6, hrow6⟩ := dwz63_orbitRowSix_R3 K (by norm_num) (by norm_num [dwz63Q])
  obtain ⟨N7, hrow7⟩ := dwz63_orbitRowsSevenTen_R3 K (by norm_num) (by norm_num [dwz63Q])
  refine ⟨max Nleaf
    (max (40000000000000 * (N6 + 1)) (312500000000000000000 * (N7 + 1))),
    fun s hdvd6 hdvd7 hs ↦ ?_⟩
  have hsleaf : Nleaf ≤ s := le_trans (le_max_left _ _) hs
  have hs6 : 40000000000000 * (N6 + 1) ≤ s :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hs7 : 312500000000000000000 * (N7 + 1) ≤ s :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have hdiv6 : N6 + 1 ≤ s / 40000000000000 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have hdiv7 : N7 + 1 ≤ s / 312500000000000000000 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have hcut : ∀ (o : Fin 3) (m : ℕ),
      m + 1 = 200000000 * (dwz63Alpha (dwz63OrbitRow o) * s) →
      HasTauWeight K
        (symThree K (dwz63OrbitRegion K dwz63Q o (dwz63OrbitRow o) m
          (dwz63Alpha (dwz63OrbitRow o) * s)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * ((dwz63Alpha (dwz63OrbitRow o) * s : ℕ) : ℝ) *
          (dwz63OrbitLogVal o - dwz63LeafMargin)) ^ 3) := by
    intro o m hm
    by_cases ho : o = 0
    · subst ho
      exact hrow6 s hdvd6
        (le_trans (by omega : N6 ≤ s / 40000000000000)
          (Nat.le_mul_of_pos_left _ (by norm_num)))
        (Nat.mul_pos (by norm_num) (by omega)) m hm
    · exact hrow7 s hdvd7
        (le_trans (by omega : N7 ≤ s / 312500000000000000000)
          (Nat.le_mul_of_pos_left _ (by norm_num)))
        (Nat.mul_pos (by norm_num) (by omega)) o ho m hm
  exact fun n wRef hmu ↦ hleafPeriod s hsleaf hcut n wRef hmu

/-- The actual common-seed DWZ stages have positive cofinal weight at the paid-margin rate.
The one loss contains the joint hashing loss and the good-batch cost, each raised only when
assembling the six orientations. -/
theorem dwz63_cofinal_hasTauWeight_paidMargin :
    ∃ loss : ℕ → ℝ, Growth.Subexponential loss ∧
      ∀ cutoff : ℕ, ∃ N : ℕ, cutoff ≤ N ∧ 0 < N ∧
        ∃ value : ℝ, 0 < value ∧
          HasTauWeight K (Tensor.power (symSix K (dwz63Source K)) N) dwz63Tau value ∧
          ((dwz63TrueCopyRate * Real.exp (dwz63LogVal - dwz63LeafMargin)) ^ 6) ^ N ≤
            loss N * value := by
  classical
  let loss : ℕ → ℝ := fun N ↦
    ((4 * dwz63PlainMarkedLossHashJoint K N) *
      ((4 * dwz63GoodBatchSize (N - 1) : ℕ) : ℝ)) ^ 6
  have hloss : Growth.Subexponential loss :=
    subexponential_pow_six
      (((subexponential_dwz63PlainMarkedLossHashJoint K).const_mul (by norm_num)).mul
        dwz63_subexponential_four_mul_goodBatchSize_pred)
  obtain ⟨Nleaf, hleafPeriod⟩ := dwz63_exists_paidMarginReferenceLeafPeriod K
  obtain ⟨Nseed, hseedPeriod⟩ := dwz63_exists_weightedSeededPeriod K
  let threshold := max Nleaf Nseed
  refine ⟨loss, hloss, fun cutoff ↦ ?_⟩
  obtain ⟨s, n, hs, hn, hcofinal, hdvd⟩ :
      ∃ s n : ℕ, threshold ≤ s ∧ n + 1 = 20000000000000000 * s ∧
        cutoff ≤ n + 1 ∧ 40000000000000 ∣ s ∧ 312500000000000000000 ∣ s := by
    exact ⟨dwz63PeriodSeq threshold cutoff, dwz63PeriodLen threshold cutoff,
      dwz63_le_periodSeq threshold cutoff, dwz63_periodLen_succ threshold cutoff,
      dwz63_periodSeq_cofinal threshold cutoff, dwz63_periodSeq_dvd threshold cutoff⟩
  have hsleaf : Nleaf ≤ s := le_trans (le_max_left _ _) hs
  have hsseed : Nseed ≤ s := le_trans (le_max_right _ _) hs
  obtain ⟨wRef, hmu, hmark⟩ :=
    dwz63_exists_referenceWord_marked K n (200000000 * s) s rfl (by omega)
  have hleaf := hleafPeriod s hdvd.1 hdvd.2 hsleaf n wRef hmu
  obtain ⟨value, hvalue, hweight, hrate⟩ :=
    hseedPeriod s hdvd.1 hdvd.2 hsseed n wRef hn hmu hmark hleaf
  refine ⟨n + 1, hcofinal, Nat.succ_pos n, value, hvalue, hweight, ?_⟩
  simpa only [loss, Nat.add_sub_cancel] using hrate

/-- The literal DWZ section 6.3 bound obtained from the shared cofinal-weight theorem, with
the certified interior rate and the positive leaf margin retained. -/
theorem dwz63_omega_lt_2374631_sharedCofinal : omega K < (2374631 / 1000000 : ℝ) := by
  have hweight := dwz63_cofinal_hasTauWeight_paidMargin K
  have hgap : (dwz63RateDataMargin 1 one_pos).globalRate ^ 6 <
      (dwz63TrueCopyRate * Real.exp (dwz63LogVal - dwz63LeafMargin)) ^ 6 :=
    pow_lt_pow_left₀ (dwz63_globalRateMargin_lt_trueRateMargin 1 one_pos)
      (dwz63RateDataMargin 1 one_pos).globalRate_pos.le (by norm_num)
  have hbound : omega K < 3 * dwz63Tau :=
    AsymmetricGlobal.omega_lt_three_mul_of_cofinal_hasTauWeight
      (dwz63_asymptoticRank_symSix_le K)
      (pow_pos (dwz63RateDataMargin 1 one_pos).globalRate_pos 6)
      (dwz63_rankBudget_lt_globalRateMargin_pow 1 one_pos) hgap hweight
  have htau : 3 * dwz63Tau = (2374631 / 1000000 : ℝ) := by norm_num [dwz63Tau]
  rwa [htau] at hbound

end AlgebraicComplexity.Examples
