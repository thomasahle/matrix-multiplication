/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellRows
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellGeneral
import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedDivisionIterated

set_option autoImplicit false

/-!
# The nine off-split cells, weighed at the published value

Layer 4 (`AlgebraicComplexity/Examples/`).  `dwz63_exists_zeroFineCellWeight`
(`Examples/DuanWuZhouLevelTwoFineCellGeneral.lean`) delivers a weight parameterised by an arbitrary
strict lower base for the entropy rate.  `SegmentedRegionalWeights`
(`MatrixMultiplication/SegmentedLocalizedDivisionIterated.lean`) wants, per region, a single
`HasTauWeight` fact at a definite real `value`.  This module closes the gap: it converts the
strict-base form into a weight at

`exp (mass * j * (dwz63LogVal_t - eps))`,

one statement per cell, which is exactly a region's `value` field at that period.

## Why a deficit, and why `eps` is a parameter rather than a constant

The multinomial coefficient only *approaches* `2 ^ (mass * H)`; it is never above it
(`WordType.exists_cutoff_forall_pow_le_card_proportionalTypeClass` is the committed shape for that
situation).  So no statement of this kind can be exact, and the published value has to be shaved by
some positive `eps`, exactly as the orbit certificates shave `dwz112LogValue` by an explicit
reserve (`log_dwz112LeafTerm_eq`, `Examples/DuanWuZhouLevelTwoLeafTauWeight.lean`) before
`dwz63_exists_orbitCertificates` consumes them.

Unlike that chain, `eps` is left as a **parameter** here rather than fixed to a round constant.
The reason is that the section 6.3 endpoint's whole slack is `1.7246e-7` nats per letter and it has
to be divided among the cells that need a deficit; a constant chosen here would silently claim a
share of that budget.  A client picks `eps` and pays for it, and the statement is strictly more
general than any fixed choice.  The translation is
`lowerBase = exp (mass * H - mass * eps / tau)`, so a deficit of `eps` per letter in the value
costs `mass * eps / tau` in the base.

## The nine cells

Zero leg, degree and value per cell are tabulated in
`Examples/DuanWuZhouLevelTwoFineCellRows.lean`.  Rows `5`, `12`, `14` are definitionally rows `1`,
`3`, `4`, so their rate bridges are the same terms; the instances below use them directly.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

/-! ## Two arithmetic steps -/

/-- The one-slice exponent scales with the period. -/
theorem dwz63_middleCountSum_proportional (a : PositiveWord CWBlock 1 → ℕ) (j : ℕ) :
    (∑ p : PositiveWord CWBlock 1,
        WordType.proportionalCounts a j p * cwWordMiddleCount 1 p) =
      (∑ p : PositiveWord CWBlock 1, a p * cwWordMiddleCount 1 p) * j := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [WordType.proportionalCounts]
  ring

/-- `2 ^ (m * H_bits) = exp (m * H_nats)`: the base-two entropy in the shape the counting lemma
takes, against the natural-log entropy the value atoms use. -/
theorem dwz63_two_rpow_profileEntropyBits {I : Type*} [Fintype I] (a : I → ℕ) (m : ℝ) :
    (2 : ℝ) ^ (m * WordType.profileEntropyBits a) =
      Real.exp (m * WordType.profileEntropyNats a) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [WordType.profileEntropyBits, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  field_simp

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## The weight at the published value -/

/-- **A zero-coordinate cell, weighed at its published value less an arbitrary positive
deficit.**

Everything about the cell enters through four data: the leg carrying its zero coordinate, the
coarse degree `k` of its split row, the row's mass, and the rate bridge `hrate` identifying
`tau` times the row's rate with `mass * logVal`.  The conclusion is a region's `value` field at
the period `mass * j`. -/
theorem dwz63_exists_fineCellWeight_logVal (zero : Leg) (hzero : zero ≠ Leg.Z) (k : Fin 5)
    (hq : 0 < q)
    (a : PositiveWord CWBlock 1 → ℕ) (mass : ℕ)
    (hmasseq : WordType.profileMass a = mass) (hmass0 : 0 < mass)
    (ha : ∀ p : PositiveWord CWBlock 1, a p ≠ 0 → cwSquareBlockDegree p = k)
    (logVal : ℝ)
    (hrate : dwz63Tau * ((WordType.profileMass a : ℝ) * WordType.profileEntropyNats a
        + ((∑ p : PositiveWord CWBlock 1, a p * cwWordMiddleCount 1 p : ℕ) : ℝ) *
          Real.log q) = (WordType.profileMass a : ℝ) * logVal)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = mass * j →
      HasTauWeight K
        ((((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts a j))
          (dwz63ZeroCellTarget zero k n)).realize) dwz63Tau
        (Real.exp ((mass : ℝ) * (j : ℝ) * (logVal - ε))) := by
  classical
  have htau : (0 : ℝ) < dwz63Tau := by norm_num [dwz63Tau]
  have hmassR : (0 : ℝ) < (mass : ℝ) := by exact_mod_cast hmass0
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set ones := (∑ p : PositiveWord CWBlock 1, a p * cwWordMiddleCount 1 p) with honesDef
  set H := WordType.profileEntropyNats a with hHdef
  set δ := (mass : ℝ) * ε / dwz63Tau with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hτδ : dwz63Tau * δ = (mass : ℝ) * ε := by
    rw [hδdef]
    field_simp
  set lowerBase := Real.exp ((mass : ℝ) * H - δ) with hbaseDef
  have hlower : 0 < lowerBase := by rw [hbaseDef]; exact Real.exp_pos _
  have hlt : lowerBase <
      (2 : ℝ) ^ ((WordType.profileMass a : ℝ) * WordType.profileEntropyBits a) := by
    rw [dwz63_two_rpow_profileEntropyBits, hmasseq, ← hHdef, hbaseDef]
    exact Real.exp_lt_exp.mpr (by linarith)
  obtain ⟨N, hN⟩ := dwz63_exists_zeroFineCellWeight K q zero hzero k hq a
    (by rw [hmasseq]; exact hmass0) ha dwz63Tau (le_of_lt htau) hlower hlt
  refine ⟨N, fun j hj n hn ↦ ?_⟩
  have hweight := hN j hj n (by rw [hmasseq]; exact hn)
  have hqpow : ((q : ℝ) ^ ones) = Real.exp ((ones : ℝ) * Real.log q) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hval : (lowerBase ^ j *
      ((q ^ (∑ p : PositiveWord CWBlock 1,
        WordType.proportionalCounts a j p * cwWordMiddleCount 1 p) : ℕ) : ℝ)) ^ dwz63Tau =
      Real.exp ((mass : ℝ) * (j : ℝ) * (logVal - ε)) := by
    rw [dwz63_middleCountSum_proportional, ← honesDef, Nat.cast_pow, pow_mul, hqpow, hbaseDef,
      ← mul_pow, ← Real.exp_add, ← Real.exp_nat_mul,
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    have hrateM := hrate
    rw [hmasseq] at hrateM
    linear_combination (j : ℝ) * hrateM - (j : ℝ) * hτδ
  rw [← hval]
  exact hweight

/-! ## The nine cells

Each is one application of the theorem above.  Rows `5`, `12` and `14` are definitionally rows `1`,
`3` and `4`, so their rate bridges are literally the same proofs. -/

/-- The `(0,0,4)` cell, at `dwz63LogVal004` less an arbitrary positive deficit. -/
theorem dwz63_exists_fineCellWeight_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = 200000000 * j →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 0) j))
          (dwz63ZeroCellTarget Leg.X 4 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal004 - ε))) :=
  dwz63_exists_fineCellWeight_logVal K dwz63Q Leg.X (by decide) 4 (by norm_num [dwz63Q])
    (dwz63AlphaTilde 0) 200000000 (dwz63_profileMass_alphaTilde 0) (by norm_num)
    dwz63_alphaTildeDegree_zero dwz63LogVal004 dwz63_tau_mul_rate_eq_alphaTilde_zero ε hε

/-- The `(0,1,3)` cell, at `dwz63LogVal013` less an arbitrary positive deficit. -/
theorem dwz63_exists_fineCellWeight_one (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = 200000000 * j →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 1) j))
          (dwz63ZeroCellTarget Leg.X 3 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal013 - ε))) :=
  dwz63_exists_fineCellWeight_logVal K dwz63Q Leg.X (by decide) 3 (by norm_num [dwz63Q])
    (dwz63AlphaTilde 1) 200000000 (dwz63_profileMass_alphaTilde 1) (by norm_num)
    dwz63_alphaTildeDegree_one dwz63LogVal013 dwz63_tau_mul_rate_eq_alphaTilde_one ε hε

/-- The `(0,2,2)` cell, at `dwz63LogVal022` less an arbitrary positive deficit. -/
theorem dwz63_exists_fineCellWeight_two (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = 200000000 * j →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 2) j))
          (dwz63ZeroCellTarget Leg.X 2 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal022 - ε))) :=
  dwz63_exists_fineCellWeight_logVal K dwz63Q Leg.X (by decide) 2 (by norm_num [dwz63Q])
    (dwz63AlphaTilde 2) 200000000 (dwz63_profileMass_alphaTilde 2) (by norm_num)
    dwz63_alphaTildeDegree_two dwz63LogVal022 dwz63_tau_mul_rate_eq_alphaTilde_two ε hε

/-- The `(0,3,1)` cell, at `dwz63LogVal013` less an arbitrary positive deficit. -/
theorem dwz63_exists_fineCellWeight_three (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = 200000000 * j →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 3) j))
          (dwz63ZeroCellTarget Leg.X 1 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal013 - ε))) :=
  dwz63_exists_fineCellWeight_logVal K dwz63Q Leg.X (by decide) 1 (by norm_num [dwz63Q])
    (dwz63AlphaTilde 3) 200000000 (dwz63_profileMass_alphaTilde 3) (by norm_num)
    dwz63_alphaTildeDegree_three dwz63LogVal013 dwz63_tau_mul_rate_eq_alphaTilde_three ε hε

/-- The `(0,4,0)` cell, at `dwz63LogVal004` less an arbitrary positive deficit. -/
theorem dwz63_exists_fineCellWeight_four (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = 200000000 * j →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 4) j))
          (dwz63ZeroCellTarget Leg.X 0 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal004 - ε))) :=
  dwz63_exists_fineCellWeight_logVal K dwz63Q Leg.X (by decide) 0 (by norm_num [dwz63Q])
    (dwz63AlphaTilde 4) 200000000 (dwz63_profileMass_alphaTilde 4) (by norm_num)
    dwz63_alphaTildeDegree_four dwz63LogVal004 dwz63_tau_mul_rate_eq_alphaTilde_four ε hε

/-- The `(1,0,3)` cell, at `dwz63LogVal013` less an arbitrary positive deficit. -/
theorem dwz63_exists_fineCellWeight_five (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = 200000000 * j →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 5) j))
          (dwz63ZeroCellTarget Leg.Y 3 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal013 - ε))) :=
  dwz63_exists_fineCellWeight_logVal K dwz63Q Leg.Y (by decide) 3 (by norm_num [dwz63Q])
    (dwz63AlphaTilde 5) 200000000 (dwz63_profileMass_alphaTilde 5) (by norm_num)
    dwz63_alphaTildeDegree_five dwz63LogVal013 dwz63_tau_mul_rate_eq_alphaTilde_one ε hε

/-- The `(2,0,2)` cell, at `dwz63LogVal022` less an arbitrary positive deficit. -/
theorem dwz63_exists_fineCellWeight_nine (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = 200000000 * j →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 9) j))
          (dwz63ZeroCellTarget Leg.Y 2 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal022 - ε))) :=
  dwz63_exists_fineCellWeight_logVal K dwz63Q Leg.Y (by decide) 2 (by norm_num [dwz63Q])
    (dwz63AlphaTilde 9) 200000000 (dwz63_profileMass_alphaTilde 9) (by norm_num)
    dwz63_alphaTildeDegree_nine dwz63LogVal022 dwz63_tau_mul_rate_eq_alphaTilde_nine ε hε

/-- The `(3,0,1)` cell, at `dwz63LogVal013` less an arbitrary positive deficit. -/
theorem dwz63_exists_fineCellWeight_twelve (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = 200000000 * j →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 12) j))
          (dwz63ZeroCellTarget Leg.Y 1 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal013 - ε))) :=
  dwz63_exists_fineCellWeight_logVal K dwz63Q Leg.Y (by decide) 1 (by norm_num [dwz63Q])
    (dwz63AlphaTilde 12) 200000000 (dwz63_profileMass_alphaTilde 12) (by norm_num)
    dwz63_alphaTildeDegree_twelve dwz63LogVal013 dwz63_tau_mul_rate_eq_alphaTilde_three ε hε

/-- The `(4,0,0)` cell, at `dwz63LogVal004` less an arbitrary positive deficit. -/
theorem dwz63_exists_fineCellWeight_fourteen (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = 200000000 * j →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 14) j))
          (dwz63ZeroCellTarget Leg.Y 0 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal004 - ε))) :=
  dwz63_exists_fineCellWeight_logVal K dwz63Q Leg.Y (by decide) 0 (by norm_num [dwz63Q])
    (dwz63AlphaTilde 14) 200000000 (dwz63_profileMass_alphaTilde 14) (by norm_num)
    dwz63_alphaTildeDegree_fourteen dwz63LogVal004 dwz63_tau_mul_rate_eq_alphaTilde_four ε hε

end AlgebraicComplexity.Examples
