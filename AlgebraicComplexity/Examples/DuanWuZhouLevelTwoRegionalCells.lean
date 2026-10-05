/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoRegionalCellEntry
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellOrbit
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellTwoTwoZero
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainLeafValue

set_option autoImplicit false

/-!
# The fifteen region entries of the section 6.3 leaf

Layer 4 (`AlgebraicComplexity/Examples/`).  `segmentedRegionalSymSixWeights_of_letterwise`
(`MatrixMultiplication/SegmentedRegionalAssembly.lean`) needs one `sym₆`-weight per region, at the
uniform coarse target `dwz63CellTarget`.  This module produces all fifteen at the joined period
`2 * 10 ^ 8 * (dwz63Alpha t * s)`.

## Where each of the fifteen comes from

* Eleven zero-coordinate rows (`0,1,2,3,4,5,8,9,12,13,14`) --- image 98's
  `dwz63_exists_joinedFineCellWeight_…`, already at the joined period.
* Row `11`, `(2,2,0)` --- image 103's `dwz63_exists_fineCellWeight_eleven`, exact at every period,
  read at `j = dwz63Alpha 11 * s`.
* Rows `6`, `7`, `10`, the orbit --- **hypotheses**, in image 104's `hcut` shape: an eventual
  `sym₃` weight on `dwz63OrbitRegion`.  They are hypotheses because the `112`/`121` certificate
  chains reach those rows only *cofinally*, at their own periods; the assembly therefore states
  them at the exact `j = dwz63Alpha (dwz63OrbitRow o) * s` it needs, leaving the admissible
  sub-lattice of scales to the client (`dwz63AdmissibleScale` records one).

Everything else --- the twelve proved rows --- holds at every period beyond its own cutoff, so the
sub-lattice costs nothing there.

## The uniform coarse spelling

`dwz63CellTarget` (image 105) is `dwz63ZeroCellTarget` at the twelve zero-coordinate rows and
`dwz63OrbitTarget` at the three orbit rows (`dwz63CellTarget_orbit`, via image 104's
`dwz63OrbitTarget_eq_component` and `dwz63Cell_eq_dwz63Component`), so the fifteen entries are
listed with no case split on which route weighed the cell.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K]

/-! ## The two missing coarse-target identities -/

/-- Row `11`'s coarse target, completing image 105's eleven. -/
theorem dwz63CellTarget_eleven (n : ℕ) : dwz63CellTarget 11 n = dwz63ZeroCellTarget Leg.Z 2 n :=
  dwz63CellTarget_eq_zeroCellTarget 11 Leg.Z 2 n (fun c ↦ by cases c <;> rfl)

/-- **The orbit spelling bridge**, absorbed on this side as the coordinator ruled: the uniform
`dwz63CellTarget` at an orbit row is image 104's `dwz63OrbitTarget`. -/
theorem dwz63CellTarget_orbit (o : Fin 3) (n : ℕ) :
    dwz63CellTarget (dwz63OrbitRow o) n = dwz63OrbitTarget o n := by
  funext c
  rw [dwz63OrbitTarget_eq_component]
  show positiveWordConst (dwz63Cell (dwz63OrbitRow o) c) n = _
  rw [dwz63Cell_eq_dwz63Component]

/-! ## The region value -/

/-- The `tau`-weight the region of cell `t` carries at scale `s` and per-letter deficit `ε`. -/
noncomputable def dwz63RegionValue (t : Fin 15) (s : ℕ) (ε : ℝ) : ℝ :=
  Real.exp ((200000000 : ℝ) * ((dwz63Alpha t * s : ℕ) : ℝ)
    * (dwz63LogValComponent t - ε)) ^ 6

/-! ## The fifteen entries -/

/-- The `sym₆` region entry of an orbit row, from image 104's `sym₃` obligation at the exact
period the assembly needs. -/
theorem dwz63_symSix_regionEntry_orbit (o : Fin 3) (n j : ℕ) (ε : ℝ)
    (hcut : HasTauWeight K
      (symThree K (dwz63OrbitRegion K dwz63Q o (dwz63OrbitRow o) n j).realize) dwz63Tau
      (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63OrbitLogVal o - ε)) ^ 3)) :
    HasTauWeight K
      (symSix K ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 15 (fun _ ↦ dwz63OrbitRow o)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
          (fun t ↦ if t = dwz63OrbitRow o then
            WordType.proportionalCounts (dwz63AlphaTilde (dwz63OrbitRow o)) j else 0))
        (dwz63CellTarget (dwz63OrbitRow o) n)).realize)) dwz63Tau
      (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63OrbitLogVal o - ε)) ^ 6) := by
  have h := dwz63_symSix_orbitRegionEntry_of_symThree K dwz63Q o (dwz63OrbitRow o) n j
    (by positivity) hcut
  rw [← pow_mul] at h
  rw [dwz63CellTarget_orbit]
  exact h


/-- **The region entry of one cell**, at the joined period.

The three orbit rows are the hypothesis `hcut`, in image 104's shape and at the exact period the
assembly needs; the other twelve are proved. -/
theorem dwz63_exists_symSix_regionEntry_cell (ε : ℝ) (hε : 0 < ε) (t : Fin 15) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
      (∀ (o : Fin 3) (m : ℕ), m + 1 = 200000000 * (dwz63Alpha (dwz63OrbitRow o) * s) →
        HasTauWeight K (symThree K (dwz63OrbitRegion K dwz63Q o (dwz63OrbitRow o) m
          (dwz63Alpha (dwz63OrbitRow o) * s)).realize) dwz63Tau
          (Real.exp ((200000000 : ℝ) * ((dwz63Alpha (dwz63OrbitRow o) * s : ℕ) : ℝ)
            * (dwz63OrbitLogVal o - ε)) ^ 3)) →
      ∀ n : ℕ, n + 1 = 200000000 * (dwz63Alpha t * s) →
        HasTauWeight K
          (symSix K ((((cwPartitionedTensor K dwz63Q).positivePower
              1).segmentedLocalizedSplittingPower
            cwSquareDegreeMap n 15 (fun _ ↦ t)
            (SegmentedSplitRestriction.ofLeg
              (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
              (fun t' ↦ if t' = t then
                WordType.proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s) else 0))
            (dwz63CellTarget t n)).realize)) dwz63Tau (dwz63RegionValue t s ε) := by
  fin_cases t
  · obtain ⟨N, hN⟩ := dwz63_exists_joinedFineCellWeight_zero (K := K) ε hε
    refine ⟨N, fun s hs _ n hn ↦ ?_⟩
    exact dwz63_symSixRegionEntry_of_oneSegmentWeight K (0 : Fin 15) 0 Leg.X 4 n _ _
      (Real.exp_pos _).le (dwz63CellTarget_zero n) (hN s hs n hn)
  · obtain ⟨N, hN⟩ := dwz63_exists_joinedFineCellWeight_one (K := K) ε hε
    refine ⟨N, fun s hs _ n hn ↦ ?_⟩
    exact dwz63_symSixRegionEntry_of_oneSegmentWeight K (1 : Fin 15) 1 Leg.X 3 n _ _
      (Real.exp_pos _).le (dwz63CellTarget_one n) (hN s hs n hn)
  · obtain ⟨N, hN⟩ := dwz63_exists_joinedFineCellWeight_two (K := K) ε hε
    refine ⟨N, fun s hs _ n hn ↦ ?_⟩
    exact dwz63_symSixRegionEntry_of_oneSegmentWeight K (2 : Fin 15) 2 Leg.X 2 n _ _
      (Real.exp_pos _).le (dwz63CellTarget_two n) (hN s hs n hn)
  · obtain ⟨N, hN⟩ := dwz63_exists_joinedFineCellWeight_three (K := K) ε hε
    refine ⟨N, fun s hs _ n hn ↦ ?_⟩
    exact dwz63_symSixRegionEntry_of_oneSegmentWeight K (3 : Fin 15) 3 Leg.X 1 n _ _
      (Real.exp_pos _).le (dwz63CellTarget_three n) (hN s hs n hn)
  · obtain ⟨N, hN⟩ := dwz63_exists_joinedFineCellWeight_four (K := K) ε hε
    refine ⟨N, fun s hs _ n hn ↦ ?_⟩
    exact dwz63_symSixRegionEntry_of_oneSegmentWeight K (4 : Fin 15) 4 Leg.X 0 n _ _
      (Real.exp_pos _).le (dwz63CellTarget_four n) (hN s hs n hn)
  · obtain ⟨N, hN⟩ := dwz63_exists_joinedFineCellWeight_five (K := K) ε hε
    refine ⟨N, fun s hs _ n hn ↦ ?_⟩
    exact dwz63_symSixRegionEntry_of_oneSegmentWeight K (5 : Fin 15) 5 Leg.Y 3 n _ _
      (Real.exp_pos _).le (dwz63CellTarget_five n) (hN s hs n hn)
  · refine ⟨0, fun s _ hcut n hn ↦ ?_⟩
    exact dwz63_symSix_regionEntry_orbit K 0 n (dwz63Alpha 6 * s) ε (hcut 0 n hn)
  · refine ⟨0, fun s _ hcut n hn ↦ ?_⟩
    exact dwz63_symSix_regionEntry_orbit K 1 n (dwz63Alpha 7 * s) ε (hcut 1 n hn)
  · obtain ⟨N, hN⟩ := dwz63_exists_joinedFineCellWeight_eight (K := K) ε hε
    refine ⟨N, fun s hs _ n hn ↦ ?_⟩
    exact dwz63_symSixRegionEntry_of_oneSegmentWeight K (8 : Fin 15) 8 Leg.Z 3 n _ _
      (Real.exp_pos _).le (dwz63CellTarget_eight n) (hN s hs n hn)
  · obtain ⟨N, hN⟩ := dwz63_exists_joinedFineCellWeight_nine (K := K) ε hε
    refine ⟨N, fun s hs _ n hn ↦ ?_⟩
    exact dwz63_symSixRegionEntry_of_oneSegmentWeight K (9 : Fin 15) 9 Leg.Y 2 n _ _
      (Real.exp_pos _).le (dwz63CellTarget_nine n) (hN s hs n hn)
  · refine ⟨0, fun s _ hcut n hn ↦ ?_⟩
    exact dwz63_symSix_regionEntry_orbit K 2 n (dwz63Alpha 10 * s) ε (hcut 2 n hn)
  · obtain ⟨N, hN⟩ := dwz63_exists_fineCellWeight_eleven (K := K) ε hε
    refine ⟨N, fun s hs _ n hn ↦ ?_⟩
    exact dwz63_symSixRegionEntry_of_oneSegmentWeight K (11 : Fin 15) 11 Leg.Z 2 n _ _
      (Real.exp_pos _).le (dwz63CellTarget_eleven n)
      (hN (dwz63Alpha 11 * s)
        (le_trans hs (Nat.le_mul_of_pos_left s
          (by rw [show dwz63Alpha 11 = 10045791 from rfl]; norm_num))) n hn)
  · obtain ⟨N, hN⟩ := dwz63_exists_joinedFineCellWeight_twelve (K := K) ε hε
    refine ⟨N, fun s hs _ n hn ↦ ?_⟩
    exact dwz63_symSixRegionEntry_of_oneSegmentWeight K (12 : Fin 15) 12 Leg.Y 1 n _ _
      (Real.exp_pos _).le (dwz63CellTarget_twelve n) (hN s hs n hn)
  · obtain ⟨N, hN⟩ := dwz63_exists_joinedFineCellWeight_thirteen (K := K) ε hε
    refine ⟨N, fun s hs _ n hn ↦ ?_⟩
    exact dwz63_symSixRegionEntry_of_oneSegmentWeight K (13 : Fin 15) 13 Leg.Z 1 n _ _
      (Real.exp_pos _).le (dwz63CellTarget_thirteen n) (hN s hs n hn)
  · obtain ⟨N, hN⟩ := dwz63_exists_joinedFineCellWeight_fourteen (K := K) ε hε
    refine ⟨N, fun s hs _ n hn ↦ ?_⟩
    exact dwz63_symSixRegionEntry_of_oneSegmentWeight K (14 : Fin 15) 14 Leg.Y 0 n _ _
      (Real.exp_pos _).le (dwz63CellTarget_fourteen n) (hN s hs n hn)

/-- **All fifteen region entries with a common cutoff.**  The cutoff is the supremum of the twelve
proved cells' cutoffs; the three orbit rows contribute none, being hypotheses at the exact
period. -/
theorem dwz63_exists_symSix_regionEntry_cells (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
      (∀ (o : Fin 3) (m : ℕ), m + 1 = 200000000 * (dwz63Alpha (dwz63OrbitRow o) * s) →
        HasTauWeight K (symThree K (dwz63OrbitRegion K dwz63Q o (dwz63OrbitRow o) m
          (dwz63Alpha (dwz63OrbitRow o) * s)).realize) dwz63Tau
          (Real.exp ((200000000 : ℝ) * ((dwz63Alpha (dwz63OrbitRow o) * s : ℕ) : ℝ)
            * (dwz63OrbitLogVal o - ε)) ^ 3)) →
      ∀ (t : Fin 15) (n : ℕ), n + 1 = 200000000 * (dwz63Alpha t * s) →
        HasTauWeight K
          (symSix K ((((cwPartitionedTensor K dwz63Q).positivePower
              1).segmentedLocalizedSplittingPower
            cwSquareDegreeMap n 15 (fun _ ↦ t)
            (SegmentedSplitRestriction.ofLeg
              (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
              (fun t' ↦ if t' = t then
                WordType.proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s) else 0))
            (dwz63CellTarget t n)).realize)) dwz63Tau (dwz63RegionValue t s ε) := by
  choose N hN using dwz63_exists_symSix_regionEntry_cell K ε hε
  exact ⟨Finset.univ.sup N, fun s hs hcut t n hn ↦
    hN t s (le_trans (Finset.le_sup (Finset.mem_univ t)) hs) hcut n hn⟩


/-! ## The value the fifteen regions deliver -/

/-- The exponent of one region's weight: `dwz63RegionValue t s ε = exp (…) ^ 6`. -/
noncomputable def dwz63RegionExponent (t : Fin 15) (s : ℕ) (ε : ℝ) : ℝ :=
  (200000000 : ℝ) * ((dwz63Alpha t * s : ℕ) : ℝ) * (dwz63LogValComponent t - ε)

theorem dwz63RegionValue_eq_exp (t : Fin 15) (s : ℕ) (ε : ℝ) :
    dwz63RegionValue t s ε = Real.exp (dwz63RegionExponent t s ε) ^ 6 := rfl

/-- The fifteen masses sum to `10 ^ 8`, over the reals. -/
theorem dwz63_sum_alphaCast : ∑ t : Fin 15, (dwz63Alpha t : ℝ) = 100000000 := by
  simp only [dwz63Alpha, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  norm_num

/-- **The fifteen regional exponents sum to the whole word's `dwz63LogVal` rate, less the
deficit.**  This is `dwz63_logVal_eq_sum` read at the joined period: the `alpha`-weighted sum of
the component logarithms is `10 ^ 8 * dwz63LogVal`, and the masses sum to `10 ^ 8`, so the deficit
enters once per letter. -/
theorem dwz63_sum_regionExponent (s : ℕ) (ε : ℝ) :
    ∑ t : Fin 15, dwz63RegionExponent t s ε
      = 20000000000000000 * (s : ℝ) * (dwz63LogVal - ε) := by
  have hlog : ∑ t : Fin 15, (dwz63Alpha t : ℝ) * dwz63LogValComponent t
      = 100000000 * dwz63LogVal := by
    rw [← dwz63_sum_alpha_mul_log]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [log_dwz63Val]
  have hsplit : ∑ t : Fin 15, dwz63RegionExponent t s ε
      = (200000000 : ℝ) * (s : ℝ) *
        (∑ t : Fin 15, (dwz63Alpha t : ℝ) * dwz63LogValComponent t)
        - (200000000 : ℝ) * (s : ℝ) * ε * ∑ t : Fin 15, (dwz63Alpha t : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    unfold dwz63RegionExponent
    push_cast
    ring
  rw [hsplit, hlog, dwz63_sum_alphaCast]
  ring

/-- The whole word carries `20000000000000000 * s` letters at the joined period. -/
theorem dwz63_leafValue_eq (n s : ℕ) (ε : ℝ) (hn : n + 1 = 20000000000000000 * s) :
    Real.exp (∑ t : Fin 15, dwz63RegionExponent t s ε) ^ 6
      = Real.exp (((n : ℝ) + 1) * (dwz63LogVal - ε)) ^ 6 := by
  rw [dwz63_sum_regionExponent]
  have hcast : ((n : ℝ) + 1) = 20000000000000000 * (s : ℝ) := by
    have hc := congrArg (fun m : ℕ ↦ (m : ℝ)) hn
    push_cast at hc
    linarith
  rw [hcast]

/-- The endpoint's demand, as one exponential. -/
theorem dwz63_expLogVal_pow_eq_expMul (n : ℕ) :
    Real.exp dwz63LogVal ^ (6 * (n + 1)) = Real.exp (((n : ℝ) + 1) * dwz63LogVal) ^ 6 := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **The deficit is a real loss against the endpoint's demand.**

`omega_lt_2374631_of_plainBatchedStageAndLeaf`'s `hleafValue` binder asks for
`exp dwz63LogVal ^ (6 * (n + 1))` and the fifteen regions deliver
`exp ((n + 1) * (dwz63LogVal - ε)) ^ 6`, which is **strictly smaller** for every positive `ε`.
`dwz63_logVal_eq_sum` is an *equality*, so the fifteen cells at their published values reproduce
`dwz63LogVal` exactly and leave no room: the published `1.7446 * 10 ^ (-7)` slack of section 6.3 is
spent inside the constants, not available at this binder. -/
theorem dwz63_regionProduct_lt_required (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Real.exp (((n : ℝ) + 1) * (dwz63LogVal - ε)) ^ 6 < Real.exp dwz63LogVal ^ (6 * (n + 1)) := by
  rw [dwz63_expLogVal_pow_eq_expMul]
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine pow_lt_pow_left₀ ?_ (Real.exp_pos _).le (by norm_num)
  refine Real.exp_lt_exp.mpr ?_
  nlinarith

end AlgebraicComplexity.Examples
