/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoTripleEntropy
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobalArithmetic

set_option autoImplicit false

/-!
# `Dwz63TripleEntropyBound`, discharged

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoCounting.lean` states
`Dwz63TripleEntropyBound` and calls it "the only genuinely new mathematics the count side of
section 6.3 needs": every fifteen-cell type sharing `alpha`'s three coordinate marginals has
entropy at most `H(alpha) + log K`, `K = 1 + 10 ^ (-10)`.
`Examples/DuanWuZhouLevelTwoTripleEntropy.lean` supplies the first half — the reading of the Gibbs
witness — and its docstring names the second half as the missing piece:

> The second half is the entropy comparison: that the dual gap `log W - E_alpha[s] - H(alpha)` is
> the committed constant `dwz63GibbsDeficit` … That gap identity has been verified exactly in
> rational arithmetic outside Lean … but it is not formalized here.

This module formalizes that gap identity and composes the four pieces.

## The chain

For a competitor type `q` of mass `10 ^ 8 · k` sharing `alpha`'s three marginals:

* `H(q) ≤ log W − E_q[s]` — weak duality,
  `Probability/MaximumEntropyDual.entropy_le_logPartition_sub_expectation`, at the score
  `dwz63GibbsScore` whose partition function is the committed `dwz63_partitionSum_eq`
  (`dwz63_partition_dwz63GibbsScore`);
* `E_q[s] = E_alpha[s]` — `coordinateScore_expectation` together with `marginal_div_profileMass`:
  a coordinate-potential expectation sees a profile only through its three marginals, and `q` and
  `alpha` have the same ones by hypothesis;
* `log W − E_alpha[s] = H(alpha) + dwz63GibbsDeficit` — `dwz63_logPartition_sub_alphaScore`, the
  gap identity, proved here;
* `dwz63GibbsDeficit ≤ log K` — the committed numeric certificate
  `dwz63_gibbsDeficit_le_log_hashLossMultiplier`.

## The gap identity, term by term

`log W − E_alpha[s] − H(alpha) = log W + Σ_c p_c · log (p_c / (u_i v_j w_k))` with
`p_c = alpha(c) / 10 ^ 8`, and every one of the sixteen resulting terms is one of
`dwz63GibbsDeficit`'s sixteen, in exact rational arithmetic: the fifteen cell terms match one for
one — `dwz63GibbsCellTerm` records the matching, cell by cell, in the deficit's own spelling —
and the sixteenth is `log W` itself (`−log (250000000000000000 / 249999816060193851)`).  Five
cells --- rows `0`, `1`, `2`, `8`, `13` --- have `p_c < u_i v_j w_k`, and `dwz63GibbsDeficit`
writes those with a negated coefficient and an inverted argument; `dwz63_gibbsCellInv` is that
reading.  Nothing here is an enclosure: every step is an exact rational identity closed by
`norm_num`, and the only inequality used is the committed certificate.

Primary source: `[duan2023faster]`, arXiv:2210.10173.  The certificate spans two sections: the
general fixed-marginal argument it discharges is `lem:numtriple_singledist`,
`papers/sources/2210.10173/hashing.tex:63-70`, used in the section 6.2 analysis at
`papers/sources/2210.10173/global_value.tex:292-323`; the fifteen-cell numbers it is calibrated
against are the section 6.3 level-two example (Table 2), `global_value.tex:350-375`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity WordType

open scoped BigOperators

/-! ## One cell of the dual gap -/

/-- `p log p − p log g = p log (p / g)`, the shape a cell with `p ≥ g` takes. -/
theorem dwz63_gibbsCell {p g r : ℝ} (hp : p ≠ 0) (hg : g ≠ 0) (hr : p / g = r) :
    p * Real.log p - p * Real.log g = p * Real.log r := by
  rw [← hr, Real.log_div hp hg]
  ring

/-- The same with the argument inverted, the shape a cell with `p < g` takes in
`dwz63GibbsDeficit`'s own spelling. -/
theorem dwz63_gibbsCellInv {p g r : ℝ} (hp : p ≠ 0) (hg : g ≠ 0) (hr : g / p = r) :
    p * Real.log p - p * Real.log g = -(p * Real.log r) := by
  rw [← hr, Real.log_div hg hp]
  ring

/-- The coordinate score is the logarithm of the product weight. -/
theorem dwz63_gibbsScore_eq_log (c : Fin 15) :
    dwz63GibbsScore c =
      Real.log (dwz63GibbsX (dwz63XIndex c) * dwz63GibbsY (dwz63YIndex c) *
        dwz63GibbsZ (dwz63ZIndex c)) := by
  unfold dwz63GibbsScore MaximumEntropyDual.coordinateScore
  rw [Real.log_mul (mul_pos (dwz63GibbsX_pos _) (dwz63GibbsY_pos _)).ne'
      (dwz63GibbsZ_pos _).ne',
    Real.log_mul (dwz63GibbsX_pos _).ne' (dwz63GibbsY_pos _).ne']

/-- The score expectation, as the three marginal pairings, by
`MaximumEntropyDual.coordinateScore_expectation`; stated separately so that the one delta step
unfolding `dwz63GibbsScore` happens against a fixed expected type rather than inside a `rfl`. -/
theorem dwz63_gibbsScore_expectation (r : Fin 15 → ℝ) :
    ∑ c, r c * dwz63GibbsScore c =
      (∑ x, Real.log (dwz63GibbsX x) * MaximumEntropyDual.marginal dwz63XIndex r x) +
      (∑ y, Real.log (dwz63GibbsY y) * MaximumEntropyDual.marginal dwz63YIndex r y) +
      (∑ z, Real.log (dwz63GibbsZ z) * MaximumEntropyDual.marginal dwz63ZIndex r z) :=
  MaximumEntropyDual.coordinateScore_expectation _ _ _ r _ _ _

/-! ## The fifteen cell terms of `dwz63GibbsDeficit` -/

/-- **The `c`-th cell term of `dwz63GibbsDeficit`**, in the deficit's own spelling: coefficient
`alpha(c) / 10 ^ 8` reduced, and the argument `p_c / (u_i v_j w_k)` — inverted, with the sign
flipped, on the five cells where that ratio is below one, rows `0`, `1`, `2`, `8` and `13`. -/
noncomputable def dwz63GibbsCellTerm : Fin 15 → ℝ :=
  ![-(20860 / 100000000 * Real.log (1490051696823 / 1490000000000)),
    -(1211153 / 100000000 * Real.log (75697153534023 / 75697062500000)),
    -(10366945 / 100000000 * Real.log (3239676929105477 / 3239670312500000)),
    1333318 / 100000000 * Real.log (29761562500000 / 29761433689713),
    24731 / 100000000 * Real.log (552031250000 / 552020398401),
    1211153 / 100000000 * Real.log (1211153000000000 / 1211152565099421),
    20088623 / 100000000 * Real.log (25110778750000000 / 25110739931247103),
    20734458 / 100000000 * Real.log (12959036250000000 / 12959028326673737),
    -(1251758 / 100000000 * Real.log (391174889585529 / 391174375000000)),
    10366945 / 100000000 * Real.log (103669450000000000 / 103669436050005141),
    20734458 / 100000000 * Real.log (8639357500000000 / 8639346902497641),
    10045791 / 100000000 * Real.log (697624375000000 / 697623226254687),
    1333318 / 100000000 * Real.log (13333180000000000 / 13333158315186897),
    -(1251758 / 100000000 * Real.log (1564706229284909 / 1564697500000000)),
    24731 / 100000000 * Real.log (30913750000000 / 30901755043599)]

set_option maxRecDepth 8000 in
/-- **Each cell's dual-gap contribution is the corresponding term of `dwz63GibbsDeficit`.**

Proof sketch: rewrite the score as `log (u_i v_j w_k)` (`dwz63_gibbsScore_eq_log`) and split on
the cell.  Each branch is `p log p − p log g` at explicit rationals: `dwz63_gibbsCell` when
`p ≥ g` (ten cells), `dwz63_gibbsCellInv` when `p < g` (rows `0`, `1`, `2`, `8`, `13`).  Their
side conditions `p ≠ 0`, `g ≠ 0` and the exact ratio are closed by `norm_num` on rational
literals; nothing is enclosed, and the case split is over `Fin 15`, not a tensor-level type. -/
theorem dwz63_gibbsCellTerm_eq (c : Fin 15) :
    ((dwz63Alpha c : ℝ) / 100000000) * Real.log ((dwz63Alpha c : ℝ) / 100000000) -
        ((dwz63Alpha c : ℝ) / 100000000) * dwz63GibbsScore c =
      dwz63GibbsCellTerm c := by
  rw [dwz63_gibbsScore_eq_log]
  fin_cases c <;>
    simp only [dwz63Alpha, dwz63XIndex, dwz63YIndex, dwz63ZIndex, dwz63GibbsCellTerm,
      dwz63GibbsX, dwz63GibbsY, dwz63GibbsZ, Fin.isValue]
  · refine dwz63_gibbsCellInv ?_ ?_ ?_ <;> norm_num
  · refine dwz63_gibbsCellInv ?_ ?_ ?_ <;> norm_num
  · refine dwz63_gibbsCellInv ?_ ?_ ?_ <;> norm_num
  · refine dwz63_gibbsCell ?_ ?_ ?_ <;> norm_num
  · refine dwz63_gibbsCell ?_ ?_ ?_ <;> norm_num
  · refine dwz63_gibbsCell ?_ ?_ ?_ <;> norm_num
  · refine dwz63_gibbsCell ?_ ?_ ?_ <;> norm_num
  · refine dwz63_gibbsCell ?_ ?_ ?_ <;> norm_num
  · refine dwz63_gibbsCellInv ?_ ?_ ?_ <;> norm_num
  · refine dwz63_gibbsCell ?_ ?_ ?_ <;> norm_num
  · refine dwz63_gibbsCell ?_ ?_ ?_ <;> norm_num
  · refine dwz63_gibbsCell ?_ ?_ ?_ <;> norm_num
  · refine dwz63_gibbsCell ?_ ?_ ?_ <;> norm_num
  · refine dwz63_gibbsCellInv ?_ ?_ ?_ <;> norm_num
  · refine dwz63_gibbsCell ?_ ?_ ?_ <;> norm_num

set_option maxRecDepth 8000 in
/-- **The fifteen cell terms sum to the deficit, less its `log W` term.** -/
theorem dwz63_sum_gibbsCellTerm :
    ∑ c : Fin 15, dwz63GibbsCellTerm c =
      dwz63GibbsDeficit + Real.log (250000000000000000 / 249999816060193851 : ℝ) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, dwz63GibbsCellTerm, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, dwz63GibbsDeficit]
  ring

/-- The partition sum's logarithm, in the deficit's spelling. -/
theorem dwz63_log_partitionSum :
    Real.log (249999816060193851 / 250000000000000000 : ℝ) =
      -Real.log (250000000000000000 / 249999816060193851 : ℝ) := by
  rw [← Real.log_inv]
  norm_num

/-! ## The gap identity -/

set_option maxRecDepth 8000 in
/-- **The dual gap at `alpha` is exactly `dwz63GibbsDeficit`.**

This is the identity `Examples/DuanWuZhouLevelTwoTripleEntropy.lean`'s docstring records as
verified outside Lean; here it is proved.

Proof sketch: four exact relations combined by `linarith`.  Summing `dwz63_gibbsCellTerm_eq` over
the fifteen cells gives that the `p log p` sum minus the score expectation is
`∑ c, dwz63GibbsCellTerm c`; unfolding `profileEntropyNats` at `profileMass_dwz63Alpha` and
`Real.negMulLog` identifies `H(alpha)` with the negation of that sum; and the committed
`dwz63_sum_gibbsCellTerm`/`dwz63_log_partitionSum` evaluate it and `log W` exactly. -/
theorem dwz63_logPartition_sub_alphaScore :
    Real.log (249999816060193851 / 250000000000000000 : ℝ) -
        ∑ c : Fin 15, ((dwz63Alpha c : ℝ) / 100000000) * dwz63GibbsScore c =
      profileEntropyNats dwz63Alpha + dwz63GibbsDeficit := by
  have hsum : (∑ c : Fin 15,
        ((dwz63Alpha c : ℝ) / 100000000) * Real.log ((dwz63Alpha c : ℝ) / 100000000)) -
      (∑ c : Fin 15, ((dwz63Alpha c : ℝ) / 100000000) * dwz63GibbsScore c) =
      ∑ c : Fin 15, dwz63GibbsCellTerm c := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ ↦ dwz63_gibbsCellTerm_eq c
  have hH : profileEntropyNats dwz63Alpha =
      -(∑ c : Fin 15,
        ((dwz63Alpha c : ℝ) / 100000000) * Real.log ((dwz63Alpha c : ℝ) / 100000000)) := by
    unfold profileEntropyNats
    rw [profileMass_dwz63Alpha, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [Real.negMulLog]
    push_cast
    ring
  have h5 := dwz63_sum_gibbsCellTerm
  have hW := dwz63_log_partitionSum
  linarith

/-! ## The bound -/

set_option maxRecDepth 8000 in
/-- **`Dwz63TripleEntropyBound`, discharged.**

Weak duality at the committed Gibbs witness, the gap identity above, and the committed numeric
certificate.  Nothing is assumed.

Proof sketch: two branches on the scale `k`.  At `k = 0` every count vanishes, so the entropy is
`0` and the bound is `0 ≤ H(alpha) + log K` with both summands nonnegative.  At `k > 0` the
competitor `a` has exact mass `10 ^ 8 · k`; normalising by it gives a probability vector, and
finite Gibbs weak duality (`MaximumEntropyDual.entropy_le_logPartition_sub_expectation`) at
`dwz63GibbsScore` bounds its entropy by `log W − E_a[s]`.  `dwz63_gibbsScore_expectation` then
writes the expectation through the three coordinate marginals only and `marginal_div_profileMass`
equates those of `a` and `alpha` --- this is where `hX`, `hY`, `hZ` are used, `X` and `Y` against
the committed `dwz63AlphaX` and `Z` against `dwz63AlphaZ`.  `dwz63_logPartition_sub_alphaScore`
then replaces what is left by `H(alpha) + dwz63GibbsDeficit`, bounded by `log K`. -/
theorem dwz63_tripleEntropyBound : Dwz63TripleEntropyBound := by
  intro k a ha hX hY hZ
  have hcert := dwz63_gibbsDeficit_le_log_hashLossMultiplier
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hm : ∑ i, a i = 0 := by simpa using WordType.mem_types.mp ha
    have hzero : profileEntropyNats a = 0 := by
      unfold profileEntropyNats
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have hle : a i ≤ ∑ j, a j :=
        Finset.single_le_sum (f := a) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      rw [hm] at hle
      rw [Nat.le_zero.mp hle]
      simp
    rw [hzero]
    have h1 := profileEntropyNats_nonneg dwz63Alpha
    have h2 : (0 : ℝ) ≤ Real.log dwz63HashLossMultiplier := by
      refine Real.log_nonneg ?_
      rw [dwz63HashLossMultiplier]
      norm_num
    linarith
  · have hmass : ∑ i, a i = profileMass dwz63Alpha * k := WordType.mem_types.mp ha
    have hpm : profileMass a = profileMass dwz63Alpha * k := hmass
    have hMpos : 0 < profileMass dwz63Alpha * k := by
      rw [profileMass_dwz63Alpha]
      exact Nat.mul_pos (by norm_num) hk
    have hMR : (0 : ℝ) < ((profileMass dwz63Alpha * k : ℕ) : ℝ) := by exact_mod_cast hMpos
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hp : ∀ c, 0 ≤ (a c : ℝ) / ((profileMass dwz63Alpha * k : ℕ) : ℝ) :=
      fun _ ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hpsum : ∑ c, (a c : ℝ) / ((profileMass dwz63Alpha * k : ℕ) : ℝ) = 1 := by
      rw [← Finset.sum_div]
      have : (∑ c, (a c : ℝ)) = ((profileMass dwz63Alpha * k : ℕ) : ℝ) := by
        rw [← hmass]
        push_cast
        ring
      rw [this]
      exact div_self hMR.ne'
    have hdual := MaximumEntropyDual.entropy_le_logPartition_sub_expectation
      (fun c ↦ (a c : ℝ) / ((profileMass dwz63Alpha * k : ℕ) : ℝ)) dwz63GibbsScore hp hpsum
    rw [dwz63_partition_dwz63GibbsScore] at hdual
    have hent : MaximumEntropyDual.entropy
        (fun c ↦ (a c : ℝ) / ((profileMass dwz63Alpha * k : ℕ) : ℝ)) =
          profileEntropyNats a := by
      unfold MaximumEntropyDual.entropy profileEntropyNats
      rw [hpm]
    rw [hent] at hdual
    have hmarg : ∀ (B : Type) (_ : Fintype B) (_ : DecidableEq B) (coord : Fin 15 → B)
        (bX : B → ℕ), WordType.mappedType coord a = WordType.proportionalCounts bX k →
        WordType.mappedType coord dwz63Alpha = bX → ∀ b : B,
          MaximumEntropyDual.marginal coord
              (fun c ↦ (a c : ℝ) / ((profileMass dwz63Alpha * k : ℕ) : ℝ)) b =
            MaximumEntropyDual.marginal coord
              (fun c ↦ (dwz63Alpha c : ℝ) / 100000000) b := by
      intro B _ _ coord bX h1 h2 b
      rw [marginal_div_profileMass, marginal_div_profileMass, h1, h2, profileMass_dwz63Alpha]
      show ((bX b * k : ℕ) : ℝ) / ((100000000 * k : ℕ) : ℝ) =
        ((bX b : ℕ) : ℝ) / 100000000
      push_cast
      field_simp
    have hscore :
        ∑ c, ((a c : ℝ) / ((profileMass dwz63Alpha * k : ℕ) : ℝ)) * dwz63GibbsScore c =
        ∑ c : Fin 15, ((dwz63Alpha c : ℝ) / 100000000) * dwz63GibbsScore c := by
      have hmX := fun x ↦ hmarg (Fin 5) inferInstance inferInstance dwz63XIndex dwz63AlphaX hX
        mappedType_dwz63XIndex_dwz63Alpha x
      have hmY := fun y ↦ hmarg (Fin 5) inferInstance inferInstance dwz63YIndex dwz63AlphaX hY
        mappedType_dwz63YIndex_dwz63Alpha y
      have hmZ := fun z ↦ hmarg (Fin 5) inferInstance inferInstance dwz63ZIndex dwz63AlphaZ hZ
        mappedType_dwz63ZIndex_dwz63Alpha z
      rw [dwz63_gibbsScore_expectation, dwz63_gibbsScore_expectation]
      simp only [hmX, hmY, hmZ]
    rw [hscore, dwz63_logPartition_sub_alphaScore] at hdual
    exact hdual.trans (add_le_add le_rfl hcert)

end AlgebraicComplexity.Examples
