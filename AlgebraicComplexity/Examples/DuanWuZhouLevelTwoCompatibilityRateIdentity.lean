/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompatibilityTypeCount
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCountingSplit
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobalArithmetic
import AlgebraicComplexity.Combinatorics.PushedConditionalEntropyCore

set_option autoImplicit false

/-!
# `log ᾱ_p` is the conditional-entropy mass of the section 6.3 splits, exactly

Layer 4 (`AlgebraicComplexity/Examples/`).  This module supplies the one section 6.3 input that
`Examples/DuanWuZhouLevelTwoCompatibilityTypeCount.lean` asks for, and with it the named brick

`Dwz63CompatibleFractionUpper (dwz63Split k) _ (Real.exp dwz63LogCompat) (dwz63CompatSlack _ _)`

of `Examples/DuanWuZhouLevelTwoCompetitorRateBrick.lean`.

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, **§6.2--6.3 (`global_value.tex`)**: `lemma:pcomp_g`, the compatibility rate
> `ᾱ_p` and the split tables of section 6.3 (`[DuanWuZhou2022]`).

## No dual certificate is needed

The entropy step of the compatibility rate is often described as a maximum-entropy problem: bound
`H(joint) − H(K-profile)` over the compatible polytope by `log ᾱ_p`.  At section 6.3 that maximum
is *attained at the prescribed profile itself*, because DWZ's compatibility pins the split of every
requirement cell: `compatibleSet` is a single conditional type class, not a union over a polytope
of types.  So the inequality this campaign needs is an **identity**, and it needs no dual, no
Lagrangian witness and no numeric enclosure beyond exact rational arithmetic:

`dwz63_compatibilityLogLoss_dwz63Split :`
`  (dwz63Split k).compatibilityLogLoss = (2 · 10 ^ 16 · k) · dwz63LogCompat`.

Its content is that `Examples/DuanWuZhouLevelTwoGlobalArithmetic.lean`'s six-term expression
`dwz63LogCompat` *is* the normalized conditional-entropy mass of the section 6.3 tables.  Written
out, the boundary rows of `dwz63SplitCount` and the pooled rows of `dwz63PooledCount` contribute

* `log 2` from the four boundary components with a uniform two-point split and from the pooled row
  at `k = 1`, with total weight `1017788400000000 + 8293783200000000`;
* the `a`-split atoms `log (10 ^ 8 / 3477403)` and `log (5 · 10 ^ 7 / 46522597)` from `(0,2,2)`
  and `(2,0,2)`;
* the `b`-split atoms `log (2 · 10 ^ 7 / 4203)` and `log (10 ^ 7 / 9995797)` from the pooled
  interior requirement at `k = 2`,

while the typicalness rows of `dwz63AverageCount` contribute `log 2` with total weight
`8827110400000000 + 484461200000000` together with the two `γ`-atoms
`log (816450260000000 / 14504450740003)` and `log (408225130000000 / 393720679259997)`.  The two
`log 2` weights are **equal**, so that atom cancels identically — which is why `dwz63LogCompat` has
six terms and no `log 2` — and the remaining six coefficients agree with `dwz63LogCompat`'s on the
nose after multiplication by the base word length `2 · 10 ^ 16`.

## Scaling in the repetition count

`dwz63Split k` repeats the base tables `k` times, so every row is `proportionalCounts row k`.
Normalized Shannon entropy is invariant under that repetition
(`profileEntropyNats_proportionalCounts`) and the row mass is linear in it, so each row's
contribution is `k` times its base contribution; `dwz63_rowEntropyTerm_scaledRow` records this in
the zero-tolerant form that also covers `k = 0` and the structurally zero rows (the `Sum.inl` rows
of every interior component, and the pooled rows at `k = 3, 4`, which carry no interior component).

## Position in the library

Layer 4 (a client).  Every declaration is either a generic entropy rearrangement or a finite
identity between committed section 6.3 tables and a committed certificate expression.  The three
generic helpers are `dwz63`-prefixed because they are stated here rather than in `Probability/`;
their intended homes are named in the report accompanying this module.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity AlgebraicComplexity.WordType AlgebraicComplexity.CompatibleSplit
open scoped BigOperators

universe u

/-! ## Generic rearrangements -/

/-- The conditional-entropy mass of one row, division-free: `m · H(θ) = ∑_i θ_i · log (m / θ_i)`.
Zero-tolerant — a coordinate with `θ_i = 0` contributes `0` on both sides, and so does a row of
total mass `0`. -/
theorem dwz63_profileMass_mul_profileEntropyNats {I : Type u} [Fintype I] (a : I → ℕ) :
    ((profileMass a : ℕ) : ℝ) * profileEntropyNats a =
      ∑ i, (a i : ℝ) * Real.log (((profileMass a : ℕ) : ℝ) / (a i : ℝ)) := by
  rw [profileEntropyNats, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases Nat.eq_zero_or_pos (a i) with h | h
  · simp [h, Real.negMulLog]
  · have hm : 0 < profileMass a :=
      lt_of_lt_of_le h (Finset.single_le_sum (f := fun j ↦ a j)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))
    have hai : ((a i : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.ne'
    have hmR : ((profileMass a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    rw [Real.negMulLog, Real.log_div hai hmR, Real.log_div hmR hai]
    field_simp
    ring

/-- Repeating a profile `k` times multiplies its mass by `k`. -/
theorem dwz63_profileMass_scaledRow {I : Type u} [Fintype I] (a : I → ℕ) (k : ℕ) :
    profileMass (fun i ↦ a i * k) = profileMass a * k := by
  show ∑ i, a i * k = (∑ i, a i) * k
  rw [Finset.sum_mul]

/-- **The repetition law for a row's conditional-entropy contribution.**  Mass is linear and
normalized entropy is invariant, so the contribution scales by `k`.  Zero-tolerant in both
directions: no positivity of `k` or of the row mass is assumed. -/
theorem dwz63_rowEntropyTerm_scaledRow {I : Type u} [Fintype I] (a : I → ℕ) (k : ℕ) :
    ((profileMass (fun i ↦ a i * k) : ℕ) : ℝ) * profileEntropyNats (fun i ↦ a i * k) =
      (k : ℝ) * (((profileMass a : ℕ) : ℝ) * profileEntropyNats a) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [dwz63_profileMass_scaledRow]
    simp
  · rcases Nat.eq_zero_or_pos (profileMass a) with hm | hm
    · rw [dwz63_profileMass_scaledRow, hm]
      simp
    · have hent : profileEntropyNats (fun i ↦ a i * k) = profileEntropyNats a :=
        profileEntropyNats_proportionalCounts a hm k hk
      rw [dwz63_profileMass_scaledRow, hent]
      push_cast
      ring

/-- The three-letter form of `dwz63_profileMass_mul_profileEntropyNats`: the split alphabet of
section 6.3 is the ordered left half `k_l ∈ {0, 1, 2}`. -/
theorem dwz63_fin3_rowEntropyTerm (r : Fin 3 → ℕ) :
    ((profileMass r : ℕ) : ℝ) * profileEntropyNats r =
      (r 0 : ℝ) * Real.log (((r 0 + r 1 + r 2 : ℕ) : ℝ) / (r 0 : ℝ)) +
        (r 1 : ℝ) * Real.log (((r 0 + r 1 + r 2 : ℕ) : ℝ) / (r 1 : ℝ)) +
        (r 2 : ℝ) * Real.log (((r 0 + r 1 + r 2 : ℕ) : ℝ) / (r 2 : ℝ)) := by
  have hmass : profileMass r = r 0 + r 1 + r 2 := by
    show ∑ i, r i = _
    rw [Fin.sum_univ_three]
  rw [dwz63_profileMass_mul_profileEntropyNats, Fin.sum_univ_three, hmass]

/-! ## The section 6.3 identity -/

-- ELABORATION RISK: the closing `norm_num` evaluates the twenty-five three-letter rows of
-- `dwz63SplitCount`, `dwz63PooledCount` and `dwz63AverageCount`, reduces each `log (m / θ_i)`
-- argument to lowest terms, and matches the result against `dwz63LogCompat`'s six atoms.  It is
-- exact rational arithmetic on seventeen-digit numerals with no `decide` and no enclosure; the
-- measured elaboration cost of the whole module is a few seconds.
/-- **`dwz63LogCompat` is the conditional-entropy mass of the section 6.3 splits.**

`compatibilityLogLoss` is `H-mass(compatibility profile) − H-mass(typicalness profile)`, DWZ's
unnormalized `log p_comp`; the base word length of `dwz63Split k` is `2 · 10 ^ 16 · k`.  The `log 2`
contributions of the four uniform boundary splits and of the pooled row at `k = 1` cancel exactly
against those of the typicalness rows at `k = 1, 3`, leaving the six atoms of `dwz63LogCompat`. -/
theorem dwz63_compatibilityLogLoss_dwz63Split (k : ℕ) :
    (dwz63Split k).compatibilityLogLoss =
      ((20000000000000000 * k : ℕ) : ℝ) * dwz63LogCompat := by
  have hpool : ∀ z : Fin 5, (dwz63Split k).pooledSplit z = fun l ↦ dwz63PooledCount z l * k :=
    fun z ↦ funext fun l ↦ dwz63_compatibleType_inr k z l
  have havg : ∀ z : Fin 5, (dwz63Split k).averageSplit z = fun l ↦ dwz63AverageCount z l * k :=
    fun z ↦ funext fun l ↦ dwz63_typicalType k z l
  have hsplit : ∀ c : Fin 15, (dwz63Split k).splitCount c = fun l ↦ dwz63SplitCount c l * k :=
    fun _ ↦ rfl
  have hbdry : (dwz63Split k).boundary = dwz63Boundary := rfl
  rw [SplitRequirements.compatibilityLogLoss,
    (dwz63Split k).rowEntropyMass_compatibleType, (dwz63Split k).rowEntropyMass_typicalType]
  simp only [hpool, havg, hsplit, hbdry, dwz63_rowEntropyTerm_scaledRow, dwz63_fin3_rowEntropyTerm]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, dwz63Boundary, dwz63SplitCount,
    dwz63PooledCount, dwz63AverageCount, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, if_true]
  rw [dwz63LogCompat]
  push_cast
  norm_num
  ring

/-- The total mass of the section 6.3 usefulness profile is the word length `2 · 10 ^ 16 · k`. -/
theorem dwz63_profileMass_usefulType_dwz63Split (k : ℕ) :
    profileMass (dwz63Split k).usefulType = 20000000000000000 * k := by
  show ∑ p, (dwz63Split k).usefulType p = _
  rw [SplitRequirements.sum_usefulType (dwz63Split_refinesType k)]
  exact dwz63Split_profileMass k

/-- **`log ᾱ_p` at section 6.3.**  The normalized rate of `Analysis/CompatibilityRateCore.lean`
evaluated at the section 6.3 record is exactly the certificate expression `dwz63LogCompat`, whose
enclosure `dwz63_exp_le_compatRate` bounds `ᾱ_p` above by the declared `dwz63CompatRate`. -/
theorem dwz63_compatibilityRateLog_dwz63Split {k : ℕ} (hk : 0 < k) :
    (dwz63Split k).compatibilityRateLog = dwz63LogCompat := by
  have hmass : profileMass (dwz63Split k).usefulType = 20000000000000000 * k :=
    dwz63_profileMass_usefulType_dwz63Split k
  have hne : ((20000000000000000 * k : ℕ) : ℝ) ≠ 0 := by
    have : 0 < 20000000000000000 * k := by omega
    exact_mod_cast this.ne'
  rw [SplitRequirements.compatibilityRateLog, dwz63_compatibilityLogLoss_dwz63Split k, hmass]
  field_simp

/-! ## The brick, at section 6.3 -/

/-- **`Dwz63CompatibleFractionUpper` at the section 6.3 parameters, with the rate
`ᾱ_p = Real.exp dwz63LogCompat` and the polynomial slack `dwz63CompatSlack`.**

This is the brick that `Examples/DuanWuZhouLevelTwoCompetitorRateBrick.lean`'s module docstring
records as "not derivable from anything committed": the upper half of
`p_comp = ᾱ_p^{n + o(n)}`, division-free, with the slack explicit and subexponential
(`dwz63CompatSlack_subexponential`).  Only the upper bound is produced; the matching lower half is
not needed anywhere in the campaign. -/
theorem dwz63_compatibleFractionUpper_dwz63Split (k : ℕ) :
    Dwz63CompatibleFractionUpper (dwz63Split k)
      (WordType.proportionalCounts dwz63Alpha (200000000 * k))
      (Real.exp dwz63LogCompat) (dwz63CompatSlack (Fin 3) (Fin 5)) := by
  refine dwz63_compatibleFractionUpper_of_compatibilityLogLoss_le (dwz63Split k)
    (dwz63Split_refinesType k) ?_
  rw [dwz63_compatibilityLogLoss_dwz63Split k, dwz63_profileMass_usefulType_dwz63Split k]

end AlgebraicComplexity.Examples
