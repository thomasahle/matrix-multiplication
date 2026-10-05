/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.CompatibleSplitCount
import AlgebraicComplexity.Probability.IntegralProfileCore

/-!
# Finite entropy core of the Duan--Wu--Zhou compatibility rate

This lightweight module defines the compatibility-rate entropy expressions and proves their
closed forms.  It imports the finite compatible-split counting cluster and the integral-profile
entropy API.  Proportional-multinomial asymptotics and hole-fraction arithmetic remain in
`AlgebraicComplexity.Analysis.CompatibilityRate`, which imports and re-exports this module.

Keeping this finite layer separate lets certificate semantics use `compatibilityLogLoss` and
`compatibilityRateBits` without importing the substantially heavier proportional-multinomial
asymptotics cone.
-/

namespace AlgebraicComplexity.CompatibleSplit

open AlgebraicComplexity.WordType
open scoped BigOperators

universe u v w

variable {C : Type u} {L : Type v} {Z : Type w}

/-- The total conditional-entropy mass of a joint integral profile: the sum over rows of the row
mass times the row's normalized Shannon entropy, in nats.  For a profile of total mass `n` this is
`n` times the conditional entropy of the second coordinate given the first. -/
noncomputable def rowEntropyMass {A B : Type*} [Fintype A] [Fintype B] (θ : A × B → ℕ) : ℝ :=
  ∑ a, (profileMass fun b ↦ θ (a, b) : ℕ) * profileEntropyNats fun b ↦ θ (a, b)

namespace SplitRequirements

variable [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L] [Fintype Z] [DecidableEq Z]
variable (S : SplitRequirements C L Z)

/-! ### The two averaged split profiles -/

/-- DWZ's pooled split profile `α̃^{avg}_{+,+,k}` in integral form: the sum of the prescribed
splits of the interior components (`i, j > 0`) with Z-index `k`. -/
noncomputable def pooledSplit (z : Z) : L → ℕ := fun l ↦ S.compatibleType (Sum.inr z, l)

/-- DWZ's average split profile `α̃^{avg}_{*,*,k}` in integral form: the sum of the prescribed
splits of **all** components with Z-index `k`.  This is the `k`-row of the typicalness
distribution `γ`. -/
noncomputable def averageSplit (z : Z) : L → ℕ := fun l ↦ S.typicalType (z, l)

/-! ### The rate -/

/-- The unnormalized exponent of `p_comp`: the conditional-entropy mass of the compatibility
profile minus that of the typicalness profile, in nats.  For a word length `n` this is
`n · log ẏ_p`. -/
noncomputable def compatibilityLogLoss : ℝ :=
  rowEntropyMass S.compatibleType - rowEntropyMass S.typicalType

/-- `log ẏ_p` in nats: DWZ `lemma:pcomp_g`'s exponent, normalized per index position. -/
noncomputable def compatibilityRateLog : ℝ :=
  S.compatibilityLogLoss / (profileMass S.usefulType : ℕ)

/-- DWZ's `ẏ_p = lim p_comp^{1/n}`, the exponential base of the combination loss.  DWZ's
*combination loss* itself is `1 / ẏ_p`. -/
noncomputable def compatibilityRate : ℝ := Real.exp S.compatibilityRateLog

/-- `log₂ ẏ_p`: the exponent in the paper's own base-two display of `lemma:pcomp_g`. -/
noncomputable def compatibilityRateBits : ℝ := S.compatibilityRateLog / Real.log 2

omit [DecidableEq C] [DecidableEq L] [DecidableEq Z] in
/-- `ẏ_p = 2^{log₂ ẏ_p}`, matching the paper's display. -/
theorem compatibilityRate_eq_two_rpow :
    S.compatibilityRate = (2 : ℝ) ^ S.compatibilityRateBits := by
  have hlog : Real.log 2 ≠ 0 := by
    simpa using Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  rw [compatibilityRate, compatibilityRateBits,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  field_simp

/-! ### DWZ's closed form -/

omit [DecidableEq C] [DecidableEq L] in
/-- The conditional-entropy mass of the compatibility profile splits into the boundary
components' own entropies and the pooled entropies, one per Z-index.  The interior components
contribute nothing to the `Sum.inl` rows: their rows are structurally zero, which is exactly the
requirement-partition statement that an interior position is governed only by its pooled
requirement. -/
theorem rowEntropyMass_compatibleType :
    rowEntropyMass S.compatibleType =
      (∑ c, if S.boundary c then
          (profileMass (S.splitCount c) : ℕ) * profileEntropyNats (S.splitCount c) else 0) +
        ∑ z : Z, (profileMass (S.pooledSplit z) : ℕ) * profileEntropyNats (S.pooledSplit z) := by
  classical
  rw [rowEntropyMass, Fintype.sum_sum_type]
  congr 1
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  by_cases hc : S.boundary c = true
  · rw [if_pos hc]
    have hrow : (fun l ↦ S.compatibleType (Sum.inl c, l)) = S.splitCount c := by
      funext l
      rw [S.compatibleType_inl c l, if_pos hc]
    rw [hrow]
  · rw [if_neg hc]
    have hrow : (fun l ↦ S.compatibleType (Sum.inl c, l)) = fun _ ↦ 0 := by
      funext l
      rw [S.compatibleType_inl c l, if_neg hc]
    rw [hrow]
    simp [profileMass]

omit [DecidableEq C] [DecidableEq L] [DecidableEq Z] in
/-- The conditional-entropy mass of the typicalness profile is the sum over Z-indices of the
average split entropies, `∑_k n α_Z(k) H(α̃^avg_{*,*,k})`. -/
theorem rowEntropyMass_typicalType :
    rowEntropyMass S.typicalType =
      ∑ z : Z, (profileMass (S.averageSplit z) : ℕ) * profileEntropyNats (S.averageSplit z) :=
  rfl

omit [DecidableEq C] [DecidableEq L] in
/-- DWZ's closed form for `log ẏ_p`, with integral masses and explicit normalization. -/
theorem compatibilityRateLog_eq_dwz :
    S.compatibilityRateLog =
      ((∑ c, if S.boundary c then
            (profileMass (S.splitCount c) : ℕ) * profileEntropyNats (S.splitCount c) else 0) +
          (∑ z : Z, (profileMass (S.pooledSplit z) : ℕ) * profileEntropyNats (S.pooledSplit z)) -
          ∑ z : Z, (profileMass (S.averageSplit z) : ℕ) * profileEntropyNats (S.averageSplit z)) /
        (profileMass S.usefulType : ℕ) := by
  rw [compatibilityRateLog, compatibilityLogLoss, S.rowEntropyMass_compatibleType,
    S.rowEntropyMass_typicalType]

end SplitRequirements

end AlgebraicComplexity.CompatibleSplit
