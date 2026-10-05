import AlgebraicComplexity.Analysis.Subexponential

/-!
# Absorbing a finite prefix in an asymptotic copy bound

Finite extraction arguments often prove that `base ^ k ≤ copies k` only after a cutoff.  The
sequence interfaces used by the asymptotic sum inequality ask for a bound at every positive
index, with a positive subexponential loss.  This file records the elementary bridge: before the
cutoff use `base ^ k` itself as the loss, and after the cutoff use `1`.

This changes only finitely many values, so it is subexponential.  The construction is useful in
particular after a Behrend/hash-count limit theorem, where discarding the finite prefix by
reindexing would incorrectly change the tensor-power stride.
-/

namespace AlgebraicComplexity.Growth

/-- Loss which absorbs the values before `cutoff` and is exactly one afterwards. -/
def finitePrefixPowerLoss (base : ℝ) (cutoff k : ℕ) : ℝ :=
  if cutoff ≤ k then 1 else base ^ k

theorem finitePrefixPowerLoss_pos {base : ℝ} (hbase : 0 < base)
    (cutoff k : ℕ) :
    0 < finitePrefixPowerLoss base cutoff k := by
  unfold finitePrefixPowerLoss
  split_ifs
  · exact zero_lt_one
  · exact pow_pos hbase k

/-- The finite-prefix loss is bounded by one fixed constant. -/
theorem finitePrefixPowerLoss_le_const {base : ℝ} (hbase : 0 ≤ base)
    (cutoff k : ℕ) :
    finitePrefixPowerLoss base cutoff k ≤ (max 1 base) ^ cutoff := by
  unfold finitePrefixPowerLoss
  split_ifs with hk
  · exact one_le_pow₀ (le_max_left 1 base)
  · have hkcutoff : k ≤ cutoff := Nat.le_of_lt (Nat.lt_of_not_ge hk)
    calc
      base ^ k ≤ (max 1 base) ^ k :=
        pow_le_pow_left₀ hbase (le_max_right 1 base) k
      _ ≤ (max 1 base) ^ cutoff :=
        pow_le_pow_right₀ (le_max_left 1 base) hkcutoff

theorem finitePrefixPowerLoss_subexponential {base : ℝ} (hbase : 0 ≤ base)
    (cutoff : ℕ) :
    Subexponential (finitePrefixPowerLoss base cutoff) := by
  apply Subexponential.mono
      (Subexponential.const (pow_nonneg (zero_le_one.trans (le_max_left 1 base)) cutoff))
  · intro k
    unfold finitePrefixPowerLoss
    split_ifs
    · exact zero_le_one
    · exact pow_nonneg hbase k
  · exact finitePrefixPowerLoss_le_const hbase cutoff

/-- Upgrade an eventual copy lower bound to an all-positive-index growth inequality.

The only extra input is that the natural-valued copy count is positive at positive indices.  No
stride shift or tail reindexing is introduced. -/
theorem pow_le_finitePrefixPowerLoss_mul_count
    {base : ℝ} {cutoff : ℕ} {count : ℕ → ℕ}
    (hbase : 0 < base)
    (hcount : ∀ k, 0 < k → 0 < count k)
    (heventual : ∀ k, cutoff ≤ k → 0 < k → base ^ k ≤ (count k : ℝ)) :
    ∀ k, 0 < k →
      base ^ k ≤ finitePrefixPowerLoss base cutoff k * (count k : ℝ) := by
  intro k hk
  by_cases hcutoff : cutoff ≤ k
  · simpa only [finitePrefixPowerLoss, if_pos hcutoff, one_mul] using
      heventual k hcutoff hk
  · have hcountOne : (1 : ℝ) ≤ (count k : ℝ) := by
      have hcountPos : 0 < count k := hcount k hk
      exact_mod_cast (show 1 ≤ count k by omega)
    simpa only [finitePrefixPowerLoss, if_neg hcutoff] using
      (le_mul_of_one_le_right (pow_nonneg hbase.le k) hcountOne)

end AlgebraicComplexity.Growth
