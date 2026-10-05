import AlgebraicComplexity.Analysis.Subexponential

/-!
# Removing a subexponential loss from copy counts

Finite tensor extractions usually produce a natural number `copies k` together with an estimate

```text
base ^ k ≤ loss k * copies k,
```

where `loss` is subexponential.  This file records the reusable limiting step: every strictly
smaller positive base is eventually attained by the *actual integral copy count*.  The theorem is
independent of tensors, hashing, and entropy; those layers only have to establish the displayed
finite inequality.
-/

namespace AlgebraicComplexity.Growth

/-- A subexponential multiplicative loss does not change the strict exponential growth rate of a
natural-valued copy count.

More precisely, suppose `base ^ k ≤ loss k * copies`.  For every positive `lowerBase < base`, all
sufficiently large `k` satisfy `lowerBase ^ k ≤ copies`.

Proof sketch: eventually `loss k ≤ (base / lowerBase) ^ k`, because the quotient is greater than
one.  Substitute this bound into the finite inequality and cancel the positive factor `base ^ k`.
-/
theorem Subexponential.exists_forall_pow_le_natCast_of_pow_le_mul
    {base lowerBase : ℝ} {loss : ℕ → ℝ}
    (hloss : Subexponential loss)
    (hlower : 0 < lowerBase) (hlt : lowerBase < base) :
    ∃ cutoff : ℕ, ∀ k copies : ℕ, cutoff ≤ k →
      base ^ k ≤ loss k * (copies : ℝ) →
        lowerBase ^ k ≤ (copies : ℝ) := by
  have hbase : 0 < base := hlower.trans hlt
  have hratio : 1 < base / lowerBase := (one_lt_div hlower).2 hlt
  obtain ⟨cutoff, hcutoff⟩ := hloss.eventually_le_pow hratio
  refine ⟨cutoff, fun k copies hk hfinite ↦ ?_⟩
  have hcopies : 0 ≤ (copies : ℝ) := Nat.cast_nonneg copies
  have hkey : base ^ k ≤ base ^ k / lowerBase ^ k * (copies : ℝ) := by
    calc
      base ^ k ≤ loss k * (copies : ℝ) := hfinite
      _ ≤ (base / lowerBase) ^ k * (copies : ℝ) :=
        mul_le_mul_of_nonneg_right (hcutoff k hk) hcopies
      _ = base ^ k / lowerBase ^ k * (copies : ℝ) := by rw [div_pow]
  have hlowerPow : 0 < lowerBase ^ k := pow_pos hlower k
  rw [div_mul_eq_mul_div, le_div_iff₀ hlowerPow] at hkey
  exact le_of_mul_le_mul_left hkey (pow_pos hbase k)

end AlgebraicComplexity.Growth
