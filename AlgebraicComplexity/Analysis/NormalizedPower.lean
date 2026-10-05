import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Normalizing proportional real powers

This file contains the elementary real-power identity behind proportional tensor-value
certificates.  Repeating a positive base `k` times raises it to the natural power `k`; normalizing
by the proportional length `N*k` cancels that repetition exactly.
-/

namespace AlgebraicComplexity

/-- A positive repeated base, normalized by its proportional length, is independent of the
repetition count:

```text
(base^k)^(1/(N*k)) = base^(1/N).
```

Proof sketch: turn the natural power into a real power, combine the two real exponents, and cancel
the nonzero real casts of `N` and `k`.
-/
theorem normalizedRepeatedPower_eq
    (base : ℝ) (N k : ℕ) (hbase : 0 < base) (hN : 0 < N) (hk : 0 < k) :
    (base ^ k) ^ (((N * k : ℕ) : ℝ)⁻¹) =
      base ^ (((N : ℕ) : ℝ)⁻¹) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
  congr 1
  push_cast
  field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne',
    show (k : ℝ) ≠ 0 by exact_mod_cast hk.ne']

end AlgebraicComplexity
