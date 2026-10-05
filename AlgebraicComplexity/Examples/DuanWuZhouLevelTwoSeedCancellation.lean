/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The hashing seed's modulus cancellation, as pure arithmetic

Layer 4 (`AlgebraicComplexity/Examples/`).  `[DuanWuZhou2022]`'s retention bound is
`3 |marked| |B| <= 4 |R|^2 |retained|`, and the count side pairs it with an estimate carrying the
same modulus factor, `rate * (4 |R|^2) <= loss * (3 |marked| |B|)`.  Chaining them and cancelling
`4 |R|^2` gives `rate <= loss * |retained|`.

That cancellation was written out twice --- once at the six-orientation partition and once at the
plain one --- in thirty-five identical lines each, differing only in which retained support
appeared.  It contains no tensor, no partition, no hashing and no distribution: it is one
inequality about six real numbers, and it is stated here as such so that both call sites, and any
later endpoint, share it.

It is named in the `dwz63` family rather than promoted to `Analysis/` because the `3` and the
shape `rate * M <= loss * (3 m b)` are `[DuanWuZhou2022]`'s own bookkeeping, not a general fact
anyone else would look for under that name.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6 and `hashing.tex`.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

/-- **The modulus factor cancels.**

`hseed` is the seed's retention bound and `hmarked` the count-side estimate, both carrying the
modulus factor `M = 4 |R|^2`; the conclusion is free of it. -/
theorem dwz63_rate_le_loss_of_seed {rate loss m b c M : ℝ} (hM : 0 < M) (hloss : 0 ≤ loss)
    (hseed : 3 * m * b ≤ M * c) (hmarked : rate * M ≤ loss * (3 * m * b)) :
    rate ≤ loss * c := by
  have key : rate * M ≤ loss * c * M :=
    calc rate * M ≤ loss * (3 * m * b) := hmarked
      _ ≤ loss * (M * c) := mul_le_mul_of_nonneg_left hseed hloss
      _ = loss * c * M := by ring
  exact le_of_mul_le_mul_right key hM

end AlgebraicComplexity.Examples
