/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lightweight definitions for polynomial growth

This layer-0 leaf contains the two definitions needed to *state* polynomial-exponent results:
constant-tolerant polynomial boundedness and the infimum of admissible exponents.  Their theorem
library, together with exponential growth and multiplicative Fekete theory, remains in
`AlgebraicComplexity/Asymptotics.lean`.

The split is intentionally semantic rather than mathematical.  Clients that only mention an
exponent in a certificate or numerical expression should not have to load the much larger limit
theory used to prove properties of that exponent.
-/

namespace AlgebraicComplexity.Growth

/-- `a` grows at most polynomially with real exponent `τ`, up to a fixed positive constant.
The estimate is required only for positive natural inputs, where real powers are unambiguous. -/
def PolynomialBound (a : ℕ → ℕ) (τ : ℝ) : Prop :=
  0 ≤ τ ∧ ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) ≤ C * (n : ℝ) ^ τ

/-- The least real polynomial exponent bounding a natural-valued sequence. -/
noncomputable def polynomialExponent (a : ℕ → ℕ) : ℝ :=
  sInf { τ : ℝ | PolynomialBound a τ }

end AlgebraicComplexity.Growth
