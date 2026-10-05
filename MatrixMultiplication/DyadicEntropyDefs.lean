/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option autoImplicit false

/-!
# Dyadic mass and entropy definitions

This definition-only leaf contains the two real-valued primitives shared by the dyadic
certificate evaluator and semantic integral-profile bridges.  It deliberately contains no
logarithm enclosures, certificate tables, probability-vector theorems, or generated data.

`MatrixMultiplication.DyadicEntropy` imports and re-exports this module, so the public names and
their definitions are unchanged.
-/

namespace MatrixMultiplication.DyadicEntropy

noncomputable section

/-- A dyadic mass coordinate interpreted as a real number. -/
def mass (bits numerator : ℕ) : ℝ := numerator / (2 : ℝ) ^ bits

/-- One Shannon summand in bits. -/
def entropyTerm (bits numerator : ℕ) : ℝ :=
  Real.negMulLog (mass bits numerator) / Real.log 2

end

end MatrixMultiplication.DyadicEntropy
