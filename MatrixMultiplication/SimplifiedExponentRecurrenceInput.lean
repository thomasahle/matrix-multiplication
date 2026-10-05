/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Init

/-!
# Exact input records for the level-two exponent recurrence

This definition-only module owns the small integer record consumed by the level-two retained-rate
checker.  It deliberately imports neither real logarithms nor the full recursive-volume
reconstruction.  Generated certificate modules can therefore elaborate lists of these records
without loading the expensive analytic theorem closure.

The semantic interpretation of an `EdgeInput` remains in
`MatrixMultiplication/SimplifiedExponentRecurrence.lean`; the lightweight executable reconstruction
from sparse primary tables lives in `SimplifiedExponentLevelTwoInput.lean`.
-/

namespace MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

/-- Minimal exact data determining all three retained-rate contributions of one positive
level-two edge.

`occurrenceNumerator` is measured at the recurrence's common dyadic denominator,
`muNumerator` specifies the three-letter entropy law, and `heavyCoordinate` identifies the one
branch receiving that entropy rather than the unit leaf rate. -/
structure EdgeInput where
  occurrenceNumerator : Nat
  muNumerator : Nat
  heavyCoordinate : Nat
  deriving DecidableEq, Repr

end MatrixMultiplication.SimplifiedExponentRecurrence.Chunked
