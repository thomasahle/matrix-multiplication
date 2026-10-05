/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Data.List.Defs

/-!
# Definition-only utilities for dyadic numerator rows

Generated arithmetic checkers often need to remove zero padding before they import any real
analysis or entropy semantics.  This module owns that executable operation behind an `Init`-only
boundary.  `DyadicEntropyForm.lean` supplies the later semantic invariance theorems.
-/

namespace MatrixMultiplication.DyadicEntropyForm

/-- Remove every zero numerator while preserving the order of the nonzero entries. -/
def dropZeros : List ℕ → List ℕ
  | [] => []
  | 0 :: numerators => dropZeros numerators
  | (numerator + 1) :: numerators => (numerator + 1) :: dropZeros numerators

end MatrixMultiplication.DyadicEntropyForm
