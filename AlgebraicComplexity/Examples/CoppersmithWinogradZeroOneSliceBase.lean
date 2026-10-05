/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOneSlice020
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOneSlice110
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOneSlice200

/-!
# Base one-slice maps for zero-coordinate CW constituents

This module re-exports the explicit restriction certificates for the three base CW constituents
whose `Z` address is zero.  The finite coordinate proofs are deliberately compiled separately;
clients retain one stable import while each proof stays within a small elaboration envelope.
-/
