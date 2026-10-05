/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroWord
import AxiomAudit.Command

/-!
# Axiom audit for canonical all-zero CW words

Checks the exact native split-word identity used by zero-coordinate constituent clients.
-/

open AlgebraicComplexity.Examples

#assert_axioms cwChunkSplitWord_zeroChunkWord
