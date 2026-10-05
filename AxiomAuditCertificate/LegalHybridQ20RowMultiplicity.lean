/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.LegalHybridQ20RowMultiplicity

set_option autoImplicit false

/-!
# Axiom audit and literal row-44 client for q20 row multiplicities

This companion checks both public declarations of the exact q20 row-multiplicity adapter.
The paper input is regional division in [alman2025more],
`papers/sources/2404.16349/constituent.tex:153-175`; the integral ordered-count convention is
`better_bound/paper.tex:397-445`. The final client applies the all-row result at schedule
position 44 and recovers the literal region-one, parent-six sample-count proposition.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu,
  Zixuan Xu, and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace MatrixMultiplication.LegalHybridQ20RowMultiplicity

#assert_axioms rowSamples
#assert_axioms allActiveRowSamples_pos

/-- The all-row theorem applies to the literal q20 row-44 source, not an abstract row family. -/
example :
    0 < SimplifiedRecursiveSplitTypes.levelFourSamples
      (SimplifiedExponentLevelFourRecurrence.reconstructedTopBranchRows
        LegalHybridQ20Row44Primary.semanticPrimaryTables) 1 1 6 := by
  simpa only [rowSamples, Generated.LegalHybridQ20ModeSchedule.row44_key] using
    allActiveRowSamples_pos 44

end MatrixMultiplication.LegalHybridQ20RowMultiplicity
