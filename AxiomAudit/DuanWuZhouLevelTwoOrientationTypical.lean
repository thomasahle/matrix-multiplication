/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrientationTypical

set_option autoImplicit false

/-! # Axiom audit for per-orientation typicality of a six-orientation block word

The fifteen cells as coarse square addresses and the pushed-forward `dwz63Alpha` profile with its
total mass; the six oriented source letters, their membership in the coarse support, and the
oriented sub-words; the typicality predicate, the word length it forces, and the typical family
with its subfamily interface. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63CellAddress
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaAddress
#assert_axioms AlgebraicComplexity.Examples.profileMass_dwz63AlphaAddress
#assert_axioms AlgebraicComplexity.Examples.dwz63SourceLetter
#assert_axioms AlgebraicComplexity.Examples.dwz63OrientedWord
#assert_axioms AlgebraicComplexity.Examples.Dwz63OrientationTypical
#assert_axioms AlgebraicComplexity.Examples.dwz63OrientationTypical_length
#assert_axioms AlgebraicComplexity.Examples.dwz63TypicalWords
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63TypicalWords
#assert_axioms AlgebraicComplexity.Examples.dwz63TypicalWords_orientationTypical
#assert_axioms AlgebraicComplexity.Examples.orientationTypical_of_subset
#assert_axioms AlgebraicComplexity.Examples.dwz63SourceLetter_mem_cwSquareSupport
