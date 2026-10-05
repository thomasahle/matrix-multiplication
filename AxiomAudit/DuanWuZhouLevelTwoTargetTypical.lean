/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoTargetTypical

set_option autoImplicit false

/-! # Axiom audit for target-coordinate typicality of a six-orientation block word

The leg-permutation equivalence of coarse addresses and the symmetry of the degree-four
antidiagonal; the six named orientations and the untransported target letter; the target sub-word,
its typicality predicate, the word length that predicate forces, and the typical family with its
subfamily interface; and the lemma relating the target convention to the source convention of
`Examples/DuanWuZhouLevelTwoOrientationTypical.lean`.

The anti-vacuity pin `dwz63TargetLetter_mem_cwSquareSupport` is audited by the typical-count
lane's `AxiomAudit` for `Examples/DuanWuZhouLevelTwoSixOrientationDigits.lean`, which is where it
is proved; it cannot be stated here because that module imports this one. -/

#assert_axioms AlgebraicComplexity.Examples.cwSquarePermute
#assert_axioms AlgebraicComplexity.Examples.cwSquarePermute_apply
#assert_axioms AlgebraicComplexity.Examples.cwSquarePermute_eq_permuteBlockAddress
#assert_axioms AlgebraicComplexity.Examples.mem_cwSquareAntidiagonal_iff
#assert_axioms AlgebraicComplexity.Examples.mem_cwSquareSupport_cwSquarePermute
#assert_axioms AlgebraicComplexity.Examples.dwz63Orientation
#assert_axioms AlgebraicComplexity.Examples.dwz63TargetLetter
#assert_axioms AlgebraicComplexity.Examples.dwz63TargetLetter_eq_cwSquarePermute
#assert_axioms AlgebraicComplexity.Examples.dwz63TargetWord
#assert_axioms AlgebraicComplexity.Examples.dwz63TargetWord_eq
#assert_axioms AlgebraicComplexity.Examples.Dwz63TargetTypical
#assert_axioms AlgebraicComplexity.Examples.multiplicity_comp_equiv
#assert_axioms AlgebraicComplexity.Examples.dwz63TargetTypical_iff_orientationTypical_comp
#assert_axioms AlgebraicComplexity.Examples.dwz63TargetTypical_length
#assert_axioms AlgebraicComplexity.Examples.dwz63TargetTypicalWords
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63TargetTypicalWords
#assert_axioms AlgebraicComplexity.Examples.targetTypical_of_subset
