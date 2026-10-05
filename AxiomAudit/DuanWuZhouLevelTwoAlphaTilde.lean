/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAlphaTilde

/-! # Axiom audit for the fifteen `alphaTilde` rows of section 6.3

The `CWBlock` profile constructors and the pair-profile table; the fifteen integral rows on one
fine letter `(k_l, k_r)`, the explicit nine-pair sum showing each has the common mass `2 * 10 ^ 8`,
the entry identities tying two rows to `a` and `b`, and the swap symmetry `k_l <-> k_r`. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cwProfile
#assert_axioms AlgebraicComplexity.Examples.cwZeroProfile
#assert_axioms AlgebraicComplexity.Examples.cwBlock_univ
#assert_axioms AlgebraicComplexity.Examples.profileMass_cwProfile
#assert_axioms AlgebraicComplexity.Examples.cwPairProfile
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaTildeMass
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaTilde
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaTilde_sum
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaTilde_a_entries
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaTilde_b_entries
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaTilde_two_eq_nine
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaTilde_swap
