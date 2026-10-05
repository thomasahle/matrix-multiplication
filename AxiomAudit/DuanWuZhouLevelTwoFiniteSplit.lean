/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteSplit

/-!
# Audit of the finite profile compatibility adapter

[duan2023faster], `papers/sources/2210.10173/global_value.tex:35-51,332-378`.
Every declaration is checked against the standard axiom allow-list.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteCoarseLaw
#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteCoarseLaw_valid
#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteCoarseLaw_profile
#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteSplitPair
#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteSplitPair_splitCount
#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteSplitPair_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteSplitPair_letterPushforward
#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteSplitPair_matchableCompatible_subset
