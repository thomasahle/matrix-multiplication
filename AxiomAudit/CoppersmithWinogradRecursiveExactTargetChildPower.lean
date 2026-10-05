/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveExactTargetChildPower
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Audit of selected parent-to-child tensor transport

Checks the labelled-child splitting step of Total-Weight's `hyp:intact-box`,
`better_bound/paper.tex:1219–1229`. Child-product terminology follows [alman2025more],
`papers/sources/2404.16349/constituent.tex:488–495`. This asserts no regrouping, hole bound or
certificate-specific extraction rate.
-/

#assert_axioms AlgebraicComplexity.Examples.cwChildPowerSplitSequence
#assert_axioms AlgebraicComplexity.Examples.cwChildPowerSplitSequence_parentChildEquiv
#assert_axioms AlgebraicComplexity.Examples.cwRecursiveExactChildParts
#assert_axioms AlgebraicComplexity.Examples.mem_cwRecursiveExactChildParts_iff
#assert_axioms AlgebraicComplexity.Examples.mem_cwRecursiveExactChildParts_iff_parent
#assert_axioms AlgebraicComplexity.Examples.cwRecursiveExactTargetBox_isomorphic_childPowerBox
#assert_axioms AlgebraicComplexity.Examples.cwRecursiveCompactExactTarget_restricts_childPowerBox
