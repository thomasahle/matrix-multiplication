/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteBaseRule

/-!
# Audit of the literal DWZ paired-011 base-rule consumer

These assertions cover finite lookup, admission and the native two-factor restriction for
[duan2023faster], `second_power.tex:51-63`. No full 022 extraction or exponent is asserted.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63Row022BaseRuleData
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022MiddleBaseRules_checked
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022MiddleBaseRules_restricts
