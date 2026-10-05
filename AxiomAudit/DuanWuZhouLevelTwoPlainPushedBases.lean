/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainPushedBases

set_option autoImplicit false

/-! # Axiom audit for the plain pushed entropy bases and `hupper` -/

#assert_axioms AlgebraicComplexity.Examples.dwz63PlainRateAlpha
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainRateAlpha_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63_exp_natCast_mul
#assert_axioms AlgebraicComplexity.Examples.dwz63_plainAlpha_profileMass_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63_pushedTypeFiberEntropyBase_pow
#assert_axioms AlgebraicComplexity.Examples.dwz63_pushedTypeFiberEntropyBase_X_pow
#assert_axioms AlgebraicComplexity.Examples.dwz63_pushedTypeFiberEntropyBase_Z_pow
#assert_axioms AlgebraicComplexity.Examples.dwz63_mappedType_plainLegRead_Z
#assert_axioms AlgebraicComplexity.Examples.dwz63_card_typedWordMapFiber_Z_le
