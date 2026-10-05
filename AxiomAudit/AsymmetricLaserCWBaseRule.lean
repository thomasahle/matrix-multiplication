/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.AsymmetricLaserCWBaseRule
import AxiomAudit.Command

/-! Audit of finite native CW base-rule admission from [duan2023faster]. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.CWBaseRuleData
#assert_axioms AlgebraicComplexity.Examples.CWBaseRuleData.q
#assert_axioms AlgebraicComplexity.Examples.CWBaseRuleData.shape
#assert_axioms AlgebraicComplexity.Examples.cwBaseShapeDigits
#assert_axioms AlgebraicComplexity.Examples.decodeCWBaseShape
#assert_axioms AlgebraicComplexity.Examples.decodeCWBaseShape_sound
#assert_axioms AlgebraicComplexity.Examples.cwBaseRuleCheck
#assert_axioms AlgebraicComplexity.Examples.cwBaseRuleCheck_sound
