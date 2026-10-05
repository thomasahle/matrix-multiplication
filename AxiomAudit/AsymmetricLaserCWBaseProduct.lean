/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.AsymmetricLaserCWBaseProduct

/-!
# Audit of AsymmetricLaserCWBaseProduct

Assertions for the ordered base-product step of [duan2023faster],
`prelim.tex:294-309` and `component_value.tex:205-225`. No full-parent extraction is asserted.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.CWBaseProductData
#assert_axioms AlgebraicComplexity.Examples.decodeCWBaseChild
#assert_axioms AlgebraicComplexity.Examples.cwBaseChildDimensions
#assert_axioms AlgebraicComplexity.Examples.cwBaseProductDimensions
#assert_axioms AlgebraicComplexity.Examples.cwBaseProductCheck
#assert_axioms AlgebraicComplexity.Examples.decodeCWBaseChild_sound
#assert_axioms AlgebraicComplexity.Examples.cwBaseProductCheck_sound
