/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteProduct

/-!
# Audit of DuanWuZhouLevelTwoFiniteProduct

Assertions for the ordered base-product step of [duan2023faster],
`prelim.tex:294-309` and `component_value.tex:205-225`. No full-parent extraction is asserted.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63Row022ProductData
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Product_checked
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Product_restricts
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022RotatedProductData
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022RotatedProduct_checked
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022RotatedProduct_restricts
