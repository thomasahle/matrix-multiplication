/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradLevelTwoOrientedTypedLeaf

set_option autoImplicit false

/-!
# Axiom audit for oriented positive level-two CW typed leaves

This focused audit checks the exact dimension identification used by the recursive leaf semantics
of [dupont2026improving].
-/

#assert_axioms AlgebraicComplexity.Examples.cwLevelTwoRationalTypedLeaf_dimension
