/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.AsymmetricLaserLogWitness

/-!
# Audit of finite logarithm atoms

Checks the directed logarithm primitive for [duan2023faster], `global_value.tex:286-309`,
following the arithmetic construction in `better_bound/paper.tex:3537-3546`.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.AsymmetricLaserData.LogAtom
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.LogAtom.mk
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.LogAtom.argument
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.LogAtom.scale
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.LogAtom.terms
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.LogAtom.lower
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.LogAtom.upper
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.LogAtom.Valid
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.LogAtom.lower_le
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.LogAtom.le_upper
