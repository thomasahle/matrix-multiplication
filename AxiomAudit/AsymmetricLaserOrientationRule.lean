/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserOrientationRule

/-!
# Audit of AsymmetricLaserOrientationRule

Assertions for the finite physical-leg step of [duan2023faster],
`component_value.tex:459-475`. No shared-map coherence or exponent is asserted.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.AsymmetricLaserData.physicalLegCode
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.physicalLegTable
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.decodePhysicalLegs
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.physicalLegMatrixDimensions
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.decodePhysicalLegs_sound
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.decodePhysicalLegs_isomorphic
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.decodePhysicalLegs_restricts
