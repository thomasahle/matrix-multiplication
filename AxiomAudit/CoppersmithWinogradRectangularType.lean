/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradRectangularType

set_option autoImplicit false

/-!
# Axiom audit for the rectangular Huang--Pan leg-fiber comparison

Focused trust audit for `AlgebraicComplexity/Examples/CoppersmithWinogradRectangularType.lean`,
the type layer of the two-parameter Huang--Pan family run over the full Coppersmith--Winograd
tensor of [coppersmith1990matrix, Eq. (10)]; the family and its rectangular reading are X. Huang
and V. Y. Pan, *Fast rectangular matrix multiplication and applications*, J. Complexity **14**
(1998), 257--299, Sections 5 and 7.1.

The umbrella audit asserts the mirror comparison `cwRectLegTypedFiber_X_le_Y` and the two other
declarations of the `README.md` (7.2) row.  Asserted here is the remaining leg direction
`cwRectLegTypedFiber_Y_le_X` that the same row names.
-/

#assert_axioms AlgebraicComplexity.Examples.cwRectLegTypedFiber_Y_le_X
