/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.GroupTensorBarrier

set_option autoImplicit false

/-!
# Axiom audit for the Sawin obligation of the group-tensor barrier

Focused trust audit for the `Sawin` section of
`AlgebraicComplexity/Examples/GroupTensorBarrier.lean`, which follows Section 6 of J. Alman and
V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to Matrix
Multiplication*, arXiv:1810.08671v1.

The umbrella audit asserts every theorem that consumes `SawinBound`, so the proposition is
covered through its consumers' types.  It is asserted directly here as well, matching the
convention already used for the `Prop` obligation
`MatrixMultiplication.CurrentProofObligations.TotalWeightCertificateReconstruction` in
`AxiomAudit/CurrentProofObligations.lean`; the `README.md` named-obligation row lists it as a
declaration of record.
-/

namespace AlgebraicComplexity.Examples

#assert_axioms SawinBound

end AlgebraicComplexity.Examples
