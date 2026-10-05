/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.CurrentProofObligations

set_option autoImplicit false

/-!
# Axiom audit for the canonical Total-Weight obligation boundary

These checks cover the replacement-certificate arithmetic and the two direct extraction-sequence
endpoints.  Their recursive counting source is [alman2025more], Claim 6.18
(`papers/sources/2404.16349/constituent.tex:376-440`); the manuscript states the remaining counting
hypothesis at `better_bound/paper.tex:1729-1761` and the final rational inequality at
`better_bound/paper.tex:2195-2212`.  The legacy experimental adapters remain covered by the
umbrella audit, and since 2026-09-05 the six legacy obligation `Prop`s that `README.md`'s
named-obligation table lists are asserted directly here as well, in the same convention as
`TotalWeightCertificateReconstruction` above; they were previously covered only through the types
of their asserted consumers.
-/

namespace MatrixMultiplication.CurrentProofObligations

#assert_axioms totalWeightOmegaTarget
#assert_axioms totalWeightRetainedFloor
#assert_axioms totalWeightVolumeFloor
#assert_axioms totalWeightOmegaTarget_pos
#assert_axioms totalWeightVolumeFloor_pos
#assert_axioms certified_totalWeight_endpoint_slack
#assert_axioms TotalWeightCertificateReconstruction
#assert_axioms totalWeightCertificateReconstruction_of_floor_bounds
#assert_axioms omega_lt_2365815_of_subexponentialVolumeSequence
#assert_axioms omega_lt_2365815_of_wholeConstituentSequenceData

-- The legacy obligation `Prop`s of `README.md`'s named-obligation table.
#assert_axioms ConcreteGlobalConstituentTypeCounting
#assert_axioms CompatibilityZeroingAndHoleRepair
#assert_axioms CertifiedParentConsistencyInstantiation
#assert_axioms CertifiedTwoLetterInstantiation
#assert_axioms ExactLevelFourReconstruction
#assert_axioms VolumeOnlyLevelFourReconstruction
#assert_axioms ExactLevelFourReconstruction.toVolumeOnly

end MatrixMultiplication.CurrentProofObligations
