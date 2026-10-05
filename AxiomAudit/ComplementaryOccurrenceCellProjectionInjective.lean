/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Probability.ComplementaryOccurrenceCellProjectionInjective

/-! Axiom audit for injective complementary-occurrence cell projections. -/

open AlgebraicComplexity AlgebraicComplexity.ComplementaryOccurrenceLaw

#assert_axioms cellJointProfile_apply_of_injective
#assert_axioms complementaryOccurrenceCellProfile_apply_of_injective
#assert_axioms normalizedCellChildLaw_apply_of_injective
#assert_axioms toCellProductProjectionModel_reference_eq_identity_of_injective
#assert_axioms toCellProductProjectionModel_parentLaw_eq_identity_of_injective
