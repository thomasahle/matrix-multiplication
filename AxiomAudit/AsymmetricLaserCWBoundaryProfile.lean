/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.AsymmetricLaserCWBoundaryProfile

/-! # Axiom audit for finite native boundary-profile admission -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.CWBoundaryProfileData
#assert_axioms AlgebraicComplexity.Examples.CWBoundaryProfileData.mk
#assert_axioms AlgebraicComplexity.Examples.CWBoundaryProfileData.q
#assert_axioms AlgebraicComplexity.Examples.CWBoundaryProfileData.zeroLeg
#assert_axioms AlgebraicComplexity.Examples.CWBoundaryProfileData.zDegree
#assert_axioms AlgebraicComplexity.Examples.CWBoundaryProfileData.profile
#assert_axioms AlgebraicComplexity.Examples.decodeCWBoundaryProfile
#assert_axioms AlgebraicComplexity.Examples.cwBoundaryProfileCounts
#assert_axioms AlgebraicComplexity.Examples.cwBoundaryProfileCounts_mass
#assert_axioms AlgebraicComplexity.Examples.cwBoundaryProfileCounts_degree
#assert_axioms AlgebraicComplexity.Examples.decodeCWBoundaryProfile_sound
