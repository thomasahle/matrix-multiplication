/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserSplitProfile

/-!
# Audit of the finite profile compatibility adapter

[duan2023faster], `papers/sources/2210.10173/global_value.tex:35-51,332-378`.
Every declaration is checked against the standard axiom allow-list.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.AsymmetricLaserData.splitRequirementsFromProfiles
#assert_axioms
  AlgebraicComplexity.AsymmetricLaserData.splitRequirementsFromProfiles_splitCount_of_period
