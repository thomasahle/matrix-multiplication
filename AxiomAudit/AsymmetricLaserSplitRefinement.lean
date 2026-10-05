/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserSplitRefinement
import AxiomAudit.Command

/-! Audit of finite refinement and native-letter admission for [duan2023faster]. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.AsymmetricLaserData.splitRequirementsFromProfiles_refinesType
#assert_axioms
  AlgebraicComplexity.AsymmetricLaserData.splitRequirementsFromProfiles_isUseful_mem_alphabet
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.orderedSplitAlphabet_degree_of_mem
