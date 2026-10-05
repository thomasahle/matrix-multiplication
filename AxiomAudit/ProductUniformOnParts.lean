/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.ProductUniformOnParts

set_option autoImplicit false

/-! # Axiom audit for the m-fold product of shuffling families -/

#assert_axioms AlgebraicComplexity.HoleRepair.UniformOnParts.filter_piCongrRight_eq_piFinset
#assert_axioms AlgebraicComplexity.HoleRepair.UniformOnParts.pi
#assert_axioms AlgebraicComplexity.HoleRepair.UniformOnParts.pi_relabel
#assert_axioms AlgebraicComplexity.HoleRepair.UniformOnParts.congrEquiv
