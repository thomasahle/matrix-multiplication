/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CompatibilityTargetCore
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for the lightweight exact compatibility-target core

This companion checks every public declaration in the finite target core supporting
[alman2025more], Claim 6.18 (`papers/sources/2404.16349/constituent.tex:404-429`) -- the
hand-written ones and the `DecidableEq` instance that `CoarseIndex`'s `deriving` clause emits.
The instance is defined as its own auxiliary decision procedure
`instDecidableEqCoarseIndex.decEq`, so that constant's axiom cone is contained in the one checked
here.
-/

open AlgebraicComplexity.MoreAsymmetryCompatibility

#assert_axioms CoarseIndex
#assert_axioms instDecidableEqCoarseIndex
#assert_axioms CoarseIndex.ext
#assert_axioms CoarseIndex.get
#assert_axioms cellMultiplicity
#assert_axioms cellMultiplicity_pos_of_apply_eq
#assert_axioms coarseTotal
#assert_axioms CompatibilityTargets
#assert_axioms CompatibilityTargets.exactProfile
#assert_axioms CompatibilityTargets.exactProfile_X
#assert_axioms CompatibilityTargets.exactProfile_Y
#assert_axioms CompatibilityTargets.exactProfile_Z
#assert_axioms CompatibilityTargets.IsXWeightSupported
#assert_axioms CompatibilityTargets.IsYWeightSupported
#assert_axioms CompatibilityTargets.IsZWeightSupported
#assert_axioms CompatibilityTargets.IsWeightSupported
