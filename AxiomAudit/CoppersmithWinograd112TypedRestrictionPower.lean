/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinograd112TypedRestrictionPower

/-! # Axiom audit for the `(1,1,2)` orbit region as a typed cut of the `112` partition

The inverse block dictionary and its two round-trips, the collapse of a constant segmentation to a
plain word type, the identification of the constant coarse target with the letterwise cell
condition, the support of a power of the cell, and the pushed-forward profile and typed cut. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cw112RawDictInv
#assert_axioms AlgebraicComplexity.Examples.cw112RawDict_dictInv
#assert_axioms AlgebraicComplexity.Examples.cw112RawDictInv_dict
#assert_axioms AlgebraicComplexity.Examples.cw112RawCellKeep_dictInv
#assert_axioms AlgebraicComplexity.Examples.dwz63_segmentMultiplicity_constSeg
#assert_axioms AlgebraicComplexity.Examples.dwz63_orbitTarget_iff_cellKeep
#assert_axioms AlgebraicComplexity.Examples.cw112RawCell
#assert_axioms AlgebraicComplexity.Examples.dwz63_mem_orbitCellPower_support_iff
#assert_axioms AlgebraicComplexity.Examples.cw112PushedOrbitProfile
#assert_axioms AlgebraicComplexity.Examples.cw112TypedCut
#assert_axioms AlgebraicComplexity.Examples.cw112TypedCutKeepDecidable
