/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellRotatedCertificate

/-! # Axiom audit for the leg-indexed fine-cell coherent certificate

The fine-letter coherent base in all three zero orientations, the canonical shared map of a whole
cell word, and the address-indexed coherent certificate at the uniform dimension `q ^ k` that the
shared-fibre fusion consumes. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63FineZeroRotatedBase
#assert_axioms AlgebraicComplexity.Examples.dwz63FineCellRotatedCanonicalZMap
#assert_axioms AlgebraicComplexity.Examples.dwz63FineCellRotatedCoherent
