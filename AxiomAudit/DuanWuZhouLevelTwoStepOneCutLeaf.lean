/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutLeaf

set_option autoImplicit false

/-! # Axiom audit for the broken standard-form leaf of the Step-1 cut

`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:86, 98-102`, and `hole_lemma.tex:159-168`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_segmentMultiplicity_frameTransport
#assert_axioms AlgebraicComplexity.Examples.dwz63CutReferenceHoles_image
#assert_axioms AlgebraicComplexity.Examples.dwz63_cutFiber_restricts_brokenReferenceLeaf
