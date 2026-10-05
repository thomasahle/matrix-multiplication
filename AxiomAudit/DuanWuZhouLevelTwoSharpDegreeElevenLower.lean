/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSharpDegreeElevenLower

set_option autoImplicit false

/-! # Axiom audit for the eventual eleven-lower bound on the sharp degree

`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:132-133, 137`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_cofinal_eleven_le_plainSharpDegree
