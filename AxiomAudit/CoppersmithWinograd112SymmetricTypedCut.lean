/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricTypedCut

/-! # Axiom audit for the symmetric meeting point of the `112` typed cut

`sym₃` of the leaf's `alphatilde`-typed `112` cut restricts onto the committed symmetric ambient
power.  Formalizes `[duan2023faster]`, `second_power_appendix.tex:26-45`, proof of
`lem:non-rot-values` (d). -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cw112_symThree_typedCut_restricts_symmetricAmbient
