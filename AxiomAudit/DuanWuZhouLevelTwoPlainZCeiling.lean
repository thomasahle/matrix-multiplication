/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainZCeiling

/-! # Axiom audit for the plain-partition `Z`-side isolation ceiling -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63PlainJointYIsolatedSupport
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainJointIsolatedSupport
#assert_axioms AlgebraicComplexity.Examples.card_dwz63PlainJointIsolatedSupport_le_card_zWords
#assert_axioms AlgebraicComplexity.Examples.dwz63_plainCopyCount_forces_card_zWords
