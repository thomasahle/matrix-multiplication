/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompatibilityModel

set_option autoImplicit false

/-! # Axiom audit for the level-two legwise compatibility model

The model and its soundness; its strictness as a refinement; its maximality among sound models
and the resulting injectivity ceiling; and the ceiling instantiated at the joint six-orientation
hash, together with the constraint any copy count inherits from it. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63LabelCompat
#assert_axioms AlgebraicComplexity.Examples.dwz63LabelCompat_iff
#assert_axioms AlgebraicComplexity.Examples.dwz63LabelCompat_sound
#assert_axioms AlgebraicComplexity.Examples.dwz63LabelCompat_sound_forall
#assert_axioms AlgebraicComplexity.Examples.dwz63LabelCompat_not_two
#assert_axioms AlgebraicComplexity.Examples.not_forall_dwz63LabelCompat
#assert_axioms AlgebraicComplexity.Examples.sound_compatible_of_leg_eq
#assert_axioms AlgebraicComplexity.Examples.injOn_leg_of_compatibilityIsolated
#assert_axioms AlgebraicComplexity.Examples.card_compatibilityIsolatedSupport_le_card_image
#assert_axioms AlgebraicComplexity.Examples.card_dwz63JointIsolatedSupport_le_card_zWords
#assert_axioms AlgebraicComplexity.Examples.dwz63_copyCount_forces_card_zWords
#assert_axioms AlgebraicComplexity.Examples.card_image_x_dwz63JointRetainedSupport
#assert_axioms AlgebraicComplexity.Examples.dwz63_copyCount_forces_card_xWords
