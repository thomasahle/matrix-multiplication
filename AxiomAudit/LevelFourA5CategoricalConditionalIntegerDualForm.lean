/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.LevelFourA5CategoricalConditionalIntegerDualForm
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for the exact level-four A5 categorical dual form

Audits the integer-potential serialization of the Total-Weight manuscript's `prop:dual`,
`better_bound/paper.tex:2286-2307` (2026-09-06 draft), used with the combination-loss program
of [alman2025more], `papers/sources/2404.16349/constituent.tex:113-147`.
-/

open MatrixMultiplication.LevelFourA5CategoricalConditionalIntegerDualForm

#assert_axioms mappedType_fst_fixedCoordinateGraphProfile
#assert_axioms graphParent_weight
#assert_axioms stateLaw_weight
#assert_axioms categoricalDualBits_eq_countExpression
#assert_axioms mass_mul_log2Nat_eq_normalized
#assert_axioms categoricalDualForm
#assert_axioms categoricalDualForm_eval
#assert_axioms sourceEntropyForm_eval_eq_mass_mul_profileEntropyBits
#assert_axioms categoricalRetainedForm
#assert_axioms categoricalRetainedForm_eval
#assert_axioms categoricalRetainedForm32_eval
#assert_axioms categoricalRetainedForm_eval_le_of_feasibleRows
