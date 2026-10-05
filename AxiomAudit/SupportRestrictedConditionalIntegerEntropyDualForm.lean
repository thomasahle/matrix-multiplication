/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualForm
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for exact support-restricted conditional-dual forms

Audits the fixed-fiber integer-potential serialization of the Total-Weight manuscript's
`prop:dual`, `better_bound/paper.tex:2286-2307` (2026-09-06 draft). Its application is the
combination-loss program of [alman2025more],
`papers/sources/2404.16349/constituent.tex:113-147`.
-/

open MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualForm

#assert_axioms positiveLogTermForm
#assert_axioms positiveLogTermForm_eval
#assert_axioms sourceNumerators
#assert_axioms sourceEntropyForm
#assert_axioms sourceEntropyForm_eval
#assert_axioms stateWeightForm
#assert_axioms stateWeightForm_eval
#assert_axioms fixedCoordinateFiberNumerator
#assert_axioms fixedCoordinateFiberNumerator_eq
#assert_axioms fixedCoordinatePartitionForm
#assert_axioms fixedCoordinatePartitionForm_eval
#assert_axioms fixedCoordinateDualForm
#assert_axioms fixedCoordinateDualForm_eval
#assert_axioms retainedRowForm
#assert_axioms retainedRowForm_eval
