/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.Generated.SimplifiedCW112Leaves

/-!
# Audit of the selected-certificate CW 112 leaf bridge

This focused companion asserts the public declarations interpreting the stored positive
12-bit mu parameters as typed CW 112 leaves. It covers the proof-body repair in
`selected_mu_bounds` without importing the full opt-in certificate census.
-/

set_option autoImplicit false

#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.halfDenominator
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.leafG
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.leafG_pos
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.cw112Mu_numerator_leafG_eq_mass
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.middleMass_eq
#assert_axioms
  MatrixMultiplication.Generated.SimplifiedCW112Leaves.cw112MuEntropyBits_numerator_leafG_eq
#assert_axioms
  MatrixMultiplication.Generated.SimplifiedCW112Leaves.orientedRetainedRateBits_eq_evaluator
#assert_axioms
  MatrixMultiplication.Generated.SimplifiedCW112Leaves.sum_dimensionRateBits_eq_evaluator
#assert_axioms
  MatrixMultiplication.Generated.SimplifiedCW112Leaves.weighted_sum_dimensionRateBits_eq_evaluator
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.InstantiatesCW112TypedLeaf
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.instantiates_cw112_of_bounds
#assert_axioms
  MatrixMultiplication.Generated.SimplifiedCW112Leaves.storedMuIndices_are_positiveSlots
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.selected_mu_positiveSlot
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.selected_mu_bounds
#assert_axioms
  MatrixMultiplication.Generated.SimplifiedCW112Leaves.selectedLevelTwoEntry_instantiates_cw112
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.inputHeavy
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.InstantiatesCW112EdgeInput
#assert_axioms
  MatrixMultiplication.Generated.SimplifiedCW112Leaves.edgeInput_instantiates_cw112_of_bounds
