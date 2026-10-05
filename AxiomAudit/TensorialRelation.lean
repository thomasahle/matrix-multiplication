/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Probability.TensorialRelation

set_option autoImplicit false

/-!
# Axiom audit for probability-vector tensorial-relation adapters

These assertions cover the three point-mass specializations which keep probability out of the
paper-independent tensorial-relation layer while preserving the repeated-orientation API.

The repeated-orientation client follows the region-relabeling framework of [alman2025more].
-/

#assert_axioms
  AlgebraicComplexity.TensorialRelation.arbitrary_labels_of_standard_weights
#assert_axioms
  AlgebraicComplexity.TensorialRelation.LabelledDecomposition.arbitrary_labels_of_standard_weights
#assert_axioms
  AlgebraicComplexity.TensorialRelation.StandardSlotLevel.ofStandardWeights
