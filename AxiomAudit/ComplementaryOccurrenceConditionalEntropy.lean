/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceConditionalEntropy

/-! Focused trust audit for the conditional entropy of labelled complementary occurrences. -/

#assert_axioms
  AlgebraicComplexity.WordType.conditionalProfileEntropyBase_proportionalCounts
#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.profileMass_complementaryOccurrenceCellProfile
#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.complementaryOccurrenceCellProfile_proportionalCounts
#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.multiplicity_append_cellOf_complement
#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.normalizedCellChildLaw_entropy
#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.profileMass_mul_reference_conditionalEntropy_coarse
#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.conditionalProfileEntropyBase_cellJointProfile
