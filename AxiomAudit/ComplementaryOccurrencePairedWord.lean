/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.ComplementaryOccurrencePairedWord

/-! Focused trust audit for the paired-word complementary-occurrence bridge. -/

#assert_axioms AlgebraicComplexity.WordType.multiplicity_comp_perm_apply

#assert_axioms AlgebraicComplexity.WordType.multiplicity_append_complement_apply

#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.mappedType_fst_multiplicity_parentPairWord

#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.pooledMappedType_multiplicity_parentPairWord

#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.isPooledMarginalProfile_of_pairWords
