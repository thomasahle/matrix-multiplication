/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceProjectionProfile

/-! Focused trust audit for normalizing exact complementary-occurrence profiles. -/

#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.isPooledMarginalProfile_of_mappedType_eq
