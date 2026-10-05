/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.DyadicIntegralProfileEntropy

/-!
# Axiom audit for the integral-profile compatibility-rate bridge

These assertions cover the normalized one- and two-sided occurrence corollaries.  The elementary
dyadic/integral entropy conversions and the division-free compatibility-row identity have separate
lightweight audits.  In particular, the doubled-occurrence theorem accounts for the separately
labelled left and right occurrences even at self-complementary states.
-/

#assert_axioms
  AlgebraicComplexity.CompatibleSplit.SplitRequirements.canonicalCompatibilityRows_rate_normalized_of_equal_mass
#assert_axioms
  AlgebraicComplexity.CompatibleSplit.SplitRequirements.canonicalCompatibilityRows_rate_normalized_of_double_occurrence_mass
