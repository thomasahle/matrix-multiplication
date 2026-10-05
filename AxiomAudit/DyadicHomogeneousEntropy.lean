/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.DyadicHomogeneousEntropy

/-! Focused trust audit for the lightweight dyadic-to-homogeneous entropy bridge. -/

#assert_axioms MatrixMultiplication.DyadicHomogeneousEntropy.totalMass_dyadic
#assert_axioms
  MatrixMultiplication.DyadicHomogeneousEntropy.weightedEntropy_dyadic_eq_homogeneousEntropyBits
