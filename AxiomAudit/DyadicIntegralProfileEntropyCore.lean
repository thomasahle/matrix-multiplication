/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.DyadicIntegralProfileEntropyCore

/-!
# Axiom audit for dyadic integral-profile entropy conversion
-/

#assert_axioms
  MatrixMultiplication.DyadicIntegralProfileEntropy.weightedEntropy_eq_mass_mul_profileEntropyBits
#assert_axioms
  MatrixMultiplication.DyadicIntegralProfileEntropy.weightedEntropy_eq_profileEntropyMass_div
#assert_axioms
  MatrixMultiplication.DyadicIntegralProfileEntropy.weightedEntropyList_numeratorList
