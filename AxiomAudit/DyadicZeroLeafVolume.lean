/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.DyadicZeroLeafVolume

/-! # Axiom audit for dyadic zero-leaf volume semantics -/

namespace MatrixMultiplication.DyadicZeroLeafVolume

#assert_axioms value
#assert_axioms entropySum_eq_profileEntropyBits
#assert_axioms value_eq_profileEntropyBits_add
#assert_axioms profileEntropyBits_proportionalCounts
#assert_axioms statisticSum_proportionalCounts
#assert_axioms scaledProfileBits_eq_mass_mul_value

end MatrixMultiplication.DyadicZeroLeafVolume
