/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.OrderingFreeAsymmetricHashing

set_option autoImplicit false

/-!
# Audit of ordering-free asymmetric hashing

The finite seed-summed union bound extends [duan2023faster], §2.9 and §6.3, without a comparison
of the numbers of X/Y and Z blocks. Every declaration of the source module is asserted here.
-/

open AlgebraicComplexity.ProgressionHash.LegalTriple

#assert_axioms seedSharedLegNonholeMass
#assert_axioms seedSharedLegNonholeMass_add_holeMass
#assert_axioms five_mul_le_eight_mul_sum_seedSharedLegNonholeMass
#assert_axioms seedMarkedXYNonholeFraction
#assert_axioms five_eighths_le_expected_seedMarkedXYNonholeFraction
#assert_axioms exists_seed_markedXYNonholeFraction
