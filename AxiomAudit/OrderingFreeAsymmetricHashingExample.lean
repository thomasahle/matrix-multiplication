/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.OrderingFreeAsymmetricHashingExample
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Audit of the ordering-free finite hashing example

Every public declaration of the finite [duan2023faster] hashing client is covered. Private
address checks and instances are included transitively in the assertions of their consumers.
-/

open AlgebraicComplexity.OrderingFreeAsymmetricHashingExample

#assert_axioms unitWord
#assert_axioms edge
#assert_axioms ambient
#assert_axioms buckets
#assert_axioms useful
#assert_axioms compatibility
#assert_axioms card_ambient
#assert_axioms usedVertexCounts
#assert_axioms fullAmbient
#assert_axioms legFiber_card
#assert_axioms fineCompetitors_card
#assert_axioms expected_nonhole_positive
#assert_axioms exists_positive_seed
#assert_axioms positiveSeed
#assert_axioms damageSeed
#assert_axioms positiveSeed_nonhole
#assert_axioms damageSeed_sharedZ

#print axioms expected_nonhole_positive
#print axioms exists_positive_seed
#print axioms damageSeed_sharedZ
