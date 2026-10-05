/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.SharedLegSeedHoleMass

set_option autoImplicit false

/-!
# Trust audit for arbitrary shared-leg seed/hole averaging

The finite theorem packages the affine collision and averaging steps used before the Y/Z
compatibility cleanup in Claim 6.18 of [alman2025more,
`papers/sources/2404.16349/constituent.tex:177-479`].
-/

open AlgebraicComplexity.ProgressionHash.LegalTriple

#assert_axioms seedSharedLegHoleMass
#assert_axioms sum_card_bucketWitnesses_mul_cube_of_sharedLeg
#assert_axioms sum_seedSharedLegHoleMass_mul_cube_le
#assert_axioms scaledHoleMass_averaging_arith
#assert_axioms exists_seed_isolation_and_sharedLegHoleMass
#assert_axioms markedXSeedSharedLegHoleMass
#assert_axioms exists_seed_many_markedXIsolatedTargets_and_sharedLegHoleMass
