/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.HashingSeedHoleMass

set_option autoImplicit false

/-! # Axiom audit for the seed-summed hole mass -/

#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.fineCompetitors
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.mem_fineCompetitors
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.seedSharedHoles
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.bucketWitnesses
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.seedHoleMass
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.card_seedSharedHoles_le
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.sum_card_bucketWitnesses_mul_cube
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.sum_seedHoleMass_mul_cube_le
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.holeMass_averaging_arith
