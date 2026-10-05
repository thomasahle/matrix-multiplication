/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.HashingConditionalIndependence

/-! Focused trust audit for [DuanWuZhou2022] `lemma:hash_independence`: the reduction of a
colliding pair of legal triples to one further collision, the exact `M⁻³` fiber count, and the
`M⁻¹` conditional mass, including the paper's literal shared-Z form. -/

#assert_axioms AlgebraicComplexity.ProgressionHash.Seed.yHash_eq_of_xHash_eq_of_zHash_eq
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.xIndex_ne_and_yIndex_ne_of_zIndex_eq
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.inCommonTriple_pair_iff_collisionProxy
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.card_inCommonTriple_pair_mul_cube
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.uniformSeed_inCommonTriple_pair_mass
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.card_inCommonTriple_sharedZ_mul_cube
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.uniformSeed_inCommonTriple_sharedZ_mass
