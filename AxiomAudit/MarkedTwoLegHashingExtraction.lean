/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.MarkedTwoLegHashingExtraction

/-! Focused trust audit for the marked two-leg (asymmetric) hashing extraction of
[DuanWuZhou2022] §2.9: X/Y uniqueness against the whole ambient filter with the Z leg
deliberately shared, the abstract modulus form, the regression against the unmarked two-leg
theorem, and the tiny inhabited instance. -/

#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.exists_seed_many_markedXYIsolatedTargets
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.exists_seed_many_markedXYIsolatedTargets_of_modulus
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.eq_of_mem_markedXYIsolatedTargets_of_mem_filteredTargets
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.card_markedXYIsolatedTargets_le_card_marked
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.quarter_of_eight_mul_legFiber_le
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.xyCompetitorYIndices_subset_of_subset
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.exists_seed_many_xyIsolatedTargets_of_marked
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.tiny_markedXYIsolatedTargets_nonempty
#assert_axioms AlgebraicComplexity.ProgressionHash.LegalTriple.card_tinyMarked_lt_card_tinyAmbient
