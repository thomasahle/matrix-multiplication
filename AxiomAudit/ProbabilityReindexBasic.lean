/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Probability.ReindexBasic

/-!
# Axiom audit for basic probability reindexing

This focused audit checks entropy invariance and the interaction between source relabelling and
deterministic pushforward.
-/

#assert_axioms AlgebraicComplexity.ProbabilityVector.entropyBits_reindex
#assert_axioms AlgebraicComplexity.ProbabilityVector.pushforward_reindex
#assert_axioms AlgebraicComplexity.ProbabilityVector.entropyBits_pushforward_equiv
#assert_axioms AlgebraicComplexity.ProbabilityVector.reindex_symm_reindex
