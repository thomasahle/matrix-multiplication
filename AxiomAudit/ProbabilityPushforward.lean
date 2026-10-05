/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Probability.Pushforward

/-!
# Axiom audit for finite pushforward composition

This focused audit checks the lightweight functorial law used by probability reindexing and
finite coupling interfaces.
-/

#assert_axioms AlgebraicComplexity.ProbabilityVector.pushforward_comp
