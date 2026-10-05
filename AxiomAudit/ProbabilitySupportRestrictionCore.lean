/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Probability.SupportRestrictionCore

/-!
# Axiom audit for positive-support restriction core

This focused audit checks that deleting common structural zeroes preserves total mass, entropy,
and finite KL divergence without importing derivative-based KL estimates.
-/

#assert_axioms AlgebraicComplexity.ProbabilityVector.sum_positiveSupport_eq
#assert_axioms AlgebraicComplexity.ProbabilityVector.restrictToPositiveSupport_entropy
#assert_axioms AlgebraicComplexity.ProbabilityVector.restrictToPositiveSupport_klDiv
