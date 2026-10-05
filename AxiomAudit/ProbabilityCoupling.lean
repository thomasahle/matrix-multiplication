/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Probability.Coupling

/-!
# Axiom audit for finite couplings

This focused audit checks exact marginal transport, independent-product marginals, sparse
entropy subadditivity, and the maximum-entropy property of the independent product.
-/

#assert_axioms AlgebraicComplexity.ProbabilityVector.IsCoupling.pushforward_prodMap
#assert_axioms AlgebraicComplexity.ProbabilityVector.product_isCoupling
#assert_axioms AlgebraicComplexity.ProbabilityVector.IsCoupling.entropy_le_add
#assert_axioms AlgebraicComplexity.ProbabilityVector.product_isMaximumEntropyCoupling
