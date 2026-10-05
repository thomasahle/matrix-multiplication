import AlgebraicComplexity.Tensor.ProductCore
import AxiomAudit.Command

/-!
# Axiom audit for the lightweight external-product core

Checks the definition's elementary pure and finite-sum laws.
-/

open AlgebraicComplexity.Tensor

#assert_axioms external_pure
#assert_axioms external_sum_sum
