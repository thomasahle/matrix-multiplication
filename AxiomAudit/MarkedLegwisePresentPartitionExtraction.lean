/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.MarkedLegwisePresentPartitionExtractionTiny
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for present marked all-leg extraction

This companion audits the finite present/missing split and direct-sum restriction formalizing
Corollary `cor:present-marked-all-leg-extraction` of the Total-Weight manuscript,
`better_bound/paper.tex`.  It also executes the strict-support client: the abstract isolated family
has one actually present and one genuinely missing target, and the former is extracted as a
nonempty indexed direct sum.
-/

namespace AlgebraicComplexity.PartitionHashEncoding

#assert_axioms
  presentMarkedLegwiseIsolatedPowerAddresses

#assert_axioms
  missingMarkedLegwiseIsolatedPowerAddresses

#assert_axioms
  card_missing_add_card_presentMarkedLegwiseIsolatedPowerAddresses

#assert_axioms
  presentMarkedLegwiseIsolatedPowerAddresses_hasUniqueLegFibers

#assert_axioms
  presentMarkedLegwiseIsolatedPowerAddresses_isLegwiseInjective

end AlgebraicComplexity.PartitionHashEncoding

namespace AlgebraicComplexity.Tensor.Restricts

#assert_axioms
  presentHashFiltered_to_presentMarkedLegwiseIsolatedIndexedDirectSum

#assert_axioms
  presentModeledTargets_to_presentMarkedLegwiseIsolatedIndexedDirectSum

end AlgebraicComplexity.Tensor.Restricts

namespace AlgebraicComplexity.Examples.MarkedLegwisePresentPartitionExtractionTiny

#assert_axioms
  strict_support_extraction_nonvacuous

end AlgebraicComplexity.Examples.MarkedLegwisePresentPartitionExtractionTiny
