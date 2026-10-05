/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.ModeledMarkedHashingModel

set_option autoImplicit false

/-!
# Axiom audit for native marked-hashing partition models

This companion checks every hand-written public declaration in the lightweight native partition
model.  The product-model operations are checked separately by
`AxiomAudit.ModeledMarkedHashingProductModel`.
-/

open AlgebraicComplexity.ProgressionHash.LegalTriple

#assert_axioms PartitionModel
#assert_axioms PartitionModel.encode
#assert_axioms PartitionModel.address
#assert_axioms PartitionModel.encode_address
#assert_axioms PartitionModel.reindex
#assert_axioms PartitionModel.onSubset
#assert_axioms PartitionModel.castDomain
#assert_axioms PartitionModel.address_injectiveOn
#assert_axioms PartitionModel.modeledTargets
#assert_axioms PartitionModel.card_modeledTargets
#assert_axioms PartitionModel.modeledMarkedLegwiseIsolatedAddresses
#assert_axioms PartitionModel.card_modeledMarkedLegwiseIsolatedAddresses
#assert_axioms PartitionModel.modeledFilteredAddresses
#assert_axioms PartitionModel.modeledMarked_subset_modeledFiltered
#assert_axioms PartitionModel.hashKeepBlock
#assert_axioms PartitionModel.hashKeepBlock_address_iff
#assert_axioms PartitionModel.filter_modeledTargets_hashKeepBlock_eq
