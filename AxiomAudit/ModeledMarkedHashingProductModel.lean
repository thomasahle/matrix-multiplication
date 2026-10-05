/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.ModeledMarkedHashingProductModel

set_option autoImplicit false

/-!
# Axiom audit for products of native marked-hashing models

This companion checks the restriction to one aggregate factor and the two product-model
constructors used by heterogeneous marked hashing.
-/

open AlgebraicComplexity.ProgressionHash.LegalTriple.PartitionModel

#assert_axioms aggregateFactor
#assert_axioms aggregateFactor_aggregate
#assert_axioms aggregateModel
#assert_axioms aggregateModelReindex
