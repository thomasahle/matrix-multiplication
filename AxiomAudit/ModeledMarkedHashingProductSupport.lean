/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.ModeledMarkedHashingProductSupport

set_option autoImplicit false

/-!
# Axiom audit for product-model support

The audited theorem identifies aggregate modeled targets with the factorwise Cartesian product
of modeled target families.
-/

open AlgebraicComplexity.ProgressionHash.LegalTriple.PartitionModel

#assert_axioms modeledTargets_aggregateModel
