/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.RawCyclicRowExtraction

set_option autoImplicit false

/-!
# Axiom audit for one-hash raw cyclic-row extraction

These declarations formalize the new finite one-joint-hash raw-cyclic specialization for the
forthcoming legal-hybrid appendix of the Total-Weight manuscript (`better_bound/paper.tex`).  They
are not a theorem from [alman2025more]; its ordinary constituent hashing and cleanup at
`papers/sources/2404.16349/constituent.tex:376-440,483-497` provide ingredients only.
-/

open AlgebraicComplexity

#assert_axioms Tensor.PartitionedTensor.positiveWordEquiv_symThreeWordEquiv
#assert_axioms Tensor.PartitionedTensor.symThreeSupportEquiv
#assert_axioms Tensor.PartitionedTensor.symThreePositivePowerAddress
#assert_axioms Tensor.PartitionedTensor.isomorphic_symThreePositivePower_constituent_of_same_type
#assert_axioms PositiveIntegralProfile.mappedType_proportionalCounts_cyclicProduct_fst_fst
#assert_axioms PositiveIntegralProfile.mappedType_proportionalCounts_cyclicProduct_fst_snd
#assert_axioms PositiveIntegralProfile.mappedType_proportionalCounts_cyclicProduct_snd
#assert_axioms Tensor.PartitionedTensor.symThreeSupportProfile
#assert_axioms Tensor.PartitionedTensor.symThreePrimitiveWords
#assert_axioms Tensor.PartitionedTensor.multiplicity_symThreePrimitiveWords_fst_fst
#assert_axioms Tensor.PartitionedTensor.multiplicity_symThreePrimitiveWords_fst_snd
#assert_axioms Tensor.PartitionedTensor.multiplicity_symThreePrimitiveWords_snd
#assert_axioms Tensor.PartitionedTensor.positiveSupportWordBlockAddress_eq_symThreePrimitiveWords
#assert_axioms Tensor.PartitionedTensor.isomorphic_symThreePositivePower_constituent_of_reference_type
#assert_axioms Tensor.Restricts.rawCyclicRow_to_symThreeChildDirectSum
