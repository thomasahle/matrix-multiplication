/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrizedHashing

set_option autoImplicit false

/-! # Axiom audit for one hashing seed on a product of permuted partitions

The mixed-radix `NatBlockEncoding` and its three constructors (leg permutation, external product,
cast into a field), the seeded marked two-leg extraction for a positive power, and the uniform
batching that supplies `[DuanWuZhou2022]` section 6's `batch`/`hbatch`. -/

#assert_axioms AlgebraicComplexity.leg_add_three_comp_equiv
#assert_axioms AlgebraicComplexity.NatBlockEncoding.copy
#assert_axioms AlgebraicComplexity.NatBlockEncoding.copy_code
#assert_axioms AlgebraicComplexity.NatBlockEncoding.copy_alphabet
#assert_axioms AlgebraicComplexity.NatBlockEncoding.copy_natTarget
#assert_axioms AlgebraicComplexity.NatBlockEncoding.permute
#assert_axioms AlgebraicComplexity.NatBlockEncoding.permute_alphabet
#assert_axioms AlgebraicComplexity.NatBlockEncoding.permute_natTarget
#assert_axioms AlgebraicComplexity.NatBlockEncoding.external
#assert_axioms AlgebraicComplexity.NatBlockEncoding.external_alphabet
#assert_axioms AlgebraicComplexity.NatBlockEncoding.external_natTarget
#assert_axioms AlgebraicComplexity.NatBlockEncoding.toPartitionHashEncoding
#assert_axioms AlgebraicComplexity.NatBlockEncoding.toPartitionHashEncoding_target
#assert_axioms AlgebraicComplexity.NatBlockEncoding.toPartitionHashEncoding_encode
#assert_axioms AlgebraicComplexity.uniformBatchIndex
#assert_axioms AlgebraicComplexity.uniformBatch
#assert_axioms AlgebraicComplexity.uniformBatch_val
#assert_axioms AlgebraicComplexity.uniformBatch_surjective
#assert_axioms AlgebraicComplexity.le_card_uniformBatch_fiber
#assert_axioms AlgebraicComplexity.PartitionHashEncoding.restricts_positivePower_to_markedXYIsolated
#assert_axioms
  AlgebraicComplexity.PartitionHashEncoding.markedXYIsolatedPowerAddresses_subset_positivePower_support
#assert_axioms AlgebraicComplexity.PartitionHashEncoding.x_injOn_markedXYIsolated_positivePower
#assert_axioms AlgebraicComplexity.PartitionHashEncoding.exists_seed_markedXYIsolated_positivePower
