/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.PartitionedPermutePower

/-! # Axiom audit for leg permutation across products and powers

Permuting a partitioned external product, moving a leg permutation across a positive partitioned
power, and transporting a block cut along a reindex equivalence.  These are the Lean-side
bookkeeping for the symmetrization/power reordering performed silently in `[duan2023faster]`,
`second_power_appendix.tex:26-45`. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.external_permute
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.reindexEquiv_permute_positivePower
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.ReindexEquiv.isomorphic_select
