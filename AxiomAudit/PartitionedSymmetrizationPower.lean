/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrizationPower

/-! # Axiom audit for `sym₃` of a positive partitioned power

The label transpose, the reindex equivalence identifying the three-orientation partition of a
positive power with the positive power of the three-orientation partition, and the cut form a
symmetrized laser client consumes.  Formalizes the reordering used in `[duan2023faster]`,
`second_power_appendix.tex:26-45` (`lem:non-rot-values` (d)). -/

set_option autoImplicit false

open AlgebraicComplexity.Tensor.PartitionedTensor

#assert_axioms symThreeWordEquiv
#assert_axioms reindexEquiv_symThreePartition_positivePower
#assert_axioms isomorphic_symThreePartition_positivePower_select
