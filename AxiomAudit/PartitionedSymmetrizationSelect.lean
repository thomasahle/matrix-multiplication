/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrizationSelect

/-! # Axiom audit for `sym₃` of a block cut

The induced three-orientation keep predicate and its decidability, the structural identity that
`sym₃` of a cut certificate is a cut of the `sym₃` certificate, its realization form, and the
`Restricts`-valued packaging of selection monotonicity.

These formalize the commutation/restriction bridge `[duan2023faster]` needs at
`papers/sources/2210.10173/second_power_appendix.tex:37` (inside the proof of
`lem:non-rot-values` (d), `:26-45`, especially `:31-37`), where the paper cuts by the
marginals and only then forms `sym_3`; the general reason is `global_value.tex:98-121`,
Step 4 at `:104` and the implicit symmetrization at `:121`.  The Lean statements themselves
are general partitioned-tensor facts, not published claims. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.symThreeKeep
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.symThreeKeepDecidable
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.symThreePartition_select
#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.isomorphic_symThreePartition_select
#assert_axioms AlgebraicComplexity.Tensor.Restricts.select_of_imp
