/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.RankDefs

/-!
# Axiom audit for the minimal tensor-rank definitions

These checks cover the finite list-to-`Fin` sum bridge, constructive witness predicate, existence
theorem, and minimum-rank bridge at the lowest dependency boundary.
-/

#assert_axioms AlgebraicComplexity.Tensor.list_map_sum_eq_fin_sum
#assert_axioms AlgebraicComplexity.Tensor.RankLE.pure_tensor
#assert_axioms AlgebraicComplexity.Tensor.RankLE.add
#assert_axioms AlgebraicComplexity.Tensor.exists_rankLE
#assert_axioms AlgebraicComplexity.Tensor.rank_spec
#assert_axioms AlgebraicComplexity.Tensor.rank_le_iff
