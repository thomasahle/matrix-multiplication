/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGoodBatchSizeGrowth

/-! Focused trust audit for the batching loss: the affine bound on four batches at the
predecessor length, and the subexponential growth statement the endpoints instantiate
`batchLoss` with. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_four_mul_goodBatchSize_pred_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_subexponential_four_mul_goodBatchSize_pred
