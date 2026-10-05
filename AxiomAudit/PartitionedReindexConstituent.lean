/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.PartitionedReindexConstituent

set_option autoImplicit false

/-!
# Focused trust audit for constituents under reindexing

The audited theorem is the local algebraic reindexing step used by the new raw-cyclic Mode-B
specialization in the forthcoming legal-hybrid appendix of the Total-Weight manuscript
(`better_bound/paper.tex`).  It is not stated in [alman2025more]; the paper's partitioned-power
discussion at `papers/sources/2404.16349/overview.tex:18-40` is only the surrounding ingredient.
-/

open AlgebraicComplexity.Tensor

#assert_axioms PartitionedTensor.ReindexEquiv.constituent_isomorphic
