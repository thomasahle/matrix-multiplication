/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedBoxEmbedding
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for compact-box ambient inclusion

Checks the representation step for the Total-Weight manuscript, `better_bound/paper.tex`,
`hyp:intact-box` (lines 1219–1229). The child-product terminology is from [alman2025more],
`papers/sources/2404.16349/constituent.tex:488–495`.
This audit does not assert the remaining child-product factorization.
-/

#assert_axioms AlgebraicComplexity.Tensor.Restricts.compactBox_to_box
