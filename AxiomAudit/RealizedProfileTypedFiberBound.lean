/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.RealizedProfileTypedFiberBound

set_option autoImplicit false

/-! # Axiom audit for counting an actual family through its realized profiles -/

#assert_axioms AlgebraicComplexity.WordType.realizedProfileTypedFiberEmbedding
#assert_axioms AlgebraicComplexity.WordType.card_le_sum_realizedProfileTypedFibers
