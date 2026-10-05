/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.PooledMarginalTypeConcentrationSource

/-! Focused trust audit for the native-source-length pooled concentration wrapper. -/

#assert_axioms AlgebraicComplexity.WordType.mem_pooledMarginalDeviatingWordsForSource
#assert_axioms AlgebraicComplexity.WordType.card_pooledMarginalDeviatingWordsForSource_le
