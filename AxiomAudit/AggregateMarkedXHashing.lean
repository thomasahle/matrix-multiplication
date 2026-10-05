/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.AggregateMarkedXHashing

set_option autoImplicit false

/-!
# Trust audit for aggregate marked X-only hashing

The audited declarations are the finite one-leg hashing interface used before the compatibility
zero-outs in Claim 6.18 of [alman2025more].
-/

#assert_axioms
  AlgebraicComplexity.ProgressionHash.LegalTriple.card_aggregate_xCompetitorYIndices_le_product
#assert_axioms
  AlgebraicComplexity.ProgressionHash.LegalTriple.aggregateX_quarter_of_factorXFiberBounds
#assert_axioms
  AlgebraicComplexity.ProgressionHash.LegalTriple.exists_seed_many_aggregateMarkedXIsolatedTargets
