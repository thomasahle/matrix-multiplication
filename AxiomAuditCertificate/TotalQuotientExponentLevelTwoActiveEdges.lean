/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdges

/-!
# Certificate axiom audit for the compact active-edge certificate

The address cache is an exact finite certificate.  These assertions cover its range split,
representative boundary shards, reassembly, and final equality with the computed lightweight edge
enumeration.
-/

#assert_axioms MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdges.range_split
#assert_axioms MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdges.shard0
#assert_axioms MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdges.shard7
#assert_axioms MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdges.cached_reassemble
#assert_axioms MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdges.activeEdges_eq
