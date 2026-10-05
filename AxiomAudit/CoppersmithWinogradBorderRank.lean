/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd
import AlgebraicComplexity.Examples.CoppersmithWinogradPartition
import AxiomAudit.Command

/-!
# Axiom audit for the Coppersmith--Winograd border-rank certificate

Focused trust audit for the classical constructive bound `borderRank(CW_q) <= q + 2` proved in
`AlgebraicComplexity.Examples.CoppersmithWinograd`, together with the three restatements it
supports on the typed partitioned realization in
`AlgebraicComplexity.Examples.CoppersmithWinogradPartition`: equality of the two border ranks
under the partition isomorphism, the inherited numeric bound, and its logarithmic form.  These
are the tensor-source budget every laser endpoint over a power of `CW_q` ultimately spends, so
their axiom cone is asserted here rather than being inherited from a client's audit.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.coppersmithWinograd_borderRankLE
#assert_axioms AlgebraicComplexity.Examples.cwPartitionedTensor_borderRank
#assert_axioms AlgebraicComplexity.Examples.cwPartitionedTensor_borderRank_le
#assert_axioms AlgebraicComplexity.Examples.log_cwPartitionedTensor_borderRank_le
