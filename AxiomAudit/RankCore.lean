/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.RankCore

/-!
# Axiom audit for the map and restriction tensor-rank core

The witness/minimum bridge is checked in `AxiomAudit/RankDefs.lean`.  This layer checks the
functorial rank laws introduced after leg maps and restrictions become available; product and
direct-sum laws remain covered by their downstream audits and clients.
-/

#assert_axioms AlgebraicComplexity.Tensor.RankLE.map
#assert_axioms AlgebraicComplexity.Tensor.rank_restricts_le
#assert_axioms AlgebraicComplexity.Tensor.rank_isomorphic
